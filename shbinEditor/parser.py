from __future__ import annotations

import csv
import json
import math
import os
import re
import shutil
import struct
import tkinter as tk
from dataclasses import dataclass, field
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .constants import *
from .utils import *
from .pica import *
from .assembler import *

@dataclass
class ParseIssue:
    level: str
    message: str

@dataclass
class ShaderInstruction:
    index: int
    offset: int
    word: int
    raw_opcode: int
    opcode: int
    mnemonic: str
    fmt: str
    disasm: str
    fields: Dict[str, Any] = field(default_factory=dict)

    @property
    def display_name(self) -> str:
        return f"{self.index:04d}: {self.disasm}"

@dataclass
class DVLPInfo:
    offset: int
    size: int = 0
    version: int = 0
    unknown: int = 0
    opcode_offset: int = 0
    opcode_count: int = 0
    opdesc_offset: int = 0
    opdesc_count: int = 0
    line_offset: int = 0
    line_count: int = 0
    filename_symbol_offset: int = 0
    filename_symbol_size: int = 0
    opcodes: List[int] = field(default_factory=list)
    opdescs: List[Tuple[int, int]] = field(default_factory=list)
    instructions: List[ShaderInstruction] = field(default_factory=list)
    lines: List[Tuple[int, int, str]] = field(default_factory=list)
    filenames: List[Tuple[int, str]] = field(default_factory=list)

@dataclass
class ShaderConstant:
    dvle_index: int
    index: int
    offset: int
    entry_type: int
    register_id: int
    length_hint: int
    raw: List[int]
    name: str = ""
    register_name: str = ""
    mapped_input: str = ""

    @property
    def type_name(self) -> str:
        return CONSTANT_TYPE_NAMES.get(self.entry_type, f"Unknown({self.entry_type})")

    @property
    def values_for_display(self) -> List[Any]:
        if self.entry_type == 2:
            return [pica24_to_float(v) for v in self.raw]
        if self.entry_type == 0:
            return [bool(self.raw[0])]
        return list(self.raw)

    @property
    def display_name(self) -> str:
        if self.name:
            return self.name
        if self.register_name:
            return self.register_name
        return f"unknown_{self.type_name.lower()}_{self.register_id:02X}"

@dataclass
class ShaderInput:
    index: int
    offset: int
    name_offset: int
    start: int
    end: int
    name: str

@dataclass
class ShaderOutput:
    index: int
    offset: int
    output_type: int
    register_id: int
    mask: int
    unknown: int

@dataclass
class ShaderLabel:
    index: int
    offset: int
    label_id: int
    unknown_a: bytes
    opcode_address: int
    unknown_b: int
    name_offset: int
    name: str

@dataclass
class DVLEInfo:
    index: int
    offset: int
    size: int = 0
    version: int = 0
    shader_type: int = 0
    opcode_entry: int = 0
    opcode_end: int = 0
    unknown_10: int = 0
    unknown_14: int = 0
    const_offset: int = 0
    const_count: int = 0
    label_offset: int = 0
    label_count: int = 0
    output_offset: int = 0
    output_count: int = 0
    input_offset: int = 0
    input_count: int = 0
    symbol_offset: int = 0
    symbol_size: int = 0
    constants: List[ShaderConstant] = field(default_factory=list)
    labels: List[ShaderLabel] = field(default_factory=list)
    outputs: List[ShaderOutput] = field(default_factory=list)
    inputs: List[ShaderInput] = field(default_factory=list)
    symbols: List[Tuple[int, str]] = field(default_factory=list)

    @property
    def shader_type_name(self) -> str:
        if self.shader_type == 0:
            return "Vertex"
        if self.shader_type == 1:
            return "Geometry"
        return f"Unknown({self.shader_type})"

class BinaryReader:
    def __init__(self, data: bytearray, issues: List[ParseIssue]):
        self.data = data
        self.issues = issues

    def require(self, offset: int, size: int, context: str) -> bool:
        if offset < 0 or size < 0 or offset + size > len(self.data):
            self.issues.append(ParseIssue("error", f"{context}: range 0x{offset:X}..0x{offset + size:X} is outside file size 0x{len(self.data):X}"))
            return False
        return True

    def bytes(self, offset: int, size: int, context: str = "read") -> bytes:
        if not self.require(offset, size, context):
            return b"\x00" * max(0, size)
        return bytes(self.data[offset:offset + size])

    def u8(self, offset: int, context: str = "u8") -> int:
        if not self.require(offset, 1, context):
            return 0
        return self.data[offset]

    def u16(self, offset: int, context: str = "u16") -> int:
        if not self.require(offset, 2, context):
            return 0
        return struct.unpack_from("<H", self.data, offset)[0]

    def u32(self, offset: int, context: str = "u32") -> int:
        if not self.require(offset, 4, context):
            return 0
        return struct.unpack_from("<I", self.data, offset)[0]

    def cstring(self, offset: int, max_end: Optional[int] = None) -> str:
        if offset < 0 or offset >= len(self.data):
            return ""
        max_end = min(max_end if max_end is not None else len(self.data), len(self.data))
        pos = offset
        out = bytearray()
        while pos < max_end and self.data[pos] != 0:
            out.append(self.data[pos])
            pos += 1
        return out.decode("ascii", errors="replace")

    def iter_cstrings(self, start: int, size: int) -> List[Tuple[int, str]]:
        result: List[Tuple[int, str]] = []
        if size <= 0 or not self.require(start, size, "symbol table"):
            return result
        end = start + size
        pos = start
        while pos < end:
            while pos < end and self.data[pos] == 0:
                pos += 1
            if pos >= end:
                break
            rel = pos - start
            name = self.cstring(pos, end)
            result.append((rel, name))
            pos += len(name.encode("ascii", errors="replace")) + 1
        return result

class SHBINParser:
    def __init__(self) -> None:
        self.data = bytearray()
        self.filename = ""
        self.file_size = 0
        self.dvle_offsets: List[int] = []
        self.dvlp: Optional[DVLPInfo] = None
        self.dvles: List[DVLEInfo] = []
        self.issues: List[ParseIssue] = []
        self._reader: Optional[BinaryReader] = None
        self.register_symbol_maps: Dict[str, Dict[str, str]] = {"global": dict(DEFAULT_REGISTER_SYMBOLS)}

    @property
    def loaded(self) -> bool:
        return bool(self.data)

    def load(self, filename: str) -> None:
        self.filename = filename
        with open(filename, "rb") as f:
            self.data = bytearray(f.read())
        self.parse()

    def parse(self) -> None:
        self.file_size = len(self.data)
        self.dvle_offsets.clear()
        self.dvles.clear()
        self.dvlp = None
        self.issues.clear()
        self._reader = BinaryReader(self.data, self.issues)
        r = self._reader

        if len(self.data) < 8:
            raise ValueError("File is too small to be a DVLB/SHBIN file")

        magic = r.bytes(0, 4, "DVLB magic").decode("ascii", errors="ignore")
        if magic != "DVLB":
            raise ValueError("Not a valid DVLB .shbin file: missing DVLB magic at 0x0")

        dvle_count = r.u32(4, "DVLE count")
        if dvle_count > 256:
            self.issues.append(ParseIssue("warning", f"Suspicious DVLE count: {dvle_count}"))

        table_size = 8 + dvle_count * 4
        if not r.require(8, dvle_count * 4, "DVLE offset table"):
            return

        for i in range(dvle_count):
            off = r.u32(8 + i * 4, f"DVLE[{i}] offset")
            self.dvle_offsets.append(off)

        self._parse_dvlp(table_size)
        for i, off in enumerate(self.dvle_offsets):
            self.dvles.append(self._parse_dvle(off, i))

        self._annotate_instruction_metadata()
        self._estimate_block_sizes()

    def _parse_dvlp(self, offset: int) -> None:
        r = self._reader
        assert r is not None
        if not r.require(offset, 0x28, "DVLP header"):
            return
        magic = r.bytes(offset, 4, "DVLP magic").decode("ascii", errors="ignore")
        if magic != "DVLP":
            self.issues.append(ParseIssue("error", f"Expected DVLP at 0x{offset:X}, found {magic!r}"))
            return

        dvlp = DVLPInfo(
            offset=offset,
            version=r.u16(offset + 0x04, "DVLP version"),
            unknown=r.u16(offset + 0x06, "DVLP unknown"),
            opcode_offset=r.u32(offset + 0x08, "DVLP opcode table offset"),
            opcode_count=r.u32(offset + 0x0C, "DVLP opcode table count"),
            opdesc_offset=r.u32(offset + 0x10, "DVLP opdesc table offset"),
            opdesc_count=r.u32(offset + 0x14, "DVLP opdesc table count"),
            line_offset=r.u32(offset + 0x18, "DVLP line table offset"),
            line_count=r.u32(offset + 0x1C, "DVLP line table count"),
            filename_symbol_offset=r.u32(offset + 0x20, "DVLP filename symbols offset"),
            filename_symbol_size=r.u32(offset + 0x24, "DVLP filename symbols size"),
        )

        opcode_abs = offset + dvlp.opcode_offset
        if dvlp.opcode_count and r.require(opcode_abs, dvlp.opcode_count * 4, "DVLP opcode table"):
            dvlp.opcodes = [r.u32(opcode_abs + i * 4, f"opcode[{i}]") for i in range(dvlp.opcode_count)]

        opdesc_abs = offset + dvlp.opdesc_offset
        if dvlp.opdesc_count and r.require(opdesc_abs, dvlp.opdesc_count * 8, "DVLP opdesc table"):
            dvlp.opdescs = [
                (
                    r.u32(opdesc_abs + i * 8, f"opdesc[{i}].desc"),
                    r.u32(opdesc_abs + i * 8 + 4, f"opdesc[{i}].flags"),
                )
                for i in range(dvlp.opdesc_count)
            ]

        opcode_base = offset + dvlp.opcode_offset
        dvlp.instructions = []
        for i, word in enumerate(dvlp.opcodes):
            fields = pica_decode_instruction_fields(i, word, dvlp.opdescs)
            dvlp.instructions.append(ShaderInstruction(
                index=i,
                offset=opcode_base + i * 4,
                word=word,
                raw_opcode=fields.get("raw_opcode", get_bits(word, 26, 6)),
                opcode=fields.get("opcode", pica_effective_opcode(word)),
                mnemonic=fields.get("mnemonic", pica_opcode_name(word)),
                fmt=fields.get("format", "unknown"),
                disasm=fields.get("disasm", f".word 0x{word:08X}"),
                fields=fields,
            ))

        symbol_abs = offset + dvlp.filename_symbol_offset
        symbol_end = symbol_abs + dvlp.filename_symbol_size
        if dvlp.filename_symbol_size:
            dvlp.filenames = r.iter_cstrings(symbol_abs, dvlp.filename_symbol_size)

        line_abs = offset + dvlp.line_offset
        if dvlp.line_count and r.require(line_abs, dvlp.line_count * 8, "DVLP line table"):
            for i in range(dvlp.line_count):
                filename_off = r.u32(line_abs + i * 8, f"line[{i}].filename_offset")
                line_num = r.u32(line_abs + i * 8 + 4, f"line[{i}].line")
                filename = r.cstring(symbol_abs + filename_off, symbol_end) if dvlp.filename_symbol_size else ""
                dvlp.lines.append((filename_off, line_num, filename))

        self.dvlp = dvlp

    def _parse_dvle(self, offset: int, index: int) -> DVLEInfo:
        r = self._reader
        assert r is not None
        if not r.require(offset, 0x40, f"DVLE[{index}] header"):
            return DVLEInfo(index=index, offset=offset)

        magic = r.bytes(offset, 4, f"DVLE[{index}] magic").decode("ascii", errors="ignore")
        if magic != "DVLE":
            self.issues.append(ParseIssue("error", f"Expected DVLE[{index}] at 0x{offset:X}, found {magic!r}"))

        dvle = DVLEInfo(
            index=index,
            offset=offset,
            version=r.u16(offset + 0x04, f"DVLE[{index}] version"),
            shader_type=r.u8(offset + 0x06, f"DVLE[{index}] shader type"),
            opcode_entry=r.u32(offset + 0x08, f"DVLE[{index}] opcode entry"),
            opcode_end=r.u32(offset + 0x0C, f"DVLE[{index}] opcode end"),
            unknown_10=r.u32(offset + 0x10, f"DVLE[{index}] unknown 0x10"),
            unknown_14=r.u32(offset + 0x14, f"DVLE[{index}] unknown 0x14"),
            const_offset=r.u32(offset + 0x18, f"DVLE[{index}] const offset"),
            const_count=r.u32(offset + 0x1C, f"DVLE[{index}] const count"),
            label_offset=r.u32(offset + 0x20, f"DVLE[{index}] label offset"),
            label_count=r.u32(offset + 0x24, f"DVLE[{index}] label count"),
            output_offset=r.u32(offset + 0x28, f"DVLE[{index}] output offset"),
            output_count=r.u32(offset + 0x2C, f"DVLE[{index}] output count"),
            input_offset=r.u32(offset + 0x30, f"DVLE[{index}] input offset"),
            input_count=r.u32(offset + 0x34, f"DVLE[{index}] input count"),
            symbol_offset=r.u32(offset + 0x38, f"DVLE[{index}] symbol offset"),
            symbol_size=r.u32(offset + 0x3C, f"DVLE[{index}] symbol size"),
        )

        symbol_abs = offset + dvle.symbol_offset
        symbol_end = symbol_abs + dvle.symbol_size
        if dvle.symbol_size:
            dvle.symbols = r.iter_cstrings(symbol_abs, dvle.symbol_size)

        self._parse_inputs(dvle, symbol_abs, symbol_end)
        self._parse_outputs(dvle)
        self._parse_labels(dvle, symbol_abs, symbol_end)
        self._parse_constants(dvle)
        self._map_constant_names(dvle)
        return dvle

    def _parse_inputs(self, dvle: DVLEInfo, symbol_abs: int, symbol_end: int) -> None:
        r = self._reader
        assert r is not None
        abs_off = dvle.offset + dvle.input_offset
        if not dvle.input_count:
            return
        if not r.require(abs_off, dvle.input_count * 8, f"DVLE[{dvle.index}] input table"):
            return
        for i in range(dvle.input_count):
            entry_off = abs_off + i * 8
            name_off = r.u32(entry_off, f"input[{i}].name_offset")
            start = r.u16(entry_off + 4, f"input[{i}].start")
            end = r.u16(entry_off + 6, f"input[{i}].end")
            name = r.cstring(symbol_abs + name_off, symbol_end) if dvle.symbol_size else ""
            dvle.inputs.append(ShaderInput(i, entry_off, name_off, start, end, name))

    def _parse_outputs(self, dvle: DVLEInfo) -> None:
        r = self._reader
        assert r is not None
        abs_off = dvle.offset + dvle.output_offset
        if not dvle.output_count:
            return
        if not r.require(abs_off, dvle.output_count * 8, f"DVLE[{dvle.index}] output table"):
            return
        for i in range(dvle.output_count):
            entry_off = abs_off + i * 8
            dvle.outputs.append(ShaderOutput(
                index=i,
                offset=entry_off,
                output_type=r.u16(entry_off, f"output[{i}].type"),
                register_id=r.u16(entry_off + 2, f"output[{i}].register"),
                mask=r.u16(entry_off + 4, f"output[{i}].mask"),
                unknown=r.u16(entry_off + 6, f"output[{i}].unknown"),
            ))

    def _parse_labels(self, dvle: DVLEInfo, symbol_abs: int, symbol_end: int) -> None:
        r = self._reader
        assert r is not None
        abs_off = dvle.offset + dvle.label_offset
        if not dvle.label_count:
            return
        if not r.require(abs_off, dvle.label_count * 0x10, f"DVLE[{dvle.index}] label table"):
            return
        for i in range(dvle.label_count):
            entry_off = abs_off + i * 0x10
            label_id = r.u8(entry_off, f"label[{i}].id")
            unknown_a = r.bytes(entry_off + 1, 3, f"label[{i}].unknown_a")
            opcode_address = r.u32(entry_off + 4, f"label[{i}].opcode_address")
            unknown_b = r.u32(entry_off + 8, f"label[{i}].unknown_b")
            name_off = r.u32(entry_off + 0x0C, f"label[{i}].name_offset")
            name = r.cstring(symbol_abs + name_off, symbol_end) if dvle.symbol_size else ""
            dvle.labels.append(ShaderLabel(i, entry_off, label_id, unknown_a, opcode_address, unknown_b, name_off, name))

    def _parse_constants(self, dvle: DVLEInfo) -> None:
        r = self._reader
        assert r is not None
        abs_off = dvle.offset + dvle.const_offset
        if not dvle.const_count:
            return
        if not r.require(abs_off, dvle.const_count * 0x14, f"DVLE[{dvle.index}] constant table"):
            return
        for i in range(dvle.const_count):
            entry_off = abs_off + i * 0x14
            entry_type = r.u8(entry_off, f"constant[{i}].type")
            register_id = r.u8(entry_off + 2, f"constant[{i}].id")
            length_hint = r.u8(entry_off + 3, f"constant[{i}].length_hint")
            raw = [0, 0, 0, 0]
            if entry_type == 2:
                raw = [r.u32(entry_off + 4 + j * 4, f"constant[{i}].float{j}") & 0xFFFFFF for j in range(4)]
            elif entry_type == 1:
                raw = list(r.bytes(entry_off + 4, 4, f"constant[{i}].int4"))
            elif entry_type == 0:
                raw[0] = r.u8(entry_off + 4, f"constant[{i}].bool")
            else:
                self.issues.append(ParseIssue("warning", f"DVLE[{dvle.index}] constant[{i}] has unknown type {entry_type} at 0x{entry_off:X}"))
                raw = [r.u32(entry_off + 4 + j * 4, f"constant[{i}].raw{j}") for j in range(4)]

            c = ShaderConstant(
                dvle_index=dvle.index,
                index=i,
                offset=entry_off,
                entry_type=entry_type,
                register_id=register_id,
                length_hint=length_hint,
                raw=raw,
                register_name=self._constant_register_name(entry_type, register_id),
            )
            dvle.constants.append(c)

    def _map_constant_names(self, dvle: DVLEInfo) -> None:
        for c in dvle.constants:
            reg = self._constant_register_number(c.entry_type, c.register_id)
            if reg is None:
                continue
            for inp in dvle.inputs:
                lo, hi = sorted((inp.start, inp.end))
                if lo <= reg <= hi:
                    c.mapped_input = inp.name
                    if inp.name:
                        if hi > lo:
                            c.name = f"{inp.name}[{reg - lo}]"
                        else:
                            c.name = inp.name
                    break

    def _annotate_instruction_metadata(self) -> None:
        if not self.dvlp:
            return

        for inst in self.dvlp.instructions:
            f = inst.fields
            f["source_line"] = self._source_line_for_instruction(inst.index)
            f["labels_here"] = []
            f["entrypoints"] = []
            f["end_markers"] = []
            f["active_dvles"] = []
            f["register_annotations"] = []
            f["target_annotations"] = []
            f["annotated_disasm_by_dvle"] = []

        for dvle in self.dvles:
            for lab in dvle.labels:
                if 0 <= lab.opcode_address < len(self.dvlp.instructions):
                    self.dvlp.instructions[lab.opcode_address].fields["labels_here"].append(self._label_annotation(dvle, lab))

            if 0 <= dvle.opcode_entry < len(self.dvlp.instructions):
                self.dvlp.instructions[dvle.opcode_entry].fields["entrypoints"].append(self._dvle_ref(dvle))
            if 0 <= dvle.opcode_end < len(self.dvlp.instructions):
                self.dvlp.instructions[dvle.opcode_end].fields["end_markers"].append(self._dvle_ref(dvle))

            for inst in self.dvlp.instructions:
                if not self._instruction_in_dvle_range(inst.index, dvle):
                    continue
                inst.fields["active_dvles"].append(self._dvle_ref(dvle))
                ann = self._instruction_annotation_for_dvle(inst, dvle)
                if ann["registers"]:
                    inst.fields["register_annotations"].extend(ann["registers"])
                if ann["targets"]:
                    inst.fields["target_annotations"].extend(ann["targets"])
                if ann["annotated_disasm"] != inst.disasm:
                    inst.fields["annotated_disasm_by_dvle"].append({
                        "dvle": dvle.index,
                        "shader_type": dvle.shader_type_name,
                        "disasm": ann["annotated_disasm"],
                    })
                    inst.fields.setdefault("annotated_disasm", ann["annotated_disasm"])

    def _source_line_for_instruction(self, inst_index: int) -> Optional[Dict[str, Any]]:
        if not self.dvlp or inst_index >= len(self.dvlp.lines):
            return None
        filename_off, line_num, filename = self.dvlp.lines[inst_index]
        return {"filename_offset": filename_off, "line": line_num, "filename": filename}

    @staticmethod
    def _instruction_in_dvle_range(inst_index: int, dvle: DVLEInfo) -> bool:
        lo, hi = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
        return lo <= inst_index <= hi

    @staticmethod
    def _dvle_ref(dvle: DVLEInfo) -> Dict[str, Any]:
        return {
            "dvle": dvle.index,
            "shader_type": dvle.shader_type_name,
            "opcode_entry": dvle.opcode_entry,
            "opcode_end": dvle.opcode_end,
        }

    def _label_display_name(self, lab: ShaderLabel) -> str:
        return lab.name or f"label_{lab.label_id:02X}_{lab.opcode_address:04d}"

    def _label_annotation(self, dvle: DVLEInfo, lab: ShaderLabel) -> Dict[str, Any]:
        return {
            "dvle": dvle.index,
            "label_index": lab.index,
            "label_id": lab.label_id,
            "name": self._label_display_name(lab),
            "opcode_address": lab.opcode_address,
            "symbol_offset": lab.name_offset,
        }

    def _labels_at(self, dvle: DVLEInfo, opcode_address: int) -> List[ShaderLabel]:
        return [lab for lab in dvle.labels if lab.opcode_address == opcode_address]

    def _target_text_for_dvle(self, dvle: DVLEInfo, target: int, targets_out: List[Dict[str, Any]]) -> str:
        labels = self._labels_at(dvle, int(target))
        if not labels:
            return str(target)
        lab = labels[0]
        ann = self._label_annotation(dvle, lab)
        targets_out.append(ann)
        return f"{target}<{ann['name']}>"

    def _input_symbol_for_register(self, dvle: DVLEInfo, register_number: int) -> Tuple[str, Optional[ShaderInput]]:
        for inp in dvle.inputs:
            lo, hi = sorted((inp.start, inp.end))
            if lo <= register_number <= hi:
                base = inp.name or f"input_{inp.index}"
                if hi > lo:
                    return f"{base}[{register_number - lo}]", inp
                return base, inp
        return "", None

    def _constant_for(self, dvle: DVLEInfo, entry_type: int, register_id: int) -> Optional[ShaderConstant]:
        for c in dvle.constants:
            if c.entry_type == entry_type and c.register_id == register_id:
                return c
        return None

    def _output_for_register(self, dvle: DVLEInfo, register_id: int) -> Optional[ShaderOutput]:
        for out in dvle.outputs:
            if out.register_id == register_id:
                return out
        return None

    def _dest_symbol_info(self, dvle: DVLEInfo, dst_raw: int) -> Dict[str, Any]:
        reg_name = pica_dest_reg_name(dst_raw)
        alias = self.register_alias(reg_name, dvle.index)
        if dst_raw < 0x10:
            out = self._output_for_register(dvle, dst_raw)
            if out:
                symbol = alias or OUTPUT_TYPES.get(out.output_type, f"output_{out.output_type}")
                return {
                    "register": reg_name,
                    "symbol": symbol,
                    "kind": "output",
                    "table": "User Symbol Map" if alias else "Output Register Table",
                    "table_index": out.index,
                    "mask": component_mask(out.mask),
                }
        return {"register": reg_name, "symbol": alias, "kind": "temporary" if dst_raw >= 0x10 else "output", "table": "User Symbol Map" if alias else "", "table_index": None}

    def _src_symbol_info(self, dvle: DVLEInfo, src_raw: int) -> Dict[str, Any]:
        reg_name = pica_src_reg_name(src_raw)
        if src_raw < 0x10:
            alias = self.register_alias(reg_name, dvle.index)
            symbol, inp = self._input_symbol_for_register(dvle, src_raw)
            return {
                "register": reg_name,
                "symbol": alias or symbol,
                "kind": "attribute/input",
                "table": "User Symbol Map" if alias else ("Input Register Table" if inp else ""),
                "table_index": inp.index if inp else None,
                "register_number": src_raw,
            }
        if src_raw < 0x20:
            alias = self.register_alias(reg_name, dvle.index)
            return {"register": reg_name, "symbol": alias, "kind": "temporary", "table": "User Symbol Map" if alias else "", "table_index": None, "register_number": src_raw}

        const_id = src_raw - 0x20
        register_number = FLOAT_REG_BASE + const_id
        c = self._constant_for(dvle, 2, const_id)
        input_symbol, inp = self._input_symbol_for_register(dvle, register_number)
        symbol = ""
        table = ""
        table_index: Optional[int] = None
        alias = self.register_alias(reg_name, dvle.index)
        if alias:
            symbol = alias
            table = "User Symbol Map"
        elif c and c.display_name != c.register_name:
            symbol = c.display_name
            table = "Constant Table"
            table_index = c.index
        elif input_symbol:
            symbol = input_symbol
            table = "Input Register Table"
            table_index = inp.index if inp else None
        return {
            "register": reg_name,
            "symbol": symbol,
            "kind": "float uniform/constant",
            "table": table,
            "table_index": table_index,
            "constant_index": c.index if c else None,
            "input_index": inp.index if inp else None,
            "register_number": register_number,
        }

    def _uniform_symbol_info(self, dvle: DVLEInfo, entry_type: int, uniform_id: int) -> Dict[str, Any]:
        if entry_type == 1:
            reg_name = f"i{uniform_id}"
            register_number = INT_REG_BASE + uniform_id
            kind = "int uniform"
        else:
            reg_name = f"b{uniform_id}"
            register_number = BOOL_REG_BASE + uniform_id
            kind = "bool uniform"
        c = self._constant_for(dvle, entry_type, uniform_id)
        input_symbol, inp = self._input_symbol_for_register(dvle, register_number)
        symbol = ""
        table = ""
        table_index: Optional[int] = None
        alias = self.register_alias(reg_name, dvle.index)
        if alias:
            symbol = alias
            table = "User Symbol Map"
        elif c and c.display_name != c.register_name:
            symbol = c.display_name
            table = "Constant Table"
            table_index = c.index
        elif input_symbol:
            symbol = input_symbol
            table = "Input Register Table"
            table_index = inp.index if inp else None
        return {
            "register": reg_name,
            "symbol": symbol,
            "kind": kind,
            "table": table,
            "table_index": table_index,
            "constant_index": c.index if c else None,
            "input_index": inp.index if inp else None,
            "register_number": register_number,
        }

    @staticmethod
    def _annotated_register_name(info: Dict[str, Any]) -> str:
        symbol = info.get("symbol") or ""
        if symbol:
            return str(symbol)
        return str(info.get("register", ""))

    def _instruction_annotation_for_dvle(self, inst: ShaderInstruction, dvle: DVLEInfo) -> Dict[str, Any]:
        f = inst.fields
        desc = f.get("opdesc", {}) if isinstance(f.get("opdesc"), dict) else {}
        registers: List[Dict[str, Any]] = []
        targets: List[Dict[str, Any]] = []

        def record(role: str, info: Dict[str, Any]) -> str:
            if info.get("symbol") or info.get("table"):
                rec = {"dvle": dvle.index, "role": role, **info}
                registers.append(rec)
            return self._annotated_register_name(info)

        def dst_text() -> str:
            raw = int(f.get("dst_raw", 0))
            base = record("dst", self._dest_symbol_info(dvle, raw))
            mask = str(desc.get("dest_mask", "xyzw"))
            return append_register_selector_for_display(base, mask)

        def src_text(role: str, raw_key: str, neg_key: str, swizzle_key: str) -> str:
            raw = int(f.get(raw_key, 0))
            info = self._src_symbol_info(dvle, raw)
            base = record(role, info)
            swizzle = str(desc.get(swizzle_key, "xyzw"))
            base = append_register_selector_for_display(base, swizzle)
            out = ("-" if bool(desc.get(neg_key, False)) else "") + base
            return out

        def uniform_text(entry_type: int, uniform_id: int) -> str:
            info = self._uniform_symbol_info(dvle, entry_type, uniform_id)
            return record("uniform", info)

        name = inst.mnemonic.lower()
        op = inst.opcode
        fmt = inst.fmt

        try:
            if fmt in {"1", "1u", "1i"}:
                s1 = src_text("src1", "src1_raw", "src1_neg", "src1_swizzle")
                if int(f.get("idx", 0)):
                    s1 += f"[{f.get('idx_name', '?')}]"
                if op in ARITH_ONE_ARG:
                    annotated = f"{name} {dst_text()}, {s1}"
                else:
                    s2 = src_text("src2", "src2_raw", "src2_neg", "src2_swizzle")
                    annotated = f"{name} {dst_text()}, {s1}, {s2}"
                return {"annotated_disasm": annotated, "registers": registers, "targets": targets}

            if fmt == "1c":
                s1 = src_text("src1", "src1_raw", "src1_neg", "src1_swizzle")
                s2 = src_text("src2", "src2_raw", "src2_neg", "src2_swizzle")
                annotated = f"cmp {str(f.get('cmpx_name', f.get('cmpx', 0))).lower()}, {str(f.get('cmpy_name', f.get('cmpy', 0))).lower()}, {s1}, {s2}"
                return {"annotated_disasm": annotated, "registers": registers, "targets": targets}

            if fmt == "2":
                target = int(f.get("target", 0))
                target_s = self._target_text_for_dvle(dvle, target, targets)
                num = int(f.get("num", 0))
                condop = str(f.get("condop_name", f.get("condop", 0))).lower()
                refx = int(f.get("refx", 0))
                refy = int(f.get("refy", 0))
                if op == 0x24:
                    annotated = f"{name} {target_s}, {num}"
                elif op == 0x23:
                    annotated = f"{name} {condop} x={refx} y={refy}"
                else:
                    annotated = f"{name} {target_s}, {num}, {condop} x={refx} y={refy}"
                return {"annotated_disasm": annotated, "registers": registers, "targets": targets}

            if fmt == "3":
                target = int(f.get("target", 0))
                target_s = self._target_text_for_dvle(dvle, target, targets)
                num = int(f.get("num", 0))
                uniform_id = int(f.get("uniform_id", 0))
                uniform = uniform_text(1 if op == 0x29 else 0, uniform_id)
                annotated = f"{name} {target_s}, {num}, {uniform}"
                return {"annotated_disasm": annotated, "registers": registers, "targets": targets}

            if fmt in {"5", "5i"}:
                s1 = src_text("src1", "src1_raw", "src1_neg", "src1_swizzle")
                s2 = src_text("src2", "src2_raw", "src2_neg", "src2_swizzle")
                s3 = src_text("src3", "src3_raw", "src3_neg", "src3_swizzle")
                if int(f.get("idx", 0)):
                    if fmt == "5i":
                        s3 += f"[{f.get('idx_name', '?')}]"
                    else:
                        s2 += f"[{f.get('idx_name', '?')}]"
                annotated = f"{name} {dst_text()}, {s1}, {s2}, {s3}"
                return {"annotated_disasm": annotated, "registers": registers, "targets": targets}
        except Exception as exc:
            self.issues.append(ParseIssue("warning", f"Could not annotate instruction {inst.index} for DVLE {dvle.index}: {exc}"))

        return {"annotated_disasm": inst.disasm, "registers": registers, "targets": targets}

    @staticmethod
    def _constant_register_number(entry_type: int, register_id: int) -> Optional[int]:
        if entry_type == 2:
            return FLOAT_REG_BASE + register_id
        if entry_type == 1:
            return INT_REG_BASE + register_id
        if entry_type == 0:
            return BOOL_REG_BASE + register_id
        return None

    @staticmethod
    def _constant_register_name(entry_type: int, register_id: int) -> str:
        if entry_type == 2:
            return f"c{register_id}"
        if entry_type == 1:
            return f"i{register_id}"
        if entry_type == 0:
            return f"b{register_id}"
        return f"?{register_id}"

    def _estimate_block_sizes(self) -> None:
        starts: List[Tuple[int, str, Any]] = []
        if self.dvlp:
            starts.append((self.dvlp.offset, "DVLP", self.dvlp))
        for dvle in self.dvles:
            starts.append((dvle.offset, "DVLE", dvle))
        starts = sorted((s for s in starts if 0 <= s[0] < len(self.data)), key=lambda x: x[0])
        for idx, (off, _kind, obj) in enumerate(starts):
            next_off = starts[idx + 1][0] if idx + 1 < len(starts) else len(self.data)
            obj.size = max(0, next_off - off)

    def save(self, filename: str, make_backup: bool = True) -> None:
        target = Path(filename)
        if make_backup and target.exists():
            backup = target.with_suffix(target.suffix + ".bak")
            shutil.copy2(target, backup)
        with open(target, "wb") as f:
            f.write(self.data)
        self.filename = str(target)

    def update_constant(self, dvle_idx: int, const_idx: int, raw_values: List[int]) -> None:
        dvle = self.dvles[dvle_idx]
        c = dvle.constants[const_idx]
        r = self._reader
        assert r is not None
        if not r.require(c.offset, 0x14, "constant update"):
            raise ValueError("Selected constant is outside the file range")
        c.raw = list(raw_values)
        if c.entry_type == 2:
            for j in range(4):
                struct.pack_into("<I", self.data, c.offset + 4 + j * 4, raw_values[j] & 0xFFFFFF)
        elif c.entry_type == 1:
            vals = [(int(v) & 0xFF) for v in raw_values[:4]]
            struct.pack_into("BBBB", self.data, c.offset + 4, *vals)
        elif c.entry_type == 0:
            struct.pack_into("B", self.data, c.offset + 4, 1 if raw_values[0] else 0)
        else:
            for j in range(4):
                struct.pack_into("<I", self.data, c.offset + 4 + j * 4, raw_values[j] & 0xFFFFFFFF)

    def update_opcode_word(self, opcode_index: int, word: int) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        if not (0 <= opcode_index < self.dvlp.opcode_count):
            raise IndexError("Opcode index out of range")
        abs_off = self.dvlp.offset + self.dvlp.opcode_offset + opcode_index * 4
        r = self._reader
        assert r is not None
        if not r.require(abs_off, 4, "opcode update"):
            raise ValueError("Selected opcode is outside the file range")
        struct.pack_into("<I", self.data, abs_off, int(word) & 0xFFFFFFFF)

    def update_opdesc(self, opdesc_index: int, desc: int, flags: int = 0) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        if not (0 <= opdesc_index < self.dvlp.opdesc_count):
            raise IndexError("Opdesc index out of range")
        abs_off = self.dvlp.offset + self.dvlp.opdesc_offset + opdesc_index * 8
        r = self._reader
        assert r is not None
        if not r.require(abs_off, 8, "opdesc update"):
            raise ValueError("Selected opdesc is outside the file range")
        struct.pack_into("<II", self.data, abs_off, int(desc) & 0xFFFFFFFF, int(flags) & 0xFFFFFFFF)


    def _symbol_maps(self) -> Dict[str, Dict[str, str]]:
        maps = getattr(self, "register_symbol_maps", None)
        if not isinstance(maps, dict):
            maps = {"global": dict(DEFAULT_REGISTER_SYMBOLS)}
            self.register_symbol_maps = maps
                                                                                                      
        maps.setdefault("global", {})
        return maps

    def register_alias(self, register: str, dvle_index: Optional[int] = None) -> str:
        reg = str(register).strip()
        maps = self._symbol_maps()
        key = f"dvle:{dvle_index}" if dvle_index is not None else "global"
        if key in maps and reg in maps[key]:
            return maps[key][reg]
        return maps.get("global", {}).get(reg, "")

    def set_register_alias(self, register: str, symbol: str, dvle_index: Optional[int] = None) -> None:
        reg = native_register_from_display(register)
        if not reg:
            raise ValueError("Register name is required, e.g. c17, v0, o2, r3, b0, i0")
                                                                                                      
        low = reg.lower()
        if low[0] in {"v", "r", "c"}:
            parse_pica_src_reg(low)
        elif low[0] == "o":
            parse_pica_dest_reg(low)
        elif low[0] in {"b", "i"}:
            int(low[1:] or "0", 0)
        else:
            raise ValueError("Register must start with v, r, c, o, b, or i")
        maps = self._symbol_maps()
        key = f"dvle:{dvle_index}" if dvle_index is not None else "global"
        symbol = str(symbol).strip()
        if symbol:
            maps.setdefault(key, {})[low] = symbol
        else:
            maps.setdefault(key, {}).pop(low, None)
        self.parse()

    def _alias_for_dest(self, dvle: DVLEInfo, dst_raw: int) -> str:
        reg = pica_dest_reg_name(dst_raw)
        return self.register_alias(reg, dvle.index)

    def _alias_for_src(self, dvle: DVLEInfo, src_raw: int) -> str:
        reg = pica_src_reg_name(src_raw)
        return self.register_alias(reg, dvle.index)

    def _alias_for_uniform(self, dvle: DVLEInfo, entry_type: int, uniform_id: int) -> str:
        reg = ("i" if entry_type == 1 else "b") + str(int(uniform_id))
        return self.register_alias(reg, dvle.index)

    def symbol_to_register_map(self, dvle_index: Optional[int] = None) -> Dict[str, str]:
        symbol_map: Dict[str, str] = {}

        def add(symbol: str, reg: str) -> None:
            sym = str(symbol or "").strip()
            rg = str(reg or "").strip().lower()
            if not sym or not rg:
                return
            symbol_map.setdefault(sym, rg)
            symbol_map.setdefault(sym.replace(" ", "_"), rg)
            stem, component_suffix = split_vector_component_suffix(sym)
            if component_suffix and stem and stem != sym:
                symbol_map.setdefault(stem, rg)
                symbol_map.setdefault(stem.replace(" ", "_"), rg)

        dvle: Optional[DVLEInfo] = None
        if dvle_index is not None and 0 <= int(dvle_index) < len(self.dvles):
            dvle = self.dvles[int(dvle_index)]

        if dvle is not None:
            for inp in dvle.inputs:
                lo, hi = sorted((inp.start, inp.end))
                for reg_num in range(lo, hi + 1):
                    if inp.name:
                        add(inp.name if lo == hi else f"{inp.name}[{reg_num - lo}]", f"v{reg_num}")
            for shader_out in dvle.outputs:
                add(OUTPUT_TYPES.get(shader_out.output_type, f"output_{shader_out.output_type}"), f"o{shader_out.register_id}")
            for c in dvle.constants:
                if c.display_name and c.display_name != c.register_name:
                    add(c.display_name, c.register_name)

        maps = self._symbol_maps()
        for reg, sym in maps.get("global", {}).items():
            if sym:
                add(str(sym), str(reg).lower())
        if dvle_index is not None:
            for reg, sym in maps.get(f"dvle:{int(dvle_index)}", {}).items():
                if sym:
                    add(str(sym), str(reg).lower())
        return symbol_map

    def register_display_name(self, register: str, dvle_index: Optional[int] = None) -> str:
        reg = str(register or "").strip().lower()
        if not reg:
            return ""
        alias = self.register_alias(reg, dvle_index)
        if alias:
            return f"{alias} ({reg})"
        if dvle_index is not None and 0 <= int(dvle_index) < len(self.dvles):
            dvle = self.dvles[int(dvle_index)]
            try:
                if reg.startswith("o"):
                    out = self._output_for_register(dvle, int(reg[1:], 0))
                    if out:
                        return f"{OUTPUT_TYPES.get(out.output_type, f'output_{out.output_type}')} ({reg})"
                if reg.startswith("v"):
                    symbol, _inp = self._input_symbol_for_register(dvle, int(reg[1:], 0))
                    if symbol:
                        return f"{symbol} ({reg})"
                if reg.startswith("c"):
                    c = self._constant_for(dvle, 2, int(reg[1:], 0))
                    if c and c.display_name != c.register_name:
                        return f"{c.display_name} ({reg})"
                if reg.startswith("i"):
                    c = self._constant_for(dvle, 1, int(reg[1:], 0))
                    if c and c.display_name != c.register_name:
                        return f"{c.display_name} ({reg})"
                if reg.startswith("b"):
                    c = self._constant_for(dvle, 0, int(reg[1:], 0))
                    if c and c.display_name != c.register_name:
                        return f"{c.display_name} ({reg})"
            except Exception:
                pass
        return reg

    def register_display_choices(self, dvle_index: Optional[int] = None, kind: str = "src") -> List[str]:
        kind = str(kind or "src").lower()
        regs: List[str] = []
        if kind == "dst":
            regs.extend(f"o{i}" for i in range(16))
            regs.extend(f"r{i}" for i in range(16))
        elif kind == "uniform":
            regs.extend(f"b{i}" for i in range(16))
            regs.extend(f"i{i}" for i in range(16))
        elif kind in {"src5", "src-noconst"}:
                                                                                           
            regs.extend(f"v{i}" for i in range(16))
            regs.extend(f"r{i}" for i in range(16))
        else:
                                                  
            regs.extend(f"v{i}" for i in range(16))
            regs.extend(f"r{i}" for i in range(16))
            regs.extend(f"c{i}" for i in range(96))
        return [self.register_display_name(reg, dvle_index) for reg in regs]

    def remove_register_alias(self, register: str, dvle_index: Optional[int] = None) -> None:
        reg = native_register_from_display(register)
        key = f"dvle:{dvle_index}" if dvle_index is not None else "global"
        maps = self._symbol_maps()
        if key in maps and reg in maps[key]:
            del maps[key][reg]
        self.parse()

    def export_register_symbol_map(self, filename: str) -> None:
        maps = self._symbol_maps()
        payload: Dict[str, Any] = {
            "format": "Cracko298.SHADER_REGISTER_SYMBOL_MAP.v1",
            "source": os.path.basename(self.filename),
            "global": maps.get("global", {}),
            "dvles": [],
        }
        for dvle in self.dvles:
            dvle_map: Dict[str, str] = dict(maps.get(f"dvle:{dvle.index}", {}))
            for inp in dvle.inputs:
                for reg_num in range(min(inp.start, inp.end), max(inp.start, inp.end) + 1):
                    name = inp.name if inp.start == inp.end else f"{inp.name}[{reg_num - min(inp.start, inp.end)}]"
                    if name:
                        dvle_map.setdefault(f"v{reg_num}", name)
            for out in dvle.outputs:
                type_name = OUTPUT_TYPES.get(out.output_type, f"output_{out.output_type}")
                dvle_map.setdefault(f"o{out.register_id}", type_name)
            for c in dvle.constants:
                if c.display_name and c.display_name != c.register_name:
                    dvle_map.setdefault(c.register_name, c.display_name)
            payload["dvles"].append({"index": dvle.index, "shader_type": dvle.shader_type_name, "registers": dvle_map})
        with open(filename, "w", encoding="utf-8") as f:
            json.dump(payload, f, indent=2)

    def import_register_symbol_map(self, filename: str) -> int:
        with open(filename, "r", encoding="utf-8") as f:
            payload = json.load(f)
        maps = self._symbol_maps()
        count = 0
        if isinstance(payload, dict):
            for reg, sym in (payload.get("global", {}) or {}).items():
                maps.setdefault("global", {})[str(reg).lower()] = str(sym)
                count += 1
            if isinstance(payload.get("registers"), dict):
                for reg, sym in payload["registers"].items():
                    maps.setdefault("global", {})[str(reg).lower()] = str(sym)
                    count += 1
            for dvle_obj in payload.get("dvles", []) or []:
                idx = dvle_obj.get("index")
                if idx is None:
                    continue
                key = f"dvle:{int(idx)}"
                for reg, sym in (dvle_obj.get("registers", {}) or {}).items():
                    maps.setdefault(key, {})[str(reg).lower()] = str(sym)
                    count += 1
        self.parse()
        return count


    @staticmethod
    def _export_safe_name(name: str, fallback: str = "sym") -> str:
        s = str(name or "").strip().replace("$", ".")
        if not s:
            s = fallback
                                                                                 
                                                                
        base, _suffix = split_vector_component_suffix(s)
        s = base or s
        s = re.sub(r"[^A-Za-z0-9_\[\]]+", "_", s).strip("_")
        if not s:
            s = fallback
        if re.match(r"^\d", s):
            s = "_" + s
        return s

    @staticmethod
    def _format_source_float(value: float) -> str:
        try:
            v = float(value)
        except Exception:
            v = 0.0
        if not math.isfinite(v):
            v = 0.0
        if v == 0.0:
            return "0.000000"
        if abs(v) < 0.0001:
            return f"{v:.8f}".rstrip("0").rstrip(".")
        return f"{v:.6f}"

    @staticmethod
    def _format_source_value(value: Any, entry_type: int) -> str:
        if entry_type == 2:
            return SHBINParser._format_source_float(float(value))
        if entry_type == 0:
            return "true" if bool(value) else "false"
        try:
            return str(int(value))
        except Exception:
            return "0"

    @staticmethod
    def _output_property_source_name(output_type: int) -> str:
        raw = OUTPUT_TYPES.get(int(output_type), f"output_{int(output_type)}")
        raw = raw.replace("result.", "")
        return raw

    @staticmethod
    def _default_output_alias(output_type: int, register_id: int, used: set[str]) -> str:
        prop = SHBINParser._output_property_source_name(output_type).lower()
        defaults = {
            "position": "outPos",
            "normalquat": "outNormalQuat",
            "color": "outColor",
            "texcoord0": "outCoord0",
            "texcoord0w": "outCoord0W",
            "texcoord1": "outCoord1",
            "texcoord2": "outCoord2",
            "view": "outView",
        }
        base = defaults.get(prop, f"out{int(register_id)}")
        name = base
        n = 1
        while name in used:
            n += 1
            name = f"{base}_{n}"
        used.add(name)
        return name

    @staticmethod
    def _register_from_uniform_number(number: int) -> str:
        n = int(number)
        if FLOAT_REG_BASE <= n < INT_REG_BASE:
            return f"c{n - FLOAT_REG_BASE}"
        if INT_REG_BASE <= n < BOOL_REG_BASE:
            return f"i{n - INT_REG_BASE}"
        if BOOL_REG_BASE <= n < BOOL_REG_BASE + 16:
            return f"b{n - BOOL_REG_BASE}"
        if 0 <= n < 16:
            return f"v{n}"
        return f"u{n}"

    @staticmethod
    def _register_range_from_uniform(inp: ShaderInput) -> Tuple[str, str, str, int]:
        start_reg = SHBINParser._register_from_uniform_number(int(inp.start))
        end_reg = SHBINParser._register_from_uniform_number(int(inp.end))
        prefix = start_reg[0] if start_reg else "u"
        try:
            size = abs(int(inp.end) - int(inp.start)) + 1
        except Exception:
            size = 1
        return prefix, start_reg, end_reg, size

    def _constant_register_set(self, dvle: DVLEInfo) -> set[Tuple[int, int]]:
        return {(int(c.entry_type), int(c.register_id)) for c in dvle.constants}

    def _constant_name_for_register(self, dvle: DVLEInfo, entry_type: int, register_id: int) -> str:
        c = self._constant_for(dvle, int(entry_type), int(register_id))
        if c and c.display_name and c.display_name != c.register_name:
            return self._export_safe_name(c.display_name, f"const{register_id}")
        return f"const{register_id}"

    def _vsh_alias_maps(self, dvle: DVLEInfo) -> Tuple[Dict[str, str], Dict[str, str], Dict[str, str]]:
        """Return dest/src/uniform alias maps for readable VSH export."""
        dest_alias: Dict[str, str] = {}
        src_alias: Dict[str, str] = {}
        uniform_alias: Dict[str, str] = {}

        used_outputs: set[str] = set()
        for out in dvle.outputs:
            alias = self._default_output_alias(out.output_type, out.register_id, used_outputs)
            dest_alias[f"o{int(out.register_id)}"] = alias

        for inp in dvle.inputs:
            prefix, start_reg, _end_reg, size = self._register_range_from_uniform(inp)
            base_name = self._export_safe_name(inp.name, start_reg)
            if prefix == "v":
                lo = int(inp.start)
                for i in range(size):
                    src_alias[f"v{lo + i}"] = base_name if size == 1 else f"{base_name}[{i}]"
            elif prefix == "c":
                lo = int(inp.start) - FLOAT_REG_BASE
                for i in range(size):
                    src_alias[f"c{lo + i}"] = base_name if size == 1 else f"{base_name}[{i}]"
            elif prefix == "i":
                lo = int(inp.start) - INT_REG_BASE
                for i in range(size):
                    uniform_alias[f"i{lo + i}"] = base_name if size == 1 else f"{base_name}[{i}]"
            elif prefix == "b":
                lo = int(inp.start) - BOOL_REG_BASE
                for i in range(size):
                    uniform_alias[f"b{lo + i}"] = base_name if size == 1 else f"{base_name}[{i}]"

                                                                                    
                                            
        maps = self._symbol_maps()
        for reg, sym in maps.get("global", {}).items():
            reg_l = str(reg).lower()
            sym_s = self._export_safe_name(str(sym), reg_l)
            if reg_l.startswith("o"):
                dest_alias[reg_l] = sym_s
            elif reg_l.startswith(("v", "r", "c")):
                src_alias[reg_l] = sym_s
            elif reg_l.startswith(("i", "b")):
                uniform_alias[reg_l] = sym_s
        for reg, sym in maps.get(f"dvle:{int(dvle.index)}", {}).items():
            reg_l = str(reg).lower()
            sym_s = self._export_safe_name(str(sym), reg_l)
            if reg_l.startswith("o"):
                dest_alias[reg_l] = sym_s
            elif reg_l.startswith(("v", "r", "c")):
                src_alias[reg_l] = sym_s
            elif reg_l.startswith(("i", "b")):
                uniform_alias[reg_l] = sym_s

        return dest_alias, src_alias, uniform_alias

    @staticmethod
    def _append_component_suffix(base: str, suffix: str, *, omit_xyzw: bool = True) -> str:
        s = str(suffix or "").strip().lower()
        if not s or s == "-" or (omit_xyzw and s == "xyzw"):
            return str(base)
        return f"{base}.{s}"

    def _format_export_dest(self, raw: int, mask: str, dest_alias: Dict[str, str], *, symbolic: bool) -> str:
        reg = pica_dest_reg_name(int(raw))
        base = dest_alias.get(reg, reg) if symbolic else reg
        if symbolic and reg in dest_alias:
                                                                               
            out_mask = ""
            for dvle in self.dvles:
                for out in dvle.outputs:
                    if f"o{int(out.register_id)}" == reg:
                        out_mask = component_mask(out.mask)
                        break
                if out_mask:
                    break
            if mask == out_mask:
                return base
        return self._append_component_suffix(base, mask, omit_xyzw=True)

    def _format_export_src(self, raw: int, neg: bool, swizzle: str, src_alias: Dict[str, str], *, symbolic: bool) -> str:
        reg = pica_src_reg_name(int(raw))
        base = src_alias.get(reg, reg) if symbolic else reg
        text = self._append_component_suffix(base, swizzle, omit_xyzw=True)
        return ("-" if neg else "") + text

    def _target_label_map(self, dvle: DVLEInfo) -> Dict[int, str]:
        out: Dict[int, str] = {}
        for lab in dvle.labels:
            name = self._label_display_name(lab).replace(" ", "_")
            if name:
                out.setdefault(int(lab.opcode_address), name)
        return out

    def _paired_proc_ranges(self, dvle: DVLEInfo) -> List[Tuple[str, int, int]]:
        labels = [(self._label_display_name(lab).replace(" ", "_"), int(lab.opcode_address)) for lab in dvle.labels]
        by_lower = {name.lower(): (name, addr) for name, addr in labels}
        ranges: List[Tuple[str, int, int]] = []
        for name, addr in labels:
            if name.lower().startswith("end"):
                continue
            end_pair = by_lower.get(("end" + name).lower())
            if end_pair is None:
                continue
            _end_name, end_addr = end_pair
            if end_addr >= addr:
                ranges.append((name, addr, end_addr))
        if not ranges:
            start = int(dvle.opcode_entry)
            end = int(dvle.opcode_end)
            if end < start:
                start, end = end, start
            ranges.append(("main", start, end))
        ranges.sort(key=lambda x: (x[1], x[2], x[0].lower()))
        return ranges

    def _is_ret_nop(self, inst: ShaderInstruction, proc_end: Optional[int]) -> bool:
        if proc_end is None:
            return False
        if inst.mnemonic.upper() != "NOP":
            return False
        return int(inst.index) == int(proc_end) - 1

    def _format_export_instruction(self, inst: ShaderInstruction, dvle: DVLEInfo,
                                   dest_alias: Dict[str, str], src_alias: Dict[str, str],
                                   uniform_alias: Dict[str, str], label_map: Dict[int, str],
                                   *, symbolic: bool, proc_end: Optional[int] = None) -> str:
        if self._is_ret_nop(inst, proc_end):
            return "ret"
        f = inst.fields
        name = str(inst.mnemonic).lower()
        fmt = str(inst.fmt)
        if fmt in {"1", "1u", "1i"}:
            desc = f.get("opdesc", {}) or {}
            mask = str(desc.get("dest_mask", "xyzw"))
            dst = self._format_export_dest(int(f.get("dst_raw", 0)), mask, dest_alias, symbolic=symbolic)
            s1 = self._format_export_src(int(f.get("src1_raw", 0)), bool(desc.get("src1_neg", False)), str(desc.get("src1_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            if int(f.get("idx", 0)):
                s1 += f"[{ADDR_REG_NAMES.get(int(f.get('idx', 0)), '?')}]"
            if inst.opcode in ARITH_ONE_ARG:
                return f"{name} {dst}, {s1}"
            s2 = self._format_export_src(int(f.get("src2_raw", 0)), bool(desc.get("src2_neg", False)), str(desc.get("src2_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            return f"{name} {dst}, {s1}, {s2}"

        if fmt == "1c":
            desc = f.get("opdesc", {}) or {}
            s1 = self._format_export_src(int(f.get("src1_raw", 0)), bool(desc.get("src1_neg", False)), str(desc.get("src1_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            s2 = self._format_export_src(int(f.get("src2_raw", 0)), bool(desc.get("src2_neg", False)), str(desc.get("src2_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            return f"cmp {CMP_OP_NAMES.get(int(f.get('cmpx', 0)), int(f.get('cmpx', 0))).lower()}, {CMP_OP_NAMES.get(int(f.get('cmpy', 0)), int(f.get('cmpy', 0))).lower()}, {s1}, {s2}"

        if fmt in {"5", "5i"}:
            desc = f.get("opdesc", {}) or {}
            mask = str(desc.get("dest_mask", "xyzw"))
            dst = self._format_export_dest(int(f.get("dst_raw", 0)), mask, dest_alias, symbolic=symbolic)
            s1 = self._format_export_src(int(f.get("src1_raw", 0)), bool(desc.get("src1_neg", False)), str(desc.get("src1_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            s2 = self._format_export_src(int(f.get("src2_raw", 0)), bool(desc.get("src2_neg", False)), str(desc.get("src2_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            s3 = self._format_export_src(int(f.get("src3_raw", 0)), bool(desc.get("src3_neg", False)), str(desc.get("src3_swizzle", "xyzw")), src_alias, symbolic=symbolic)
            if int(f.get("idx", 0)):
                if fmt == "5i":
                    s3 += f"[{ADDR_REG_NAMES.get(int(f.get('idx', 0)), '?')}]"
                else:
                    s2 += f"[{ADDR_REG_NAMES.get(int(f.get('idx', 0)), '?')}]"
            return f"{name} {dst}, {s1}, {s2}, {s3}"

        if fmt == "0":
            return name

        if fmt == "2":
            target = int(f.get("target", 0))
            target_text = label_map.get(target, str(target))
            num = int(f.get("num", 0))
            cond = CONDOP_NAMES.get(int(f.get("condop", 0)), str(f.get("condop", 0))).lower()
            refx = int(f.get("refx", 0))
            refy = int(f.get("refy", 0))
            if inst.opcode == 0x24:
                return f"call {target_text}"
            if inst.opcode == 0x23:
                return f"breakc {cond} x={refx} y={refy}"
            return f"{name} {target_text}, {num}, {cond} x={refx} y={refy}"

        if fmt == "3":
            target = int(f.get("target", 0))
            target_text = label_map.get(target, str(target))
            num = int(f.get("num", 0))
            prefix = "i" if inst.opcode == 0x29 else "b"
            reg = f"{prefix}{int(f.get('uniform_id', 0))}"
            reg = uniform_alias.get(reg, reg) if symbolic else reg
            return f"{name} {target_text}, {num}, {reg}"

        if fmt == "4":
            return f"setemit vtx={int(f.get('vertex_id', 0))} prim={int(f.get('prim_emit', 0))} winding={int(f.get('winding', 0))}"

        return f".word 0x{int(inst.word) & 0xFFFFFFFF:08X}"

    def _write_export_instruction_range(self, f: Any, dvle: DVLEInfo, start: int, end: int,
                                        *, symbolic: bool, indent: str = "", proc_end: Optional[int] = None) -> None:
        if not self.dvlp:
            return
        dest_alias, src_alias, uniform_alias = self._vsh_alias_maps(dvle) if symbolic else ({}, {}, {})
        label_map = self._target_label_map(dvle)
        hi = min(int(end), len(self.dvlp.instructions))
        lo = max(0, int(start))
        for idx in range(lo, hi):
            inst = self.dvlp.instructions[idx]
            line = self._format_export_instruction(inst, dvle, dest_alias, src_alias, uniform_alias, label_map, symbolic=symbolic, proc_end=proc_end)
            f.write(f"{indent}{line}\n")

    def export_clean_asm_source(self, filename: str) -> None:
        """Export clean, source-style ASM without numeric prefixes or comments."""
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        dvle = self.dvles[0] if self.dvles else None
        if dvle is None:
            raise ValueError("No DVLE metadata loaded")
        with open(filename, "w", encoding="utf-8") as f:
            for inp in dvle.inputs:
                name = str(inp.name or "").replace("$", ".")
                if not name:
                    continue
                _prefix, start_reg, end_reg, _size = self._register_range_from_uniform(inp)
                if start_reg == end_reg:
                    f.write(f"#pragma bind_symbol ( {name} , {start_reg} )\n")
                else:
                    f.write(f"#pragma bind_symbol ( {name} , {start_reg} , {end_reg} )\n")
            if dvle.inputs:
                f.write("\n")
            for out in dvle.outputs:
                prop = self._output_property_source_name(out.output_type)
                mask = component_mask(out.mask)
                prop_text = prop if mask == "xyzw" else f"{prop}.{mask}"
                f.write(f"#pragma output_map ( {prop_text} , o{int(out.register_id)} )\n")
            if dvle.outputs:
                f.write("\n")
            for c in dvle.constants:
                vals = c.values_for_display
                if c.entry_type == 2:
                    body = ", ".join(self._format_source_float(float(v)) for v in vals[:4])
                    f.write(f"def {c.register_name}, {body}\n")
                elif c.entry_type == 1:
                    body = ", ".join(str(int(v)) for v in vals[:4])
                    f.write(f"def {c.register_name}, {body}\n")
                elif c.entry_type == 0:
                    f.write(f"def {c.register_name}, {1 if vals and vals[0] else 0}, 0, 0, 0\n")
            if dvle.constants:
                f.write("\n")

            ranges = self._paired_proc_ranges(dvle)
            covered: set[int] = set()
            for name, start, end in ranges:
                f.write(f"{name}:\n")
                self._write_export_instruction_range(f, dvle, start, end, symbolic=False, proc_end=end)
                f.write(f"end{name}:\n\n")
                covered.update(range(start, end))
            if not ranges:
                self._write_export_instruction_range(f, dvle, 0, len(self.dvlp.instructions), symbolic=False)

    def export_vsh_source(self, filename: str) -> None:
        """Export clean Picasso-style .vsh source without comments."""
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        dvle = self.dvles[0] if self.dvles else None
        if dvle is None:
            raise ValueError("No DVLE metadata loaded")
        const_regs = self._constant_register_set(dvle)
        used_const_regs: set[Tuple[int, int]] = set()
        dest_alias, _src_alias, _uniform_alias = self._vsh_alias_maps(dvle)

        with open(filename, "w", encoding="utf-8") as f:
            for inp in dvle.inputs:
                prefix, start_reg, _end_reg, size = self._register_range_from_uniform(inp)
                name = self._export_safe_name(inp.name, start_reg)
                if prefix == "v":
                    f.write(f".in {name} {start_reg}\n")
                elif prefix == "c":
                    reg_id = int(inp.start) - FLOAT_REG_BASE
                    if (2, reg_id) in const_regs and size == 1:
                        used_const_regs.add((2, reg_id))
                        continue
                    suffix = f"[{size}]" if size > 1 else ""
                    f.write(f".fvec {name}{suffix}\n")
                elif prefix == "i":
                    reg_id = int(inp.start) - INT_REG_BASE
                    if (1, reg_id) in const_regs and size == 1:
                        used_const_regs.add((1, reg_id))
                        continue
                    suffix = f"[{size}]" if size > 1 else ""
                    f.write(f".ivec {name}{suffix}\n")
                elif prefix == "b":
                    reg_id = int(inp.start) - BOOL_REG_BASE
                    if (0, reg_id) in const_regs and size == 1:
                        used_const_regs.add((0, reg_id))
                        continue
                    suffix = f"[{size}]" if size > 1 else ""
                    f.write(f".bool {name}{suffix}\n")
            if dvle.inputs:
                f.write("\n")

            for out in dvle.outputs:
                alias = dest_alias.get(f"o{int(out.register_id)}", self._default_output_alias(out.output_type, out.register_id, set()))
                prop = self._output_property_source_name(out.output_type)
                mask = component_mask(out.mask)
                prop_text = prop if mask == "xyzw" else f"{prop}.{mask}"
                                                                                            
                                                                          
                f.write(f".out {alias} {prop_text} o{int(out.register_id)}\n")
            if dvle.outputs:
                f.write("\n")

            for c in dvle.constants:
                name = self._constant_name_for_register(dvle, c.entry_type, c.register_id)
                vals = c.values_for_display
                                                                                     
                                                                                  
                                                                                  
                                                                                     
                                                                                   
                has_named_uniform = bool(c.mapped_input and c.display_name and c.display_name != c.register_name)
                if c.entry_type == 2:
                    body = ", ".join(self._format_source_float(float(v)) for v in vals[:4])
                    if has_named_uniform:
                        f.write(f".constf {name}({body})\n")
                    else:
                        f.write(f".setf {c.register_name}({body})\n")
                elif c.entry_type == 1:
                    body = ", ".join(str(int(v)) for v in vals[:4])
                    if has_named_uniform:
                        f.write(f".consti {name}({body})\n")
                    else:
                        f.write(f".seti {c.register_name}({body})\n")
                elif c.entry_type == 0:
                    if has_named_uniform:
                        f.write(f".setb {name} {1 if vals and vals[0] else 0}\n")
                    else:
                        f.write(f".setb {c.register_name} {1 if vals and vals[0] else 0}\n")
            if dvle.constants:
                f.write("\n")

            ranges = self._paired_proc_ranges(dvle)
            for name, start, end in ranges:
                f.write(f".proc {name}\n")
                self._write_export_instruction_range(f, dvle, start, end, symbolic=True, indent="    ", proc_end=end)
                f.write(".end\n\n")

    def export_source_by_extension(self, filename: str) -> None:
        ext = Path(filename).suffix.lower()
        if ext == ".vsh":
            self.export_vsh_source(filename)
        else:
            self.export_clean_asm_source(filename)

    def export_full_asm(self, filename: str) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        with open(filename, "w", encoding="utf-8") as f:
            f.write(f"; Reassemblable PICA ASM from {os.path.basename(self.filename)}\n")
            f.write(f"{ASM_CONTROL_COMMENT}\n")
            f.write("; Keep the numeric prefix if you want safe in-place import.\n\n")
            for dvle in self.dvles:
                f.write(f"; DVLE {dvle.index} {dvle.shader_type_name}: entry={dvle.opcode_entry} end={dvle.opcode_end}\n")
                aliases = self.symbol_to_register_map(dvle.index)
                if aliases:
                    f.write("; Aliases:\n")
                    for sym, reg in sorted(aliases.items(), key=lambda kv: kv[1]):
                        f.write(f";   {reg} = {sym}\n")
                f.write("\n")
            emitted_labels: set[str] = set()
            for inst in self.dvlp.instructions:
                for lab in inst.fields.get("labels_here", []):
                    name = str(lab.get("name") or f"label_{lab.get('opcode_address', inst.index)}").replace(" ", "_")
                    f.write(f"{name}:\n")
                    emitted_labels.add(name.lower())
                ann = inst.fields.get("annotated_disasm", inst.disasm)
                ann = str(ann)
                desc = inst.fields.get("desc_id")
                desc_comment = f" desc_id={desc}" if desc is not None else ""
                f.write(f"{inst.index:04d}: {ann:<58} ; word=0x{inst.word:08X}{desc_comment}\n")
                                                                                  
                                                                              
            final_idx = len(self.dvlp.instructions)
            for dvle in self.dvles:
                for lab in dvle.labels:
                    name = self._label_display_name(lab).replace(" ", "_") if hasattr(self, "_label_display_name") else str(lab.name).replace(" ", "_")
                    if lab.opcode_address == final_idx and name and name.lower() not in emitted_labels:
                        f.write(f"{name}:\n")
                        emitted_labels.add(name.lower())

    def import_full_asm(self, filename: str) -> int:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        with open(filename, "r", encoding="utf-8") as f:
            src_lines = f.readlines()
        labels: Dict[str, int] = {}
        next_index = 0
        for raw in src_lines:
            text = clean_asm_line(raw)
            if not text:
                continue
            if text.endswith(":"):
                labels[text[:-1].strip()] = next_index
                continue
            explicit, body = strip_asm_index_prefix(raw)
            if not body:
                continue
            if explicit is not None:
                next_index = explicit
            if body.endswith(":"):
                labels[body[:-1].strip()] = next_index
                continue
            next_index += 1

        updated = 0
        seq_index = 0
        symbol_to_reg = self.symbol_to_register_map(None)
                                                                                           
        for dvle in self.dvles:
            for sym, reg in self.symbol_to_register_map(dvle.index).items():
                symbol_to_reg.setdefault(sym, reg)
        for raw in src_lines:
            clean = clean_asm_line(raw)
            if not clean or clean.endswith(":"):
                continue
            explicit, body = strip_asm_index_prefix(raw)
            if not body or body.endswith(":"):
                continue
            idx = explicit if explicit is not None else seq_index
            seq_index = idx + 1
            if not (0 <= idx < self.dvlp.opcode_count):
                continue
            existing = self.dvlp.instructions[idx]
            desc_id = int(existing.fields.get("desc_id", 0))
            try:
                word, opdesc_fields = parse_general_asm_line(body, base_word=existing.word, default_desc_id=desc_id, labels=labels, symbol_to_register=symbol_to_reg)
            except ValueError:
                continue
            self.update_opcode_word(idx, word)
            if opdesc_fields is not None and 0 <= desc_id < self.dvlp.opdesc_count:
                old_desc, old_flags = self.dvlp.opdescs[desc_id]
                desc, flags = pica_encode_opdesc(
                    opdesc_fields.get("mask", "xyzw"),
                    opdesc_fields.get("src1_swizzle", "xyzw"),
                    opdesc_fields.get("src2_swizzle", "xyzw"),
                    opdesc_fields.get("src3_swizzle", "xyzw"),
                    bool(opdesc_fields.get("src1_neg", False)),
                    bool(opdesc_fields.get("src2_neg", False)),
                    bool(opdesc_fields.get("src3_neg", False)),
                    preserve_flags=old_flags,
                )
                self.update_opdesc(desc_id, desc, flags)
            updated += 1
        self.parse()
        return updated

    def _target_adjusted_word(self, word: int, threshold: int, delta: int) -> int:
        op = pica_effective_opcode(word)
        fmt = pica_instruction_format(op, is_word=False)
        if fmt not in {"2", "3"}:
            return word & 0xFFFFFFFF
        target = get_bits(word, 10, 12)
        if delta > 0 and target >= threshold:
            target += delta
        elif delta < 0 and target > threshold:
            target += delta
        target = max(0, min(0xFFF, target))
        return set_bits(word, 10, 12, target) & 0xFFFFFFFF

    def insert_nop_instruction(self, index: int) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        if not (0 <= index < self.dvlp.opcode_count):
            raise IndexError("Instruction index out of range")
        words = list(self.dvlp.opcodes)
        words = [self._target_adjusted_word(w, index, +1) for w in words]
        nop = pica_build_instruction_word("NOP")
        words.insert(index, nop)
        words = words[:self.dvlp.opcode_count]
        for i, word in enumerate(words):
            self.update_opcode_word(i, word)
        self.parse()

    def delete_instruction_shift_up(self, index: int) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        if not (0 <= index < self.dvlp.opcode_count):
            raise IndexError("Instruction index out of range")
        words = list(self.dvlp.opcodes)
        del words[index]
        words.append(pica_build_instruction_word("NOP"))
        words = [self._target_adjusted_word(w, index, -1) for w in words]
        for i, word in enumerate(words[:self.dvlp.opcode_count]):
            self.update_opcode_word(i, word)
        self.parse()

    def add_instruction_at_end_of_range(self, dvle_index: int, asm_line: str) -> int:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        if not (0 <= dvle_index < len(self.dvles)):
            raise IndexError("DVLE index out of range")
        dvle = self.dvles[dvle_index]
        idx = max(0, min(self.dvlp.opcode_count - 1, int(dvle.opcode_end)))
        self.insert_nop_instruction(idx)
        self.parse()
        existing = self.dvlp.instructions[idx]
        word, opdesc_fields = parse_general_asm_line(asm_line, base_word=existing.word, default_desc_id=int(existing.fields.get("desc_id", 0)), symbol_to_register=self.symbol_to_register_map(dvle_index))
        self.update_opcode_word(idx, word)
        self.parse()
        return idx

    def control_flow_graph(self, dvle_index: int = 0) -> Dict[str, Any]:
        if not self.dvlp or not self.dvles:
            return {"nodes": [], "edges": []}
        dvle = self.dvles[max(0, min(dvle_index, len(self.dvles) - 1))]
        start, end = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
        end = min(end, len(self.dvlp.instructions) - 1)
        labels_by_addr: Dict[int, str] = {}
        for lab in dvle.labels:
            labels_by_addr[lab.opcode_address] = self._label_display_name(lab)
        leaders = {start}
        for inst in self.dvlp.instructions[start:end + 1]:
            f = inst.fields
            if inst.fmt in {"2", "3"}:
                target = int(f.get("target", -1))
                if start <= target <= end:
                    leaders.add(target)
                if inst.index + 1 <= end:
                    leaders.add(inst.index + 1)
            if inst.mnemonic.upper() == "END" and inst.index + 1 <= end:
                leaders.add(inst.index + 1)
        sorted_leaders = sorted(leaders)
        nodes = []
        for i, leader in enumerate(sorted_leaders):
            block_end = (sorted_leaders[i + 1] - 1) if i + 1 < len(sorted_leaders) else end
            label = labels_by_addr.get(leader, f"block_{leader:04d}")
            nodes.append({"id": leader, "start": leader, "end": block_end, "label": label})
        node_starts = {n["start"] for n in nodes}
        edges = []
        for node in nodes:
            last = self.dvlp.instructions[node["end"]]
            f = last.fields
            kind = last.mnemonic.upper()
            if last.fmt in {"2", "3"}:
                target = int(f.get("target", -1))
                if target in node_starts or start <= target <= end:
                    edges.append({"from": node["start"], "to": target, "kind": kind.lower()})
                if kind not in {"CALL", "CALLU"} and node["end"] + 1 <= end:
                    edges.append({"from": node["start"], "to": node["end"] + 1, "kind": "fallthrough"})
            elif kind != "END" and node["end"] + 1 <= end:
                edges.append({"from": node["start"], "to": node["end"] + 1, "kind": "fallthrough"})
        return {"dvle": dvle.index, "nodes": nodes, "edges": edges}

    def register_lifetime_report(self, dvle_index: int = 0) -> str:
        if not self.dvlp or not self.dvles:
            return "No shader loaded."
        dvle = self.dvles[max(0, min(dvle_index, len(self.dvles) - 1))]
        start, end = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
        end = min(end, len(self.dvlp.instructions) - 1)
        reads: Dict[str, List[int]] = {}
        writes: Dict[str, List[int]] = {}
        deps: Dict[str, set] = {}
        def reg_src(raw: int) -> str:
            reg = pica_src_reg_name(raw)
            alias = self.register_alias(reg, dvle.index)
            return f"{reg}<{alias}>" if alias else reg
        def reg_dst(raw: int) -> str:
            reg = pica_dest_reg_name(raw)
            alias = self.register_alias(reg, dvle.index)
            return f"{reg}<{alias}>" if alias else reg
        for inst in self.dvlp.instructions[start:end + 1]:
            f = inst.fields
            srcs = []
            for key in ("src1_raw", "src2_raw", "src3_raw"):
                if key in f:
                    srcs.append(reg_src(int(f[key])))
            for rname in srcs:
                reads.setdefault(rname, []).append(inst.index)
            if "dst_raw" in f:
                dst = reg_dst(int(f["dst_raw"]))
                writes.setdefault(dst, []).append(inst.index)
                combined = set(srcs)
                for sreg in srcs:
                    combined.update(deps.get(sreg, set()))
                deps[dst] = combined
        regs = sorted(set(reads) | set(writes), key=lambda x: (x[0], x))
        lines = [f"Register lifetime/dependency report for DVLE {dvle.index} ({dvle.shader_type_name})", f"Range: {start}..{end}", ""]
        for reg in regs:
            all_uses = reads.get(reg, []) + writes.get(reg, [])
            lifetime = f"{min(all_uses)}..{max(all_uses)}" if all_uses else "-"
            lines.append(f"{reg:34} life={lifetime:>9} reads={reads.get(reg, [])} writes={writes.get(reg, [])}")
            if deps.get(reg):
                lines.append(f"{'':34} depends on: {', '.join(sorted(deps[reg]))}")
        if not regs:
            lines.append("No register reads/writes decoded in this DVLE range.")
        return "\n".join(lines)

    def safety_issues(self) -> List[ParseIssue]:
        issues: List[ParseIssue] = list(self.issues)
        if not self.dvlp:
            return issues
        used_opdescs = set()
        for dvle in self.dvles:
            start, end = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
            if start < 0 or end >= len(self.dvlp.instructions):
                issues.append(ParseIssue("error", f"DVLE {dvle.index} opcode range {start}..{end} is outside the opcode table"))
                continue
            has_end = any(inst.mnemonic.upper() == "END" for inst in self.dvlp.instructions[start:end + 1])
            if not has_end:
                issues.append(ParseIssue("warning", f"DVLE {dvle.index} has no END instruction in its active range"))
            declared_outputs = {int(o.register_id) for o in dvle.outputs}
            declared_consts = {int(c.register_id) for c in dvle.constants if c.entry_type == 2}
            written_temps = set()
            for inst in self.dvlp.instructions[start:end + 1]:
                f = inst.fields
                desc_id = f.get("desc_id")
                if isinstance(desc_id, int):
                    used_opdescs.add(desc_id)
                    if not (0 <= desc_id < self.dvlp.opdesc_count):
                        issues.append(ParseIssue("error", f"Instruction {inst.index} references missing opdesc {desc_id}"))
                for key in ("src1_raw", "src2_raw", "src3_raw"):
                    if key not in f:
                        continue
                    raw = int(f[key])
                    if 0x10 <= raw < 0x20 and (raw - 0x10) not in written_temps:
                        issues.append(ParseIssue("warning", f"Instruction {inst.index} reads temp r{raw - 0x10} before a decoded write in DVLE {dvle.index}"))
                    if raw >= 0x20 and (raw - 0x20) not in declared_consts and not self.register_alias(f"c{raw - 0x20}", dvle.index):
                        issues.append(ParseIssue("info", f"Instruction {inst.index} reads c{raw - 0x20}, which is not in the constant table/symbol map for DVLE {dvle.index}"))
                if "dst_raw" in f:
                    dst = int(f["dst_raw"])
                    if dst >= 0x10:
                        written_temps.add(dst - 0x10)
                    elif dst not in declared_outputs and not self.register_alias(f"o{dst}", dvle.index):
                        issues.append(ParseIssue("warning", f"Instruction {inst.index} writes o{dst}, not declared in DVLE {dvle.index}'s output table"))
                if inst.fmt in {"2", "3"}:
                    target = int(f.get("target", -1))
                    if not (start <= target <= end):
                        issues.append(ParseIssue("warning", f"Instruction {inst.index} branch/call target {target} is outside DVLE {dvle.index} range {start}..{end}"))
        for i in range(self.dvlp.opdesc_count):
            if i not in used_opdescs:
                issues.append(ParseIssue("info", f"Opdesc {i} is unused by decoded instructions"))
        return issues

    def export_disassembly(self, filename: str) -> None:
        if not self.dvlp:
            raise ValueError("No DVLP program loaded")
        with open(filename, "w", encoding="utf-8") as f:
            f.write(f"; Disassembly from {os.path.basename(self.filename)}\n")
            f.write("; This is intended for patching/reference, not a full reassemblable source.\n")
            f.write("; Symbol annotations use reg<symbol> and label target<name> comments.\n\n")

            for dvle in self.dvles:
                f.write(f"; ---------------- DVLE {dvle.index} ({dvle.shader_type_name}) symbols ----------------\n")
                f.write(f"; Code range: entry={dvle.opcode_entry}, end={dvle.opcode_end}\n")
                if dvle.inputs:
                    f.write("; Input Register Table:\n")
                    for inp in dvle.inputs:
                        f.write(f";   [{inp.index:03d}] regs 0x{inp.start:02X}..0x{inp.end:02X} -> {inp.name} (sym_off=0x{inp.name_offset:X})\n")
                if dvle.outputs:
                    f.write("; Output Register Table:\n")
                    for out in dvle.outputs:
                        type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
                        f.write(f";   [{out.index:03d}] o{out.register_id} mask={component_mask(out.mask)} -> {type_name}\n")
                if dvle.labels:
                    f.write("; Label Table:\n")
                    for lab in dvle.labels:
                        f.write(f";   [{lab.index:03d}] {self._label_display_name(lab)}: opcode={lab.opcode_address} id={lab.label_id} sym_off=0x{lab.name_offset:X} unk_b=0x{lab.unknown_b:08X}\n")
                if dvle.symbols:
                    f.write("; Symbol Table:\n")
                    for rel, text in dvle.symbols:
                        f.write(f";   0x{rel:04X}: {text}\n")
                f.write("\n")

            for inst in self.dvlp.instructions:
                for lab in inst.fields.get("labels_here", []):
                    f.write(f"{lab.get('name')}: ; DVLE {lab.get('dvle')} label id={lab.get('label_id')}\n")
                for ref in inst.fields.get("entrypoints", []):
                    f.write(f"; DVLE {ref.get('dvle')} entry ({ref.get('shader_type')})\n")
                source = inst.fields.get("source_line")
                source_comment = ""
                if source:
                    source_comment = f" src={source.get('filename', '')}:{source.get('line', '')}"
                ann_disasm = inst.fields.get("annotated_disasm", inst.disasm)
                f.write(f"{inst.index:04d}: {ann_disasm:<64} ; word=0x{inst.word:08X} rawop=0x{inst.raw_opcode:02X} fmt={inst.fmt}{source_comment}\n")

    def to_dict(self) -> Dict[str, Any]:
        return {
            "filename": os.path.basename(self.filename),
            "file_size": len(self.data),
            "dvlb": {
                "dvle_count": len(self.dvle_offsets),
                "dvle_offsets": [f"0x{x:X}" for x in self.dvle_offsets],
                "dvlp_offset": f"0x{self.dvlp.offset:X}" if self.dvlp else None,
            },
            "dvlp": self._dvlp_to_dict(),
            "dvles": [self._dvle_to_dict(dvle) for dvle in self.dvles],
            "issues": [{"level": i.level, "message": i.message} for i in self.safety_issues()],
            "register_symbol_maps": self._symbol_maps(),
        }

    def _dvlp_to_dict(self) -> Optional[Dict[str, Any]]:
        if not self.dvlp:
            return None
        d = self.dvlp
        return {
            "offset": f"0x{d.offset:X}",
            "version": f"0x{d.version:04X}",
            "unknown": f"0x{d.unknown:04X}",
            "opcode_table": {"offset": f"0x{d.offset + d.opcode_offset:X}", "count": d.opcode_count},
            "opdesc_table": {"offset": f"0x{d.offset + d.opdesc_offset:X}", "count": d.opdesc_count},
            "line_table": {"offset": f"0x{d.offset + d.line_offset:X}", "count": d.line_count},
            "filename_symbols": d.filenames,
            "opcodes": [f"0x{x:08X}" for x in d.opcodes],
            "instructions": [
                {
                    "index": inst.index,
                    "offset": f"0x{inst.offset:X}",
                    "word": f"0x{inst.word:08X}",
                    "opcode": f"0x{inst.opcode:02X}",
                    "raw_opcode": f"0x{inst.raw_opcode:02X}",
                    "mnemonic": inst.mnemonic,
                    "format": inst.fmt,
                    "disasm": inst.disasm,
                    "fields": inst.fields,
                }
                for inst in d.instructions
            ],
            "opdescs": [
                {
                    "index": i,
                    "desc": f"0x{a:08X}",
                    "flags": f"0x{b:08X}",
                    **pica_decode_opdesc(a, b),
                }
                for i, (a, b) in enumerate(d.opdescs)
            ],
            "lines": [{"filename_offset": f"0x{a:X}", "line": b, "filename": c} for a, b, c in d.lines],
        }

    def _dvle_to_dict(self, dvle: DVLEInfo) -> Dict[str, Any]:
        return {
            "index": dvle.index,
            "offset": f"0x{dvle.offset:X}",
            "version": f"0x{dvle.version:04X}",
            "shader_type": dvle.shader_type_name,
            "opcode_entry": dvle.opcode_entry,
            "opcode_end": dvle.opcode_end,
            "constants": [
                {
                    "index": c.index,
                    "name": c.display_name,
                    "mapped_input": c.mapped_input,
                    "register": c.register_name,
                    "register_id": c.register_id,
                    "type": c.type_name,
                    "offset": f"0x{c.offset:X}",
                    "raw": [f"0x{x:X}" for x in c.raw],
                    "values": c.values_for_display,
                }
                for c in dvle.constants
            ],
            "inputs": [inp.__dict__ for inp in dvle.inputs],
            "outputs": [
                {
                    "index": out.index,
                    "type": OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}"),
                    "register_id": out.register_id,
                    "mask": component_mask(out.mask),
                    "unknown": f"0x{out.unknown:04X}",
                }
                for out in dvle.outputs
            ],
            "labels": [
                {
                    "index": lab.index,
                    "id": lab.label_id,
                    "name": lab.name,
                    "opcode_address": lab.opcode_address,
                    "unknown_b": f"0x{lab.unknown_b:08X}",
                }
                for lab in dvle.labels
            ],
            "symbols": dvle.symbols,
        }

    def export_json(self, filename: str) -> None:
        with open(filename, "w", encoding="utf-8") as f:
            json.dump(self.to_dict(), f, indent=2)

    def export_constants_csv(self, filename: str) -> None:
        with open(filename, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["dvle", "index", "name", "register", "type", "offset", "x", "y", "z", "w", "raw0", "raw1", "raw2", "raw3"])
            for dvle in self.dvles:
                for c in dvle.constants:
                    values = c.values_for_display
                    row_values = list(values) + [""] * (4 - len(values))
                    writer.writerow([
                        dvle.index,
                        c.index,
                        c.display_name,
                        c.register_name,
                        c.type_name,
                        f"0x{c.offset:X}",
                        *row_values[:4],
                        *[f"0x{x:X}" for x in c.raw],
                    ])

    def import_constant_values_json(self, filename: str) -> int:
        with open(filename, "r", encoding="utf-8") as f:
            payload = json.load(f)

        updated = 0
        dvle_payloads = payload.get("dvles", []) if isinstance(payload, dict) else []
        for dvle_obj in dvle_payloads:
            dvle_index = int(dvle_obj.get("index", -1))
            if not (0 <= dvle_index < len(self.dvles)):
                continue
            constants = dvle_obj.get("constants", []) or dvle_obj.get("uniforms", [])
            for cobj in constants:
                target = self._find_constant_for_import(dvle_index, cobj)
                if target is None:
                    continue
                values = cobj.get("values")
                raw = cobj.get("raw")
                new_raw = self._coerce_imported_values(target, values, raw)
                if new_raw is None:
                    continue
                self.update_constant(dvle_index, target.index, new_raw)
                updated += 1
        self.parse()                                                                               
        return updated

    def _find_constant_for_import(self, dvle_index: int, cobj: Dict[str, Any]) -> Optional[ShaderConstant]:
        constants = self.dvles[dvle_index].constants
        idx = cobj.get("index")
        if isinstance(idx, int) and 0 <= idx < len(constants):
            return constants[idx]
        name = str(cobj.get("name", "")).strip()
        reg = str(cobj.get("register", "")).strip()
        reg_id = cobj.get("register_id")
        for c in constants:
            if name and c.display_name == name:
                return c
            if reg and c.register_name == reg:
                return c
            if isinstance(reg_id, int) and c.register_id == reg_id:
                return c
        return None

    def _coerce_imported_values(self, c: ShaderConstant, values: Any, raw: Any) -> Optional[List[int]]:
        if isinstance(raw, list) and raw:
            out = []
            for x in raw[:4]:
                if isinstance(x, str) and x.lower().startswith("0x"):
                    out.append(int(x, 16))
                else:
                    out.append(int(x))
            return (out + [0, 0, 0, 0])[:4]
        if not isinstance(values, list):
            return None
        if c.entry_type == 2:
            return [float_to_pica24(float(x)) for x in (values + [0, 0, 0, 0])[:4]]
        if c.entry_type == 0:
            first = values[0] if values else 0
            return [1 if bool(first) else 0, 0, 0, 0]
        return [int(x) & 0xFF for x in (values + [0, 0, 0, 0])[:4]]

    def validation_report(self) -> str:
        lines = []
        issues = self.safety_issues()
        if not issues:
            lines.append("No parse/safety issues found.")
        else:
            for issue in issues:
                lines.append(f"[{issue.level.upper()}] {issue.message}")
        if self.dvlp:
            lines.append("")
            lines.append(f"DVLP: {self.dvlp.opcode_count} opcodes, {self.dvlp.opdesc_count} opdescs, {len(self.dvlp.filenames)} source filename symbols")
        for dvle in self.dvles:
            lines.append(f"DVLE {dvle.index}: {dvle.shader_type_name}, {len(dvle.constants)} constants, {len(dvle.inputs)} inputs, {len(dvle.outputs)} outputs, {len(dvle.labels)} labels")
        maps = self._symbol_maps()
        if maps:
            lines.append("")
            lines.append("User/default register symbol maps:")
            for scope, regs in maps.items():
                if regs:
                    lines.append(f"  {scope}: " + ", ".join(f"{r}={n}" for r, n in sorted(regs.items())))
        return "\n".join(lines)

__all__ = [name for name in globals() if not name.startswith("__")]

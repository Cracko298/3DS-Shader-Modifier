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

DEFAULT_REGISTER_SYMBOLS = {
                                                                                       
}

ASM_CONTROL_COMMENT = "; Full ASM import supports normal instruction lines, labels, .word 0x..., and the existing indexed export format."

def clean_asm_line(line: str) -> str:
    return str(line).split(";", 1)[0].split("#", 1)[0].strip()

def strip_asm_index_prefix(line: str) -> Tuple[Optional[int], str]:
    cleaned = clean_asm_line(line)
    if not cleaned:
        return None, ""
    head, sep, rest = cleaned.partition(":")
    h = head.strip()
    if sep and (h.isdigit() or (h.lower().startswith("0x") and len(h) > 2)):
        return int(h, 0), rest.strip()
    return None, cleaned

def split_asm_args(text: str) -> List[str]:
    return [a.strip() for a in str(text).split(",") if a.strip()]

def parse_condop(text: str) -> int:
    s = str(text).strip().upper()
    for k, v in CONDOP_NAMES.items():
        if s == v.upper():
            return k
    return int(s, 0)

def parse_cmpop(text: str) -> int:
    s = str(text).strip().upper()
    for k, v in CMP_OP_NAMES.items():
        if s == v.upper():
            return k
    return int(s, 0)

def parse_target_token(text: str, labels: Optional[Dict[str, int]] = None) -> int:
    token = str(text).strip()
    if "<" in token and ">" in token:
        token = token.split("<", 1)[0].strip()
    if labels and token in labels:
        return int(labels[token])
    if labels and token.lower() in {k.lower(): v for k, v in labels.items()}:
        lowered = {k.lower(): v for k, v in labels.items()}
        return int(lowered[token.lower()])
    return int(token, 0)

def parse_uniform_token(text: str) -> int:
    s = native_register_from_display(text)
    if s.startswith(("b", "i")) and len(s) > 1:
        return int(s[1:], 0)
    return int(s, 0)

def normalize_asm_register_aliases(line: str, symbol_to_register: Optional[Dict[str, str]] = None) -> str:
    out = str(line)

                                                                                                                                    
    out = re.sub(
        r"(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_.$\[\]]*)\s*\(([vorcib]\d+)\)",
        lambda m: m.group(2).lower(),
        out,
        flags=re.IGNORECASE,
    )

    if not symbol_to_register:
        return out

    def symbol_variants(symbol: str) -> List[str]:
        variants: List[str] = []
        s = str(symbol or "").strip()
        if not s:
            return variants
        variants.append(s)
        us = s.replace(" ", "_")
        if us != s:
            variants.append(us)

                                                                                                    
                                                                                                                           
        stem, component_suffix = split_vector_component_suffix(s)
        if component_suffix and stem and stem != s:
            variants.append(stem)
            stem_us = stem.replace(" ", "_")
            if stem_us != stem:
                variants.append(stem_us)
        return variants

    replacements: List[Tuple[str, str]] = []
    seen: set[Tuple[str, str]] = set()
    for symbol, reg in symbol_to_register.items():
        rg = native_register_from_display(reg)
        if not rg:
            continue
        for sym in symbol_variants(str(symbol)):
            key = (sym.lower(), rg.lower())
            if key not in seen:
                replacements.append((sym, rg))
                seen.add(key)

                                                                         
                                                                                                                    
    for symbol, reg in sorted(replacements, key=lambda kv: len(kv[0]), reverse=True):
        pattern = re.compile(r"(?<![A-Za-z0-9_.$])" + re.escape(symbol) + r"(?![A-Za-z0-9_\[])", re.IGNORECASE)
        out = pattern.sub(reg, out)
    return out

def parse_general_asm_line(line: str, *, base_word: int = 0, default_desc_id: int = 0,
                           labels: Optional[Dict[str, int]] = None,
                           symbol_to_register: Optional[Dict[str, str]] = None) -> Tuple[int, Optional[Dict[str, Any]]]:

    explicit_index, body = strip_asm_index_prefix(line)
    del explicit_index
    body = normalize_asm_register_aliases(body, symbol_to_register)
    if not body:
        raise ValueError("Empty assembly line")
    if body.endswith(":"):
        raise ValueError("Label-only line")
    if body.lower().startswith((".word", "word", "raw")):
        parts = body.replace("=", " ").split()
        if len(parts) < 2:
            raise ValueError("Raw word line needs a value")
        return int(parts[1], 0) & 0xFFFFFFFF, None

    parts = body.replace("\t", " ").split(None, 1)
    mnemonic = parts[0].upper()
    rest = parts[1].strip() if len(parts) > 1 else ""
    if mnemonic not in MNEMONIC_TO_OPCODE:
        raise ValueError(f"Unsupported mnemonic {mnemonic!r}")
    op = MNEMONIC_TO_OPCODE[mnemonic]
    fmt = pica_instruction_format(op, is_word=False)

    if fmt in {"1", "1u", "1i", "5", "5i"}:
        mnem, instr, opdesc = parse_arithmetic_asm_line(body)
        instr["desc_id"] = default_desc_id
        word = pica_build_instruction_word(
            mnem,
            base_word=base_word,
            desc_id=int(instr.get("desc_id", default_desc_id)),
            dst=instr.get("dst", "r0"),
            src1=instr.get("src1", "v0"),
            src2=instr.get("src2", "v0"),
            src3=instr.get("src3", "v0"),
            idx=int(instr.get("idx", 0)),
        )
        return word, opdesc

    args = split_asm_args(rest)
    if fmt == "1c":
                            
        if len(args) != 4:
            raise ValueError("cmp expects: cmp cmpx, cmpy, src1, src2")
        opdesc = {"mask": "xyzw", "src1_swizzle": "xyzw", "src2_swizzle": "xyzw", "src3_swizzle": "xyzw", "src1_neg": False, "src2_neg": False, "src3_neg": False}
        def split_src(arg: str) -> Tuple[str, bool, str]:
            arg = arg.strip()
            neg = arg.startswith("-")
            if neg:
                arg = arg[1:].strip()
            reg, dot, swz = arg.partition(".")
            return reg.strip(), neg, (swz.strip() if dot else "xyzw")
        s1, n1, sw1 = split_src(args[2]); s2, n2, sw2 = split_src(args[3])
        opdesc.update({"src1_swizzle": sw1, "src2_swizzle": sw2, "src1_neg": n1, "src2_neg": n2})
        return pica_build_instruction_word(mnemonic, base_word=base_word, desc_id=default_desc_id,
                                           src1=s1, src2=s2, cmpx=parse_cmpop(args[0]), cmpy=parse_cmpop(args[1])), opdesc

    if fmt == "0":
        return pica_build_instruction_word(mnemonic, base_word=base_word), None

    if fmt == "2":
        target = 0
        num = 0
        condop = 0
        refx = 0
        refy = 0
        if op == 0x23:                                               
            if args:
                condop = parse_condop(args[0].split()[0])
            joined = " ".join(args).replace(",", " ").lower()
        else:
            if len(args) >= 1:
                target = parse_target_token(args[0], labels)
            if len(args) >= 2:
                num = int(args[1], 0)
            if len(args) >= 3:
                condop = parse_condop(args[2].split()[0])
            joined = " ".join(args[2:]).replace(",", " ").lower()
        for tok in joined.split():
            if tok.startswith("x="):
                refx = int(tok.split("=", 1)[1], 0)
            elif tok.startswith("y="):
                refy = int(tok.split("=", 1)[1], 0)
        return pica_build_instruction_word(mnemonic, base_word=base_word, target=target, num=num, condop=condop, refx=refx, refy=refy), None

    if fmt == "3":
                                                    
        if len(args) < 3:
            raise ValueError(f"{mnemonic.lower()} expects: target, num, bN/iN")
        return pica_build_instruction_word(mnemonic, base_word=base_word,
                                           target=parse_target_token(args[0], labels),
                                           num=int(args[1], 0),
                                           uniform_id=parse_uniform_token(args[2])), None

    if fmt == "4":
        vals = {"vtx": 0, "vertex": 0, "prim": 0, "winding": 0}
        for chunk in rest.replace(",", " ").split():
            if "=" in chunk:
                k, v = chunk.split("=", 1)
                vals[k.strip().lower()] = int(v, 0)
        return pica_build_instruction_word(mnemonic, base_word=base_word,
                                           vertex_id=vals.get("vtx", vals.get("vertex", 0)),
                                           prim_emit=vals.get("prim", 0),
                                           winding=vals.get("winding", 0)), None

    raise ValueError(f"Unsupported instruction format {fmt!r} for {mnemonic}")


class PicassoCompileError(ValueError):
    """We can raise this when the assembler cannot compile a VSH source files, I am keeping for future usage."""


OUTPUT_PROPERTY_IDS = {
    "position": 0x00, "pos": 0x00,
    "normalquat": 0x01, "nquat": 0x01,
    "color": 0x02, "clr": 0x02,
    "texcoord0": 0x03, "tcoord0": 0x03, "texture0": 0x03, "tex0": 0x03,
    "texcoord0w": 0x04, "tcoord0w": 0x04,
    "texcoord1": 0x05, "tcoord1": 0x05, "texture1": 0x05, "tex1": 0x05,
    "texcoord2": 0x06, "tcoord2": 0x06, "texture2": 0x06, "tex2": 0x06,
    "view": 0x08,
    "dummy": 0x09,
}

@dataclass
class PicassoUniformEntry:
    name: str
    start: int
    end: int
    kind: str = "generic"

@dataclass
class PicassoConstantEntry:
    entry_type: int
    register_id: int
    values: List[Any]

@dataclass
class PicassoOutputEntry:
    output_type: int
    register_id: int
    mask: int
    unknown: int = 0

@dataclass
class PicassoSourceUnit:
    filename: str
    entrypoint: str = "main"
    nodvle: bool = False
    is_geo_shader: bool = False
    is_merge: bool = False
    input_mask: int = 0
    output_mask: int = 0
    geo_shader_type: int = 0
    geo_shader_fixed_start: int = 0
    geo_shader_variable_num: int = 0
    geo_shader_fixed_num: int = 0
    uniforms: List[PicassoUniformEntry] = field(default_factory=list)
    constants: List[PicassoConstantEntry] = field(default_factory=list)
    outputs: List[PicassoOutputEntry] = field(default_factory=list)
    aliases: Dict[str, str] = field(default_factory=dict)
    entry_start: int = 0
    entry_end: int = 0

def _split_args_balanced(text: str) -> List[str]:
    args: List[str] = []
    cur: List[str] = []
    depth = 0
    for ch in str(text):
        if ch == "(":
            depth += 1
            cur.append(ch)
        elif ch == ")":
            depth = max(0, depth - 1)
            cur.append(ch)
        elif ch == "," and depth == 0:
            arg = "".join(cur).strip()
            if arg:
                args.append(arg)
            cur = []
        else:
            cur.append(ch)
    arg = "".join(cur).strip()
    if arg:
        args.append(arg)
    return args


def _strip_asm_comments(line: str) -> str:
                                                                                                                                                 
    s = str(line)
    s = re.sub(r"/\*.*?\*/", "", s)
    cut = len(s)
    for marker in ("//", ";"):
        idx = s.find(marker)
        if idx >= 0:
            cut = min(cut, idx)
    return s[:cut].strip()


def _reg_base_and_suffix(expr: str) -> Tuple[str, str]:
    base, suffix = split_vector_component_suffix(str(expr).strip())
    return base, suffix


def _register_add_offset(register: str, offset: int) -> str:
    reg = native_register_from_display(register).strip().lower()
    m = re.match(r"^([vorcib])(\d+)$", reg)
    if not m:
        raise PicassoCompileError(f"Cannot index non-register alias {register!r}")
    return f"{m.group(1)}{int(m.group(2), 0) + int(offset)}"


def _combine_picasso_swizzles(alias_swizzle: str, requested_swizzle: str) -> str:
    a = _normalize_pica_components(alias_swizzle or "xyzw", fill_to_four=True)
    r = _normalize_pica_components(requested_swizzle or "xyzw", fill_to_four=True)
    idx = {"x": 0, "y": 1, "z": 2, "w": 3}
    return "".join(a[idx[ch]] for ch in r)


def _src_base_register(src: str) -> str:
    s = str(src).strip()
    if s.startswith("-"):
        s = s[1:].strip()
    s = re.sub(r"\[[^\]]+\]", "", s)
    base, _suffix = split_vector_component_suffix(s)
    return native_register_from_display(base).lower()


def _src_uses_constant(src: str) -> bool:
    return _src_base_register(src).startswith("c")


def _parse_bool_literal(text: str) -> bool:
    s = str(text).strip().lower()
    if s in {"1", "true", "yes", "on"}:
        return True
    if s in {"0", "false", "no", "off"}:
        return False
    raise PicassoCompileError(f"Invalid boolean literal {text!r}")


def _pack_u32(value: int) -> bytes:
    return struct.pack("<I", int(value) & 0xFFFFFFFF)


def _pack_u16(value: int) -> bytes:
    return struct.pack("<H", int(value) & 0xFFFF)


def _pack_u8(value: int) -> bytes:
    return struct.pack("B", int(value) & 0xFF)


def _align4(buf: bytearray) -> None:
    while len(buf) & 3:
        buf.append(0)


class EmbeddedPicassoAssembler:
    def __init__(self, *, auto_nop: bool = True) -> None:
        self.auto_nop = bool(auto_nop)
        self.unit = PicassoSourceUnit(filename="shader.vsh")
        self.output_words: List[int] = []
        self.opdescs: List[Tuple[int, int]] = []
        self.opdesc_lookup: Dict[Tuple[int, int], int] = {}
        self.labels: Dict[str, int] = {}
        self.label_relocs: List[Tuple[int, str]] = []
        self.proc_table: Dict[str, Tuple[int, int]] = {}
        self.proc_relocs: List[Tuple[int, str]] = []
        self.current_proc: Optional[Tuple[str, int]] = None
        self.next_v = 0
        self.next_o = 0
        self.next_c = 0
        self.next_i = 0
        self.next_b = 0
        self._constfa_active: Optional[Dict[str, Any]] = None

    @staticmethod
    def compile_text(source: str, filename: str = "shader.vsh", *, auto_nop: bool = True) -> bytes:
        compiler = EmbeddedPicassoAssembler(auto_nop=auto_nop)
        return compiler.compile(source, filename)

    @staticmethod
    def compile_file(input_path: str, output_path: str, *, auto_nop: bool = True) -> None:
        with open(input_path, "r", encoding="utf-8") as f:
            src = f.read()
        data = EmbeddedPicassoAssembler.compile_text(src, os.path.basename(input_path), auto_nop=auto_nop)
        with open(output_path, "wb") as f:
            f.write(data)

    def compile(self, source: str, filename: str = "shader.vsh") -> bytes:
        self.unit.filename = os.path.basename(filename or "shader.vsh")
        for line_no, raw in enumerate(str(source).splitlines(), start=1):
            try:
                self._process_line(raw, line_no)
            except Exception as exc:
                if isinstance(exc, PicassoCompileError):
                    raise PicassoCompileError(f"{self.unit.filename}:{line_no}: {exc}") from exc
                raise PicassoCompileError(f"{self.unit.filename}:{line_no}: {exc}") from exc

        if self._constfa_active is not None:
            raise PicassoCompileError("unterminated .constfa block; missing .end")
        if self.current_proc is not None:
            name, _start = self.current_proc
            raise PicassoCompileError(f"unterminated .proc {name!r}; missing .end")

        entry = self.unit.entrypoint or "main"
        self._synthesize_label_procedures()
        resolved_entry = self._resolve_proc_name(entry)
        if resolved_entry is None:
            resolved_label = self._resolve_label_name(entry)
            if resolved_label is not None:
                start = int(self.labels[resolved_label])
                end_abs = int(self._find_matching_end_label(resolved_label, len(self.output_words)))
                self.proc_table.setdefault(resolved_label, (start, max(0, end_abs - start)))
                resolved_entry = resolved_label
            elif not self.proc_table:
                self.proc_table[entry] = (0, len(self.output_words))
                resolved_entry = entry

        self._relocate()
        resolved_entry = self._resolve_proc_name(entry) or resolved_entry
        if resolved_entry is None or resolved_entry not in self.proc_table:
            raise PicassoCompileError(f"entrypoint {entry!r} is undefined")
        entry_start, entry_len = self.proc_table[resolved_entry]
        self.unit.entry_start = int(entry_start)
        self.unit.entry_end = int(entry_start) + int(entry_len)
        if self.unit.nodvle:
            raise PicassoCompileError(".nodvle was specified; no DVLE/SHBIN can be generated from this single source")
        return self._build_shbin()

    def _process_line(self, raw: str, line_no: int) -> None:
        line = _strip_asm_comments(raw)
        if not line:
            return
        if line.startswith("#"):
            if line.lower().startswith("#pragma"):
                self._pragma(line)
            return

        low_line = line.lower()
        if low_line.startswith("def ") or low_line.startswith("def,"):
            self._legacy_def_constant(line)
            return

        while True:
            m = re.match(r"^([A-Za-z_][A-Za-z0-9_$]*)\s*:\s*(.*)$", line)
            if not m:
                break
            label = m.group(1)
            self._define_label(label, len(self.output_words))
            line = m.group(2).strip()
            if not line:
                return

        if line.startswith("."):
            self._directive(line)
        else:
            self._instruction(line)

    def _pragma(self, line: str) -> None:
        m = re.match(r"^#\s*pragma\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)\s*$", line, re.IGNORECASE)
        if not m:
            return
        kind = m.group(1).lower()
        args = [a.strip() for a in _split_args_balanced(m.group(2))]
        if kind == "bind_symbol":
            self._pragma_bind_symbol(args)
        elif kind == "output_map":
            self._pragma_output_map(args)

    def _pragma_bind_symbol(self, args: List[str]) -> None:
        if len(args) < 2:
            return
        name_token = args[0].strip()
        name_base, name_suffix = split_vector_component_suffix(name_token)
        reg_start_expr = self._expand_alias_expr(args[1])
        reg_start_base, reg_start_suffix = split_vector_component_suffix(reg_start_expr)
        reg_start = native_register_from_display(reg_start_base)
        if not re.match(r"^[vcibo]\d+$", reg_start, re.IGNORECASE):
            return
        reg_prefix = reg_start[0].lower()
        start_idx = int(reg_start[1:], 0)
        end_idx = start_idx
        if len(args) >= 3:
            reg_end_expr = self._expand_alias_expr(args[2])
            reg_end_base, _reg_end_suffix = split_vector_component_suffix(reg_end_expr)
            reg_end = native_register_from_display(reg_end_base)
            if re.match(rf"^{reg_prefix}\d+$", reg_end, re.IGNORECASE):
                end_idx = int(reg_end[1:], 0)
        lo, hi = sorted((start_idx, end_idx))

        alias_suffix = name_suffix or reg_start_suffix
        alias_expr = f"{reg_prefix}{lo}"
        if alias_suffix:
            alias_expr += "." + _normalize_pica_components(alias_suffix, fill_to_four=True)
        if name_base:
            self.unit.aliases[name_base] = alias_expr

        visible_name = name_token.replace(".", "$")
        if reg_prefix == "v":
            self.unit.input_mask |= sum((1 << i) for i in range(lo, hi + 1)) & 0xFFFF
            self._add_uniform(visible_name, lo, hi, "input")
        elif reg_prefix == "c":
            self._add_uniform(visible_name, 0x10 + lo, 0x10 + hi, "fvec")
        elif reg_prefix == "i":
            self._add_uniform(visible_name, 0x70 + lo, 0x70 + hi, "ivec")
        elif reg_prefix == "b":
            self._add_uniform(visible_name, 0x78 + lo, 0x78 + hi, "bool")

    def _pragma_output_map(self, args: List[str]) -> None:
        if len(args) < 2:
            return
        prop_base, prop_suffix = split_vector_component_suffix(args[0])
        prop_key = prop_base.lower()
        if prop_key not in OUTPUT_PROPERTY_IDS:
            raise PicassoCompileError(f"unknown output property {prop_base!r}")
        reg_expr = self._expand_alias_expr(args[1])
        reg_base, reg_suffix = split_vector_component_suffix(reg_expr)
        reg = native_register_from_display(reg_base)
        if not reg.startswith("o"):
            raise PicassoCompileError("#pragma output_map requires an oN output register")
        mask_s = reg_suffix or prop_suffix or "xyzw"
        mask = parse_dvle_output_mask(mask_s)
        reg_id = int(reg[1:], 0)
        self.unit.outputs.append(PicassoOutputEntry(OUTPUT_PROPERTY_IDS[prop_key], reg_id, mask))
        self.unit.output_mask |= (1 << reg_id) & 0xFFFF

    def _legacy_def_constant(self, line: str) -> None:
                                                                 
        m = re.match(r"^def\s+([^,\s]+)\s*,\s*(.*)$", line, re.IGNORECASE)
        if not m:
            raise PicassoCompileError("def expects: def cN, x, y, z, w")
        reg = _src_base_register(self._expand_alias_expr(m.group(1)))
        vals = _split_args_balanced(m.group(2))
        if len(vals) != 4:
            raise PicassoCompileError("def requires exactly four values")
        if reg.startswith("c"):
            self._add_constant(2, int(reg[1:], 0), [float(v) for v in vals])
        elif reg.startswith("i"):
            self._add_constant(1, int(reg[1:], 0), [int(v, 0) & 0xFF for v in vals])
        elif reg.startswith("b"):
            self._add_constant(0, int(reg[1:], 0), [_parse_bool_literal(vals[0])])
        else:
            raise PicassoCompileError("def only supports cN/iN/bN constants")

    def _directive(self, line: str) -> None:
        parts = line.split(None, 1)
        cmd = parts[0].lower()
        rest = parts[1].strip() if len(parts) > 1 else ""

        if self._constfa_active is not None and cmd != ".end":
            if cmd != ".constfa":
                raise PicassoCompileError("inside .constfa array block, only .constfa (...) values or .end are allowed")
            self._directive_constfa_value(rest)
            return

        if cmd == ".proc":
            if not rest:
                raise PicassoCompileError(".proc needs a procedure name")
            if self.current_proc is not None:
                raise PicassoCompileError("nested .proc blocks are not supported")
            proc_name = rest.split()[0]
            start = len(self.output_words)
            self.current_proc = (proc_name, start)
            self._define_label(proc_name, start, allow_same_address=True)
            return

        if cmd == ".end":
            if self._constfa_active is not None:
                self._finish_constfa()
                return
            if self.current_proc is not None:
                name, start = self.current_proc
                end = len(self.output_words)
                self.proc_table[name] = (start, end - start)
                self._define_label("end" + str(name), end, allow_same_address=True, allow_existing=True)
                self.current_proc = None
                return
            raise PicassoCompileError(".end without an open .proc/.constfa block")

        if cmd == ".entry":
            if not rest:
                raise PicassoCompileError(".entry needs a procedure name")
            self.unit.entrypoint = rest.split()[0]
            return

        if cmd == ".nodvle":
            self.unit.nodvle = True
            return

        if cmd == ".alias":
            toks = rest.split(None, 1)
            if len(toks) != 2:
                raise PicassoCompileError(".alias expects: .alias aliasName register")
            self.unit.aliases[toks[0]] = self._expand_alias_expr(toks[1])
            return

        if cmd == ".in":
            self._directive_in(rest)
            return

        if cmd == ".out":
            self._directive_out(rest)
            return

        if cmd in {".fvec", ".ivec", ".bool"}:
            self._directive_uniform_list(cmd, rest)
            return

        if cmd == ".constf":
            self._directive_const_vector(rest, entry_type=2)
            return

        if cmd == ".consti":
            self._directive_const_vector(rest, entry_type=1)
            return

        if cmd == ".constfa":
            self._directive_constfa_start(rest)
            return

        if cmd == ".setf":
            self._directive_set_vector(rest, entry_type=2)
            return

        if cmd == ".seti":
            self._directive_set_vector(rest, entry_type=1)
            return

        if cmd == ".setb":
            toks = rest.split()
            if len(toks) != 2:
                raise PicassoCompileError(".setb expects: .setb bN value")
            reg = _src_base_register(self._expand_alias_expr(toks[0]))
            if not reg.startswith("b"):
                raise PicassoCompileError(".setb requires a boolean register bN")
            self._add_constant(0, int(reg[1:], 0), [_parse_bool_literal(toks[1])])
            return

        if cmd == ".gsh":
            self._directive_gsh(rest)
            return

        raise PicassoCompileError(f"unsupported directive {cmd!r}")

    def _directive_in(self, rest: str) -> None:
        toks = rest.split()
        if not toks:
            raise PicassoCompileError(".in expects: .in inName [vN]")
        name = toks[0]
        if len(toks) >= 2:
            reg = native_register_from_display(self._expand_alias_expr(toks[1]))
            if not reg.startswith("v"):
                raise PicassoCompileError(".in explicit register must be vN")
            idx = int(reg[1:], 0)
        else:
            idx = self._alloc_v(1)
            reg = f"v{idx}"
        self.unit.aliases[name] = reg
        self._add_uniform(name, idx, idx, "input")
        self.unit.input_mask |= (1 << idx) & 0xFFFF

    def _directive_out(self, rest: str) -> None:
        toks = rest.split()
        if len(toks) < 2:
            raise PicassoCompileError(".out expects: .out outName propName [register]")
        alias_name, prop_token = toks[0], toks[1]
        prop_base, prop_suffix = split_vector_component_suffix(prop_token)
        prop_key = prop_base.lower()
        if prop_key not in OUTPUT_PROPERTY_IDS:
            raise PicassoCompileError(f"unknown output property {prop_base!r}")
        reg_suffix = ""
        if len(toks) >= 3:
            reg_expr = self._expand_alias_expr(toks[2])
            reg_base, reg_suffix = split_vector_component_suffix(reg_expr)
            reg = native_register_from_display(reg_base)
            if not reg.startswith("o"):
                raise PicassoCompileError(".out explicit register must be oN or an output alias")
            reg_id = int(reg[1:], 0)
        else:
            reg_id = self._alloc_o(1)
        mask_s = reg_suffix or prop_suffix or "xyzw"
        mask = parse_dvle_output_mask(mask_s)
        self.unit.outputs.append(PicassoOutputEntry(OUTPUT_PROPERTY_IDS[prop_key], reg_id, mask))
        self.unit.output_mask |= (1 << reg_id) & 0xFFFF
        if alias_name != "-":
            alias_expr = f"o{reg_id}"
            if mask_s and _normalize_pica_components(mask_s, fill_to_four=False) not in {"", "xyzw"}:
                alias_expr += "." + _normalize_pica_components(mask_s, fill_to_four=False)
            self.unit.aliases[alias_name] = alias_expr

    def _directive_uniform_list(self, cmd: str, rest: str) -> None:
        if not rest:
            raise PicassoCompileError(f"{cmd} needs at least one name")
        for item in _split_args_balanced(rest):
            name, size = self._parse_array_name(item)
            if cmd == ".fvec":
                start = self._alloc_c(size)
                self.unit.aliases[name] = f"c{start}"
                self._add_uniform(name, 0x10 + start, 0x10 + start + size - 1, "fvec")
            elif cmd == ".ivec":
                start = self._alloc_i(size)
                self.unit.aliases[name] = f"i{start}"
                self._add_uniform(name, 0x70 + start, 0x70 + start + size - 1, "ivec")
            else:
                start = self._alloc_b(size)
                self.unit.aliases[name] = f"b{start}"
                self._add_uniform(name, 0x78 + start, 0x78 + start + size - 1, "bool")

    def _directive_const_vector(self, rest: str, entry_type: int) -> None:
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_$]*)\s*\((.*)\)\s*$", rest)
        if not m:
            raise PicassoCompileError("constant vector syntax is name(x, y, z, w)")
        name = m.group(1)
        values = self._parse_vector_values(m.group(2), entry_type)
        if entry_type == 2:
            reg = self._alloc_c(1)
            self.unit.aliases[name] = f"c{reg}"
            self._add_uniform(name, 0x10 + reg, 0x10 + reg, "constf")
        else:
            reg = self._alloc_i(1)
            self.unit.aliases[name] = f"i{reg}"
            self._add_uniform(name, 0x70 + reg, 0x70 + reg, "consti")
        self._add_constant(entry_type, reg, values)

    def _directive_constfa_start(self, rest: str) -> None:
        name, size = self._parse_array_name(rest, allow_empty_size=True)
        base = self._alloc_c(max(1, size if size > 0 else 1))
        if size == 0:
            self.next_c = base
        self.unit.aliases[name] = f"c{base}"
        self._constfa_active = {"name": name, "base": base, "declared_size": size, "values": []}

    def _directive_constfa_value(self, rest: str) -> None:
        if self._constfa_active is None:
            raise PicassoCompileError(".constfa value outside array block")
        m = re.match(r"^\((.*)\)\s*$", rest)
        if not m:
            raise PicassoCompileError(".constfa array value must be .constfa (x, y, z, w)")
        self._constfa_active["values"].append(self._parse_vector_values(m.group(1), 2))

    def _finish_constfa(self) -> None:
        assert self._constfa_active is not None
        data = self._constfa_active
        base = int(data["base"])
        vals: List[List[Any]] = list(data["values"])
        declared = int(data["declared_size"])
        if declared > 0:
            while len(vals) < declared:
                vals.append([0.0, 0.0, 0.0, 0.0])
            vals = vals[:declared]
        if declared == 0:
            self.next_c = base + len(vals)
        for i, v in enumerate(vals):
            self._add_constant(2, base + i, v)
        if vals:
            self._add_uniform(str(data["name"]), 0x10 + base, 0x10 + base + len(vals) - 1, "constfa")
        self._constfa_active = None

    def _directive_set_vector(self, rest: str, entry_type: int) -> None:
        m = re.match(r"^([^\(\s]+)\s*\((.*)\)\s*$", rest)
        if not m:
            raise PicassoCompileError(".setf/.seti syntax is register(x, y, z, w)")
        reg_expr = self._expand_alias_expr(m.group(1))
        reg = _src_base_register(reg_expr)
        if entry_type == 2:
            if not reg.startswith("c"):
                raise PicassoCompileError(".setf requires cN")
            reg_id = int(reg[1:], 0)
        else:
            if not reg.startswith("i"):
                raise PicassoCompileError(".seti requires iN")
            reg_id = int(reg[1:], 0)
        self._add_constant(entry_type, reg_id, self._parse_vector_values(m.group(2), entry_type))

    def _directive_gsh(self, rest: str) -> None:
                                                                                                                        
        self.unit.is_geo_shader = True
        toks = rest.split()
        if not toks:
            return
        mode = toks[0].lower()
        if mode == "point":
            self.unit.geo_shader_type = 0
            if len(toks) >= 2:
                reg = _src_base_register(self._expand_alias_expr(toks[1]))
                if reg.startswith("c"):
                    self.next_c = max(self.next_c, int(reg[1:], 0))
        elif mode == "variable":
            self.unit.geo_shader_type = 1
            if len(toks) >= 3:
                self.unit.geo_shader_variable_num = int(toks[2], 0)
        elif mode == "fixed":
            self.unit.geo_shader_type = 2
            if len(toks) >= 4:
                arr = _src_base_register(self._expand_alias_expr(toks[2]))
                if arr.startswith("c"):
                    self.unit.geo_shader_fixed_start = int(arr[1:], 0)
                self.unit.geo_shader_fixed_num = int(toks[3], 0)
        else:
            raise PicassoCompileError(f"unknown .gsh mode {mode!r}")

    def _instruction(self, line: str) -> None:
        expanded = self._expand_aliases_in_line(line)
        expanded = self._normalize_picasso_instruction(expanded)
        if not expanded:
            return
        mnemonic = expanded.split(None, 1)[0].upper()

        if mnemonic == "RET":
                                                                                            
            self.output_words.append(pica_build_instruction_word("NOP"))
            return

        if mnemonic == "CALL":
            args = _split_args_balanced(expanded.split(None, 1)[1] if " " in expanded else "")
            if len(args) != 1:
                raise PicassoCompileError("call expects: call procName")
            idx = len(self.output_words)
            self.output_words.append(pica_build_instruction_word("CALL", target=0, num=0))
            self.proc_relocs.append((idx, args[0]))
            return

        if mnemonic in {"CALLC", "JMPC", "BREAKC", "IFC"}:
            self._conditional_instruction(mnemonic, expanded)
            return

        if mnemonic in {"CALLU", "JMPU", "IFU"}:
            self._bool_flow_instruction(mnemonic, expanded)
            return

        word, opdesc_fields = parse_general_asm_line(expanded, default_desc_id=0, labels=self.labels, symbol_to_register=None)
        if opdesc_fields is not None:
            desc_id = self._find_or_add_opdesc(opdesc_fields)
            op = pica_effective_opcode(word)
            if pica_instruction_format(op, is_word=False) in {"5", "5i"} and desc_id > 31:
                raise PicassoCompileError("MAD/MADI can only address operand descriptors 0..31")
            word, _ = parse_general_asm_line(expanded, default_desc_id=desc_id, labels=self.labels, symbol_to_register=None)
        self.output_words.append(word & 0xFFFFFFFF)

    def _conditional_instruction(self, mnemonic: str, expanded: str) -> None:
        rest = expanded.split(None, 1)[1] if " " in expanded else ""
        args = _split_args_balanced(rest)
        if mnemonic == "BREAKC":
            if len(args) != 1:
                raise PicassoCompileError("breakc expects: breakc condExpr")
            condop, refx, refy = self._parse_cond_expr(args[0])
            self.output_words.append(pica_build_instruction_word("BREAKC", condop=condop, refx=refx, refy=refy))
            return
        if mnemonic == "IFC":
                                                                                    
                                                                                   
            if len(args) >= 3:
                word, _opdesc_fields = parse_general_asm_line(expanded, default_desc_id=0, labels=self.labels, symbol_to_register=None)
                self.output_words.append(word & 0xFFFFFFFF)
                return
            raise PicassoCompileError("ifc block directive assembly is not implemented yet; use raw form like: ifc target, num, x x=1 y=1")
        if len(args) != 2:
            raise PicassoCompileError(f"{mnemonic.lower()} expects two operands")
        condop, refx, refy = self._parse_cond_expr(args[0])
        if mnemonic == "CALLC":
            idx = len(self.output_words)
            self.output_words.append(pica_build_instruction_word("CALLC", target=0, num=0, condop=condop, refx=refx, refy=refy))
            self.proc_relocs.append((idx, args[1]))
        elif mnemonic == "JMPC":
            idx = len(self.output_words)
            resolved = self._resolve_label_name(args[1])
            target = self.labels.get(resolved, 0) if resolved is not None else 0
            self.output_words.append(pica_build_instruction_word("JMPC", target=target, num=0, condop=condop, refx=refx, refy=refy))
            if resolved is None:
                self.label_relocs.append((idx, args[1]))

    def _bool_flow_instruction(self, mnemonic: str, expanded: str) -> None:
        rest = expanded.split(None, 1)[1] if " " in expanded else ""
        args = _split_args_balanced(rest)
        if mnemonic == "IFU":
            raise PicassoCompileError("ifu block directive assembly is not implemented yet; use raw/expanded flow-control form")
        if len(args) != 2:
            raise PicassoCompileError(f"{mnemonic.lower()} expects two operands")
        breg = _src_base_register(args[0].replace("!", ""))
        if not breg.startswith("b"):
            raise PicassoCompileError(f"{mnemonic.lower()} first operand must be bN")
        uniform_id = int(breg[1:], 0)
        idx = len(self.output_words)
        resolved = self._resolve_label_name(args[1])
        self.output_words.append(pica_build_instruction_word(mnemonic, target=self.labels.get(resolved, 0) if resolved is not None else 0, num=0, uniform_id=uniform_id))
        if mnemonic == "CALLU":
            self.proc_relocs.append((idx, args[1]))
        elif resolved is None:
            self.label_relocs.append((idx, args[1]))

    def _normalize_picasso_instruction(self, line: str) -> str:
        parts = line.replace("\t", " ").split(None, 1)
        if not parts:
            return ""
        mnem = parts[0].upper()
        rest = parts[1].strip() if len(parts) > 1 else ""
        args = _split_args_balanced(rest)

        if mnem == "CMP" and len(args) == 4:
                                
                                                        
                                                        
                                                                            
            cmp_ops = {v.upper() for v in CMP_OP_NAMES.values()}
            a0_is_cmp = args[0].strip().upper() in cmp_ops
            a1_is_cmp = args[1].strip().upper() in cmp_ops
            a2_is_cmp = args[2].strip().upper() in cmp_ops
            if (not a0_is_cmp) and a1_is_cmp and a2_is_cmp:
                return f"cmp {args[1]}, {args[2]}, {args[0]}, {args[3]}"

        if mnem == "MOVA" and len(args) == 2:
            dst = args[0].strip().lower()
            if dst in {"a0", "a0.x", "a0x"}:
                return f"mova r0.x, {args[1]}"
            if dst in {"a1", "a0.y", "a0y"}:
                return f"mova r0.y, {args[1]}"
            if dst in {"a01", "a0.xy", "a0xy"}:
                return f"mova r0.xy, {args[1]}"

        invert_map = {"DPH": "DPHI", "DST": "DSTI", "SGE": "SGEI", "SLT": "SLTI"}
        if mnem in invert_map and len(args) == 3 and _src_uses_constant(args[2]) and not _src_uses_constant(args[1]):
            return f"{invert_map[mnem].lower()} {args[0]}, {args[1]}, {args[2]}"

        if mnem == "MAD" and len(args) == 4:
            src2_const = _src_uses_constant(args[2])
            src3_const = _src_uses_constant(args[3])
            if src3_const and not src2_const:
                return f"madi {args[0]}, {args[1]}, {args[2]}, {args[3]}"
            if src2_const and src3_const:
                raise PicassoCompileError("mad cannot use constants in both source 2 and source 3 narrow/wide slots")

        if mnem == "SETEMIT" and args:
            vtx = int(args[0], 0)
            flags = " ".join(args[1:]).lower()
            prim = 1 if any(x in flags.split() for x in ["prim", "primitive"]) else 0
            winding = 1 if any(x in flags.split() for x in ["inv", "invert"]) else 0
            return f"setemit vtx={vtx} prim={prim} winding={winding}"

        return line

    def _expand_alias_expr(self, expr: str) -> str:
        return self._expand_aliases_in_line(expr, whole_expr=True)

    def _expand_aliases_in_line(self, line: str, *, whole_expr: bool = False) -> str:
        aliases = self.unit.aliases
        if not aliases:
            return line
                                                                          
        name_pat = "|".join(re.escape(k) for k in sorted(aliases, key=len, reverse=True))
        if not name_pat:
            return line
        pattern = re.compile(rf"(?<![A-Za-z0-9_$])(?P<name>{name_pat})(?P<idx>\[[^\]]+\])?(?P<suffix>\.[A-Za-z]{{1,4}})?(?![A-Za-z0-9_$])")

        def repl(m: re.Match[str]) -> str:
            name = m.group("name")
            base_expr = aliases.get(name, name)
            base_expr = self._expand_aliases_in_line(base_expr, whole_expr=True) if base_expr != name else base_expr
            base_reg_expr, base_swz = _reg_base_and_suffix(base_expr)
            reg = native_register_from_display(base_reg_expr)
            if not reg:
                reg = base_reg_expr.strip().lower()
            idx_text = m.group("idx")
            if idx_text:
                inner = idx_text[1:-1].strip()
                if re.fullmatch(r"[+-]?(?:0x[0-9A-Fa-f]+|\d+)", inner):
                    reg = _register_add_offset(reg, int(inner, 0))
                else:
                                                                                              
                    raise PicassoCompileError(f"relative alias indexing is not implemented yet: {name}{idx_text}")
            suffix = (m.group("suffix") or "").lstrip(".")
            if base_swz and suffix:
                suffix = _combine_picasso_swizzles(base_swz, suffix)
            elif base_swz:
                suffix = _normalize_pica_components(base_swz, fill_to_four=True)
            elif suffix:
                suffix = _normalize_pica_components(suffix, fill_to_four=True)
            return reg + (("." + suffix) if suffix else "")

        return pattern.sub(repl, line)

    def _parse_cond_expr(self, expr: str) -> Tuple[int, int, int]:
        s = str(expr).strip().lower().replace("cmp.", "")
        s = s.replace("&&", " and ").replace("&", " and ").replace("||", " or ").replace("|", " or ")
        toks = [t for t in s.split() if t]
        if not toks:
            raise PicassoCompileError("empty condition expression")
        condop = 2     
        refx = refy = 0
        def flag(tok: str) -> Tuple[str, int]:
            inv = tok.startswith("!")
            if inv:
                tok = tok[1:]
            if tok not in {"x", "y"}:
                raise PicassoCompileError(f"condition flag must be cmp.x/cmp.y, got {tok!r}")
            return tok, 0 if inv else 1
        if len(toks) == 1:
            f, ref = flag(toks[0])
            if f == "x":
                condop, refx, refy = 2, ref, 0
            else:
                condop, refx, refy = 3, 0, ref
        elif len(toks) == 3:
            f1, r1 = flag(toks[0]); op = toks[1]; f2, r2 = flag(toks[2])
            if {f1, f2} != {"x", "y"}:
                raise PicassoCompileError("two-flag conditions must use one x and one y flag")
            refx = r1 if f1 == "x" else r2
            refy = r1 if f1 == "y" else r2
            condop = 1 if op == "and" else 0
        else:
            raise PicassoCompileError(f"unsupported condition expression {expr!r}")
        return condop, refx, refy

    def _find_or_add_opdesc(self, fields: Dict[str, Any]) -> int:
        desc, flags = pica_encode_opdesc(
            fields.get("mask", "xyzw"),
            fields.get("src1_swizzle", "xyzw"),
            fields.get("src2_swizzle", "xyzw"),
            fields.get("src3_swizzle", "xyzw"),
            bool(fields.get("src1_neg", False)),
            bool(fields.get("src2_neg", False)),
            bool(fields.get("src3_neg", False)),
            preserve_flags=0,
        )
        key = (desc, flags)
        if key in self.opdesc_lookup:
            return self.opdesc_lookup[key]
        if len(self.opdescs) >= 128:
            raise PicassoCompileError("too many operand descriptors; PICA limit is 128")
        idx = len(self.opdescs)
        self.opdescs.append(key)
        self.opdesc_lookup[key] = idx
        return idx

    def _parse_array_name(self, text: str, *, allow_empty_size: bool = False) -> Tuple[str, int]:
        s = str(text).strip()
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_$]*)(?:\[(.*?)\])?$", s)
        if not m:
            raise PicassoCompileError(f"invalid name/array syntax {text!r}")
        name = m.group(1)
        size_s = m.group(2)
        if size_s is None:
            return name, 1
        if size_s == "" and allow_empty_size:
            return name, 0
        return name, int(size_s, 0)

    def _parse_vector_values(self, text: str, entry_type: int) -> List[Any]:
        vals = _split_args_balanced(text)
        if len(vals) != 4:
            raise PicassoCompileError("vector constants require exactly 4 values")
        if entry_type == 2:
            return [float(v) for v in vals]
        return [int(v, 0) & 0xFF for v in vals]

    def _add_uniform(self, name: str, start: int, end: int, kind: str) -> None:
        self.unit.uniforms.append(PicassoUniformEntry(str(name), int(start), int(end), kind))

    def _add_constant(self, entry_type: int, register_id: int, values: List[Any]) -> None:
        self.unit.constants.append(PicassoConstantEntry(entry_type, int(register_id), list(values)))

    def _alloc_v(self, size: int) -> int:
        start = self.next_v; self.next_v += int(size); return start
    def _alloc_o(self, size: int) -> int:
        start = self.next_o; self.next_o += int(size); return start
    def _alloc_c(self, size: int) -> int:
        start = self.next_c; self.next_c += int(size); return start
    def _alloc_i(self, size: int) -> int:
        start = self.next_i; self.next_i += int(size); return start
    def _alloc_b(self, size: int) -> int:
        start = self.next_b; self.next_b += int(size); return start

    def _define_label(self, name: str, address: int, *, allow_same_address: bool = False, allow_existing: bool = False) -> None:
        label = str(name).strip()
        if not label:
            return
        addr = int(address)
        lower_lookup = {str(k).lower(): k for k in self.labels}
        existing_key = lower_lookup.get(label.lower())
        if existing_key is not None:
            existing_addr = int(self.labels[existing_key])
            if allow_existing or (allow_same_address and existing_addr == addr):
                return
            raise PicassoCompileError(f"duplicate label {label!r}")
        self.labels[label] = addr

    def _resolve_label_name(self, name: str) -> Optional[str]:
        token = str(name).strip()
        if token in self.labels:
            return token
        return {str(k).lower(): k for k in self.labels}.get(token.lower())

    def _resolve_proc_name(self, name: str) -> Optional[str]:
        token = str(name).strip()
        if token in self.proc_table:
            return token
        return {str(k).lower(): k for k in self.proc_table}.get(token.lower())

    def _label_lookup_lower(self) -> Dict[str, str]:
        return {str(name).lower(): str(name) for name in self.labels}

    def _find_matching_end_label(self, label: str, default_end: int) -> int:
        lower_lookup = self._label_lookup_lower()
        end_name = lower_lookup.get(("end" + str(label)).lower())
        if end_name is None:
            return int(default_end)
        return int(self.labels.get(end_name, default_end))

    def _synthesize_label_procedures(self) -> None:
                                                           
                                                          
                                                                                 
                                                   
        lower_lookup = self._label_lookup_lower()
        for label, start in list(self.labels.items()):
            if self._is_end_label(label):
                continue
            end_name = lower_lookup.get(("end" + str(label)).lower())
            if end_name is None:
                continue
            end_abs = int(self.labels.get(end_name, len(self.output_words)))
            if end_abs < int(start):
                continue
            self.proc_table.setdefault(str(label), (int(start), max(0, end_abs - int(start))))

    def _is_end_label(self, label: str) -> bool:
        name = str(label)
        if len(name) <= 3 or not name.lower().startswith("end"):
            return False
        lower_lookup = self._label_lookup_lower()
        base_name = lower_lookup.get(name[3:].lower())
        if base_name is None:
            return False
        return int(self.labels.get(name, -1)) >= int(self.labels.get(base_name, 0))

    def _visible_label_entries(self) -> List[Tuple[str, int]]:
        labels: List[Tuple[str, int]] = []
        seen: set[str] = set()
        max_addr = len(self.output_words)
        for name, addr in self.labels.items():
                                                                              
                                                                                  
            if not (0 <= int(addr) <= max_addr):
                continue
            key = str(name).lower()
            if key in seen:
                continue
            labels.append((str(name), int(addr)))
            seen.add(key)
        labels.sort(key=lambda item: (item[1], item[0].lower()))
        if len(labels) > 256:
            raise PicassoCompileError("too many DVLE labels; label table supports at most 256 entries in this writer")
        return labels

    def _relocate(self) -> None:
        for idx, label in self.label_relocs:
            resolved = self._resolve_label_name(label)
            if resolved is None:
                raise PicassoCompileError(f"label {label!r} is undefined")
            self.output_words[idx] = set_bits(self.output_words[idx], 10, 12, self.labels[resolved]) & 0xFFFFFFFF
        for idx, proc_name in self.proc_relocs:
            resolved_proc = self._resolve_proc_name(proc_name)
            if resolved_proc is None:
                raise PicassoCompileError(f"procedure {proc_name!r} is undefined")
            dst, num = self.proc_table[resolved_proc]
            word = self.output_words[idx]
            word &= ~0x3FFFFF
            word |= (int(num) & 0xFF) | ((int(dst) & 0xFFF) << 10)
            self.output_words[idx] = word & 0xFFFFFFFF

    def _symbol_blob_and_offsets(self, unit: PicassoSourceUnit, label_entries: Optional[List[Tuple[str, int]]] = None) -> Tuple[bytes, Dict[str, int]]:
        blob = bytearray()
        offsets: Dict[str, int] = {}

        def add_symbol(name: str) -> None:
            visible = str(name).replace("$", ".")
            if not visible or visible in offsets:
                return
            offsets[visible] = len(blob)
            blob.extend(visible.encode("ascii", errors="replace") + b"\x00")

        for u in unit.uniforms:
            add_symbol(u.name)
        for label_name, _addr in label_entries or []:
            add_symbol(label_name)
        return bytes(blob), offsets

    def _build_shbin(self) -> bytes:
        unit = self.unit
        dvle_count = 1
        prog_size = len(self.output_words)
        dvlp_size = 10 * 4 + prog_size * 4 + len(self.opdescs) * 8
        label_entries = self._visible_label_entries()
        symbol_blob, symbol_offsets = self._symbol_blob_and_offsets(unit, label_entries)
        dvle_size = 16 * 4 + len(unit.constants) * 20 + len(label_entries) * 0x10 + len(unit.outputs) * 8 + len(unit.uniforms) * 8 + len(symbol_blob)
        dvle_size = (dvle_size + 3) & ~3
        dvle_offset = 2 * 4 + dvle_count * 4 + dvlp_size

        out = bytearray()
        out += b"DVLB"
        out += _pack_u32(dvle_count)
        out += _pack_u32(dvle_offset)

        out += b"DVLP"
        out += _pack_u32(0)                   
        out += _pack_u32(10 * 4)
        out += _pack_u32(prog_size)
        out += _pack_u32(10 * 4 + prog_size * 4)
        out += _pack_u32(len(self.opdescs))
        out += _pack_u32(dvlp_size)                                        
        out += _pack_u32(0)                                                               
        out += _pack_u32(0)
        out += _pack_u32(0)
        for word in self.output_words:
            out += _pack_u32(word)
        for desc, flags in self.opdescs:
            out += _pack_u32(desc)
            out += _pack_u32(flags)

        if len(out) != dvle_offset:
            raise PicassoCompileError(f"internal SHBIN layout mismatch: DVLE offset expected 0x{dvle_offset:X}, got 0x{len(out):X}")

        cur = 16 * 4
        const_off = cur; const_count = len(unit.constants); cur += const_count * 20
        label_off = cur; label_count = len(label_entries); cur += label_count * 0x10
        output_off = cur; output_count = len(unit.outputs); cur += output_count * 8
        uniform_off = cur; uniform_count = len(unit.uniforms); cur += uniform_count * 8
        symbol_off = cur; symbol_size = len(symbol_blob)

        out += b"DVLE"
        out += _pack_u16(0x1002)
        out += _pack_u8(1 if unit.is_geo_shader else 0)
        out += _pack_u8(1 if unit.is_merge else 0)
        out += _pack_u32(unit.entry_start)
        out += _pack_u32(unit.entry_end)
        out += _pack_u16(unit.input_mask)
        out += _pack_u16(unit.output_mask)
        out += _pack_u8(unit.geo_shader_type)
        out += _pack_u8(unit.geo_shader_fixed_start)
        out += _pack_u8(unit.geo_shader_variable_num)
        out += _pack_u8(unit.geo_shader_fixed_num)
        out += _pack_u32(const_off)
        out += _pack_u32(const_count)
        out += _pack_u32(label_off)
        out += _pack_u32(label_count)
        out += _pack_u32(output_off)
        out += _pack_u32(output_count)
        out += _pack_u32(uniform_off)
        out += _pack_u32(uniform_count)
        out += _pack_u32(symbol_off)
        out += _pack_u32(symbol_size)

        for c in unit.constants:
            out += _pack_u16(c.entry_type)
            out += _pack_u16(c.register_id)
            if c.entry_type == 2:
                for v in c.values[:4]:
                    out += _pack_u32(float_to_pica24(float(v)))
            elif c.entry_type == 1:
                vals = [(int(v) & 0xFF) for v in c.values[:4]]
                out += bytes(vals)
                out += b"\x00" * 12
            elif c.entry_type == 0:
                out += _pack_u32(1 if c.values and c.values[0] else 0)
                out += b"\x00" * 12
            else:
                out += b"\x00" * 16

        for label_id, (label_name, opcode_address) in enumerate(label_entries):
            out += _pack_u8(label_id)
            out += b"\x00\x00\x00"
            out += _pack_u32(opcode_address)
            out += _pack_u32(0)
            out += _pack_u32(symbol_offsets.get(label_name, 0))

        for o in unit.outputs:
            packed = (int(o.output_type) & 0xFFFF) | ((int(o.register_id) & 0xFFFF) << 16) | ((int(o.mask) & 0xFFFF) << 32) | ((int(o.unknown) & 0xFFFF) << 48)
            out += struct.pack("<Q", packed)

        sp = 0
        for u in unit.uniforms:
            visible = u.name.replace("$", ".")
            off = symbol_offsets.get(visible, sp)
            out += _pack_u32(off)
            out += _pack_u16(u.start)
            out += _pack_u16(u.end)
            sp += len(visible.encode("ascii", errors="replace")) + 1

        out += symbol_blob
        _align4(out)
        return bytes(out)


def compile_vsh_text_to_shbin(source: str, filename: str = "shader.vsh", *, auto_nop: bool = True) -> bytes:
    return EmbeddedPicassoAssembler.compile_text(source, filename, auto_nop=auto_nop)


def compile_vsh_file_to_shbin(input_path: str, output_path: str, *, auto_nop: bool = True) -> None:
    EmbeddedPicassoAssembler.compile_file(input_path, output_path, auto_nop=auto_nop)

__all__ = [name for name in globals() if not name.startswith("__")]

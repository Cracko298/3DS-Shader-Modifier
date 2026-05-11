from __future__ import annotations

import csv
import json
import os
import re
import shutil
import struct
import math
import tkinter as tk
from dataclasses import dataclass, field
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from typing import Any, Dict, Iterable, List, Optional, Tuple

APP_TITLE = "Cracko298's 3DS SHBIN Shader Editor - DVLB/DVLP/DVLE"

# GPU register classes
FLOAT_REG_BASE = 0x10
INT_REG_BASE = 0x70
BOOL_REG_BASE = 0x78

OUTPUT_TYPES = {
    0x00: "result.position",
    0x01: "result.normalquat",
    0x02: "result.color",
    0x03: "result.texcoord0",
    0x04: "result.texcoord0w",
    0x05: "result.texcoord1",
    0x06: "result.texcoord2",
    0x07: "unknown7",
    0x08: "result.view",
}

CONSTANT_TYPE_NAMES = {
    0: "Bool",
    1: "Int",
    2: "Float24",
}

# The PICA200 instruction stream is one 32-bit word per instruction. Most
# register ops also reference an operand descriptor entry which contains the
# destination write mask, source swizzles, and source negation flags.
PICA_OPCODE_NAMES = {
    0x00: "ADD", 0x01: "DP3", 0x02: "DP4", 0x03: "DPH", 0x04: "DST",
    0x05: "EX2", 0x06: "LG2", 0x07: "LITP", 0x08: "MUL", 0x09: "SGE",
    0x0A: "SLT", 0x0B: "FLR", 0x0C: "MAX", 0x0D: "MIN", 0x0E: "RCP",
    0x0F: "RSQ", 0x12: "MOVA", 0x13: "MOV", 0x18: "DPHI", 0x19: "DSTI",
    0x1A: "SGEI", 0x1B: "SLTI", 0x20: "BREAK", 0x21: "NOP", 0x22: "END",
    0x23: "BREAKC", 0x24: "CALL", 0x25: "CALLC", 0x26: "CALLU",
    0x27: "IFU", 0x28: "IFC", 0x29: "LOOP", 0x2A: "EMIT", 0x2B: "SETEMIT",
    0x2C: "JMPC", 0x2D: "JMPU", 0x2E: "CMP", 0x2F: "CMP",
}
for _op in range(0x30, 0x38):
    PICA_OPCODE_NAMES[_op] = "MADI"
for _op in range(0x38, 0x40):
    PICA_OPCODE_NAMES[_op] = "MAD"

MNEMONIC_TO_OPCODE = {
    "ADD": 0x00, "DP3": 0x01, "DP4": 0x02, "DPH": 0x03, "DST": 0x04,
    "EX2": 0x05, "EXP": 0x05, "LG2": 0x06, "LOG": 0x06, "LITP": 0x07, "LIT": 0x07,
    "MUL": 0x08, "SGE": 0x09, "SLT": 0x0A, "FLR": 0x0B, "MAX": 0x0C, "MIN": 0x0D,
    "RCP": 0x0E, "RSQ": 0x0F, "MOVA": 0x12, "MOV": 0x13,
    "DPHI": 0x18, "DSTI": 0x19, "SGEI": 0x1A, "SLTI": 0x1B,
    "BREAK": 0x20, "NOP": 0x21, "END": 0x22, "BREAKC": 0x23, "CALL": 0x24,
    "CALLC": 0x25, "CALLU": 0x26, "IFU": 0x27, "IFC": 0x28, "LOOP": 0x29,
    "EMIT": 0x2A, "SETEMIT": 0x2B, "JMPC": 0x2C, "JMPU": 0x2D, "CMP": 0x2E,
    "MADI": 0x30, "MAD": 0x38,
}

ARITH_TWO_ARG = {0x00, 0x01, 0x02, 0x03, 0x04, 0x08, 0x09, 0x0A, 0x0C, 0x0D}
ARITH_ONE_ARG = {0x05, 0x06, 0x07, 0x0B, 0x0E, 0x0F, 0x12, 0x13}
ARITH_INVERTED = {0x18, 0x19, 0x1A, 0x1B}
TRIVIAL_OPS = {0x20, 0x21, 0x22, 0x2A}
FLOW2_OPS = {0x23, 0x24, 0x25, 0x28, 0x2C}
FLOW3_OPS = {0x26, 0x27, 0x29, 0x2D}

ADDR_REG_NAMES = {0: "", 1: "a0.x", 2: "a0.y", 3: "aL"}
CMP_OP_NAMES = {0: "EQ", 1: "NE", 2: "LT", 3: "LE", 4: "GT", 5: "GE", 6: "ALWAYS6", 7: "ALWAYS7"}
CONDOP_NAMES = {0: "OR", 1: "AND", 2: "X", 3: "Y"}

REGISTER_NAME_RE = re.compile(r"^[vorcib]\d+$", re.IGNORECASE)
REGISTER_DISPLAY_RE = re.compile(r"\(([vorcib]\d+)\)\s*$", re.IGNORECASE)
REGISTER_DISPLAY_ANYWHERE_RE = re.compile(r"\(([vorcib]\d+)\)", re.IGNORECASE)
REGISTER_ANGLE_RE = re.compile(r"<([vorcib]\d+)>", re.IGNORECASE)


VECTOR_COMPONENT_SUFFIX_RE = re.compile(r"^(?P<base>.+)\.(?P<components>[xyzw]{1,4})$", re.IGNORECASE)


def split_vector_component_suffix(text: str) -> Tuple[str, str]:
    s = str(text or "").strip()
    m = VECTOR_COMPONENT_SUFFIX_RE.match(s)
    if not m:
        return s, ""
    return m.group("base"), m.group("components").lower()


def append_register_selector_for_display(base: str, selector: str) -> str:
    b = str(base or "").strip()
    sel = str(selector or "").strip().lower()
    if not b or not sel or sel in {"-", "xyzw"}:
        return b
    # Native registers do not contain a symbol suffix, so keep normal behavior ^_^
    if REGISTER_NAME_RE.match(b):
        return f"{b}.{sel}"
    stem, existing_components = split_vector_component_suffix(b)
    if existing_components:
        b = stem
    return f"{b}.{sel}"


def strip_register_display_token(text: str) -> str:
    s = str(text).strip()
    if not s:
        return s
    m = REGISTER_DISPLAY_RE.search(s)
    if m:
        return m.group(1).lower()
    m = REGISTER_ANGLE_RE.search(s)
    if m:
        return m.group(1).lower()

    m = REGISTER_DISPLAY_ANYWHERE_RE.search(s)
    if m:
        suffix = s[m.end():].strip()
        return (m.group(1).lower() + suffix).strip()
    # Also accept forms like 'c17 = CHUNK_ORIGIN' or 'c17 | CHUNK_ORIGIN'.
    head = re.split(r"\s*(?:=|\||:|-)\s*", s, maxsplit=1)[0].strip()
    if REGISTER_NAME_RE.match(head):
        return head.lower()
    return s

def native_register_from_display(text: str) -> str:
    return strip_register_display_token(text).strip().lower()

def get_bits(value: int, shift: int, count: int) -> int:
    return (int(value) >> shift) & ((1 << count) - 1)

def set_bits(value: int, shift: int, count: int, field_value: int) -> int:
    mask = ((1 << count) - 1) << shift
    return (int(value) & ~mask) | ((int(field_value) & ((1 << count) - 1)) << shift)

def pica_effective_opcode(word: int) -> int:
    raw = get_bits(word, 26, 6)
    if (raw & ~0x7) == 0x38:
        return 0x38
    if (raw & ~0x7) == 0x30:
        return 0x30
    if (raw & ~0x1) == 0x2E:
        return 0x2E
    return raw

def pica_opcode_name(word_or_opcode: int, is_word: bool = True) -> str:
    op = pica_effective_opcode(word_or_opcode) if is_word else int(word_or_opcode)
    return PICA_OPCODE_NAMES.get(op, f"UNK_{op:02X}")

def pica_instruction_format(word_or_opcode: int, is_word: bool = True) -> str:
    op = pica_effective_opcode(word_or_opcode) if is_word else int(word_or_opcode)
    if op in ARITH_TWO_ARG or op in ARITH_ONE_ARG or op in ARITH_INVERTED:
        return "1i" if op in ARITH_INVERTED else ("1u" if op in ARITH_ONE_ARG else "1")
    if op == 0x2E:
        return "1c"
    if op in TRIVIAL_OPS:
        return "0"
    if op in FLOW2_OPS:
        return "2"
    if op in FLOW3_OPS:
        return "3"
    if op == 0x2B:
        return "4"
    if op == 0x30:
        return "5i"
    if op == 0x38:
        return "5"
    return "unknown"

def pica_dest_reg_name(raw: int) -> str:
    raw &= 0x1F
    if raw < 0x10:
        return f"o{raw}"
    return f"r{raw - 0x10}"

def pica_src_reg_name(raw: int) -> str:
    raw &= 0x7F
    if raw < 0x10:
        return f"v{raw}"
    if raw < 0x20:
        return f"r{raw - 0x10}"
    return f"c{raw - 0x20}"

def parse_pica_dest_reg(text: str) -> int:
    s = native_register_from_display(text)
    if not s:
        return 0
    if s.startswith("0x") or s.isdigit():
        return int(s, 0) & 0x1F
    prefix, number = s[0], int(s[1:], 0)
    if prefix == "o":
        return number & 0x1F
    if prefix == "r":
        return (0x10 + number) & 0x1F
    raise ValueError(f"Destination register must be oN/rN or a raw number, got {text!r}")

def parse_pica_src_reg(text: str) -> int:
    s = native_register_from_display(text)
    if not s:
        return 0
    if s.startswith("0x") or s.isdigit():
        return int(s, 0) & 0x7F
    prefix, number = s[0], int(s[1:], 0)
    if prefix == "v":
        return number & 0x7F
    if prefix == "r":
        return (0x10 + number) & 0x7F
    if prefix == "c":
        return (0x20 + number) & 0x7F
    raise ValueError(f"Source register must be vN/rN/cN or a raw number, got {text!r}")

def parse_pica_src_reg5(text: str) -> int:
    raw = parse_pica_src_reg(text)
    if raw >= 0x20:
        raise ValueError(f"This source slot is 5-bit and only supports vN/rN, not constants: {text!r}")
    return raw & 0x1F

def pica_dest_mask_to_string(mask: int) -> str:
    letters = "xyzw"
    bits = [0x8, 0x4, 0x2, 0x1]
    out = "".join(ch for ch, bit in zip(letters, bits) if mask & bit)
    return out or "-"

def parse_pica_dest_mask(text: str) -> int:
    s = str(text).strip().lower().replace(".", "")
    if not s or s == "-":
        return 0
    if s.startswith("0x") or s.isdigit():
        return int(s, 0) & 0xF
    mask = 0
    for ch in s:
        if ch == "x": mask |= 0x8
        elif ch == "y": mask |= 0x4
        elif ch == "z": mask |= 0x2
        elif ch == "w": mask |= 0x1
        elif ch in "_, ": pass
        else: raise ValueError(f"Invalid mask component {ch!r}; use xyzw")
    return mask & 0xF

def pica_swizzle_to_string(selector: int) -> str:
    letters = "xyzw"
    selector &= 0xFF
    return "".join(letters[(selector >> (6 - i * 2)) & 3] for i in range(4))

def parse_pica_swizzle(text: str) -> int:
    s = str(text).strip().lower().replace(".", "")
    if not s:
        s = "xyzw"
    if s.startswith("0x") or s.isdigit():
        return int(s, 0) & 0xFF
    if len(s) == 1 and s in "xyzw":
        s *= 4
    if len(s) != 4 or any(ch not in "xyzw" for ch in s):
        raise ValueError(f"Swizzle must be xyzw, xxxx, yzxw, etc.; got {text!r}")
    val = 0
    for i, ch in enumerate(s):
        val |= "xyzw".index(ch) << (6 - i * 2)
    return val & 0xFF

def pica_decode_opdesc(desc: int, flags: int = 0) -> Dict[str, Any]:
    return {
        "raw": desc & 0xFFFFFFFF,
        "flags": flags & 0xFFFFFFFF,
        "dest_mask_raw": get_bits(desc, 0, 4),
        "dest_mask": pica_dest_mask_to_string(get_bits(desc, 0, 4)),
        "src1_neg": bool(get_bits(desc, 4, 1)),
        "src1_swizzle_raw": get_bits(desc, 5, 8),
        "src1_swizzle": pica_swizzle_to_string(get_bits(desc, 5, 8)),
        "src2_neg": bool(get_bits(desc, 13, 1)),
        "src2_swizzle_raw": get_bits(desc, 14, 8),
        "src2_swizzle": pica_swizzle_to_string(get_bits(desc, 14, 8)),
        "src3_neg": bool(get_bits(desc, 22, 1)),
        "src3_swizzle_raw": get_bits(desc, 23, 8),
        "src3_swizzle": pica_swizzle_to_string(get_bits(desc, 23, 8)),
    }

def pica_encode_opdesc(mask: str, src1_swizzle: str, src2_swizzle: str, src3_swizzle: str,
                       src1_neg: bool = False, src2_neg: bool = False, src3_neg: bool = False,
                       preserve_flags: int = 0) -> Tuple[int, int]:
    desc = 0
    desc = set_bits(desc, 0, 4, parse_pica_dest_mask(mask))
    desc = set_bits(desc, 4, 1, 1 if src1_neg else 0)
    desc = set_bits(desc, 5, 8, parse_pica_swizzle(src1_swizzle))
    desc = set_bits(desc, 13, 1, 1 if src2_neg else 0)
    desc = set_bits(desc, 14, 8, parse_pica_swizzle(src2_swizzle))
    desc = set_bits(desc, 22, 1, 1 if src3_neg else 0)
    desc = set_bits(desc, 23, 8, parse_pica_swizzle(src3_swizzle))
    return desc & 0xFFFFFFFF, preserve_flags & 0xFFFFFFFF

def _signed_src(name: str, neg: bool, swizzle: str) -> str:
    return ("-" if neg else "") + name + (f".{swizzle}" if swizzle and swizzle != "xyzw" else "")

def pica_disassemble_word(index: int, word: int, opdescs: List[Tuple[int, int]]) -> str:
    fields = pica_decode_instruction_fields(index, word, opdescs)
    return fields.get("disasm", f".word 0x{word:08X}")

def pica_decode_instruction_fields(index: int, word: int, opdescs: List[Tuple[int, int]]) -> Dict[str, Any]:
    op = pica_effective_opcode(word)
    raw_opcode = get_bits(word, 26, 6)
    fmt = pica_instruction_format(op, is_word=False)
    name = PICA_OPCODE_NAMES.get(op, f"UNK_{op:02X}")
    out: Dict[str, Any] = {"index": index, "word": word & 0xFFFFFFFF, "raw_opcode": raw_opcode, "opcode": op, "mnemonic": name, "format": fmt}

    def desc_by_id(desc_id: int) -> Dict[str, Any]:
        if 0 <= desc_id < len(opdescs):
            return pica_decode_opdesc(opdescs[desc_id][0], opdescs[desc_id][1])
        d = pica_decode_opdesc(0x01B01B0F, 0)  # safe default xyzw/no neg/full mask
        d["missing"] = True
        return d

    if fmt in {"1", "1u", "1i"}:
        desc_id = get_bits(word, 0, 7)
        desc = desc_by_id(desc_id)
        inverted = op in ARITH_INVERTED
        if inverted:
            src2_raw = get_bits(word, 7, 7)
            src1_raw = get_bits(word, 14, 5)
        else:
            src2_raw = get_bits(word, 7, 5)
            src1_raw = get_bits(word, 12, 7)
        idx = get_bits(word, 19, 2)
        dst_raw = get_bits(word, 21, 5)
        out.update({
            "desc_id": desc_id,
            "dst_raw": dst_raw,
            "dst": pica_dest_reg_name(dst_raw),
            "src1_raw": src1_raw,
            "src1": pica_src_reg_name(src1_raw),
            "src2_raw": src2_raw,
            "src2": pica_src_reg_name(src2_raw),
            "idx": idx,
            "idx_name": ADDR_REG_NAMES.get(idx, "?"),
            "opdesc": desc,
        })
        dst = pica_dest_reg_name(dst_raw)
        mask = desc["dest_mask"]
        if mask != "-" and mask != "xyzw":
            dst += "." + mask
        s1 = _signed_src(pica_src_reg_name(src1_raw), desc["src1_neg"], desc["src1_swizzle"])
        if idx:
            s1 += f"[{ADDR_REG_NAMES.get(idx, '?')}]"
        if op in ARITH_ONE_ARG:
            out["disasm"] = f"{name.lower()} {dst}, {s1}"
        else:
            s2 = _signed_src(pica_src_reg_name(src2_raw), desc["src2_neg"], desc["src2_swizzle"])
            out["disasm"] = f"{name.lower()} {dst}, {s1}, {s2}"
        return out

    if fmt == "1c":
        desc_id = get_bits(word, 0, 7)
        desc = desc_by_id(desc_id)
        src2_raw = get_bits(word, 7, 5)
        src1_raw = get_bits(word, 12, 7)
        idx = get_bits(word, 19, 2)
        cmpy = get_bits(word, 21, 3)
        cmpx = get_bits(word, 24, 3)
        out.update({
            "desc_id": desc_id, "src1_raw": src1_raw, "src1": pica_src_reg_name(src1_raw),
            "src2_raw": src2_raw, "src2": pica_src_reg_name(src2_raw), "idx": idx,
            "idx_name": ADDR_REG_NAMES.get(idx, "?"), "cmpx": cmpx, "cmpy": cmpy,
            "cmpx_name": CMP_OP_NAMES.get(cmpx, str(cmpx)), "cmpy_name": CMP_OP_NAMES.get(cmpy, str(cmpy)),
            "opdesc": desc,
        })
        s1 = _signed_src(pica_src_reg_name(src1_raw), desc["src1_neg"], desc["src1_swizzle"])
        s2 = _signed_src(pica_src_reg_name(src2_raw), desc["src2_neg"], desc["src2_swizzle"])
        out["disasm"] = f"cmp {CMP_OP_NAMES.get(cmpx, cmpx).lower()}, {CMP_OP_NAMES.get(cmpy, cmpy).lower()}, {s1}, {s2}"
        return out

    if fmt == "0":
        out["disasm"] = name.lower()
        return out

    if fmt == "2":
        num = get_bits(word, 0, 8)
        target = get_bits(word, 10, 12)
        condop = get_bits(word, 22, 2)
        refy = get_bits(word, 24, 1)
        refx = get_bits(word, 25, 1)
        out.update({"num": num, "target": target, "condop": condop, "condop_name": CONDOP_NAMES.get(condop, str(condop)), "refx": refx, "refy": refy})
        if op in {0x24}:
            out["disasm"] = f"{name.lower()} {target}, {num}"
        elif op in {0x23}:
            out["disasm"] = f"{name.lower()} {CONDOP_NAMES.get(condop, condop).lower()} x={refx} y={refy}"
        else:
            out["disasm"] = f"{name.lower()} {target}, {num}, {CONDOP_NAMES.get(condop, condop).lower()} x={refx} y={refy}"
        return out

    if fmt == "3":
        num = get_bits(word, 0, 8)
        target = get_bits(word, 10, 12)
        uniform_id = get_bits(word, 22, 4)
        out.update({"num": num, "target": target, "uniform_id": uniform_id})
        prefix = "i" if op == 0x29 else "b"
        out["disasm"] = f"{name.lower()} {target}, {num}, {prefix}{uniform_id}"
        return out

    if fmt == "4":
        winding = get_bits(word, 22, 1)
        prim_emit = get_bits(word, 23, 1)
        vertex_id = get_bits(word, 24, 2)
        out.update({"winding": winding, "prim_emit": prim_emit, "vertex_id": vertex_id})
        out["disasm"] = f"setemit vtx={vertex_id} prim={prim_emit} winding={winding}"
        return out

    if fmt in {"5", "5i"}:
        desc_id = get_bits(word, 0, 5)
        desc = desc_by_id(desc_id)
        inverted = fmt == "5i"
        if inverted:
            src3_raw = get_bits(word, 5, 7)
            src2_raw = get_bits(word, 12, 5)
        else:
            src3_raw = get_bits(word, 5, 5)
            src2_raw = get_bits(word, 10, 7)
        src1_raw = get_bits(word, 17, 5)
        idx = get_bits(word, 22, 2)
        dst_raw = get_bits(word, 24, 5)
        out.update({
            "desc_id": desc_id, "dst_raw": dst_raw, "dst": pica_dest_reg_name(dst_raw),
            "src1_raw": src1_raw, "src1": pica_src_reg_name(src1_raw),
            "src2_raw": src2_raw, "src2": pica_src_reg_name(src2_raw),
            "src3_raw": src3_raw, "src3": pica_src_reg_name(src3_raw),
            "idx": idx, "idx_name": ADDR_REG_NAMES.get(idx, "?"), "opdesc": desc,
        })
        dst = pica_dest_reg_name(dst_raw)
        mask = desc["dest_mask"]
        if mask != "-" and mask != "xyzw":
            dst += "." + mask
        s1 = _signed_src(pica_src_reg_name(src1_raw), desc["src1_neg"], desc["src1_swizzle"])
        s2 = _signed_src(pica_src_reg_name(src2_raw), desc["src2_neg"], desc["src2_swizzle"])
        s3 = _signed_src(pica_src_reg_name(src3_raw), desc["src3_neg"], desc["src3_swizzle"])
        if idx:
            if inverted:
                s3 += f"[{ADDR_REG_NAMES.get(idx, '?')}]"
            else:
                s2 += f"[{ADDR_REG_NAMES.get(idx, '?')}]"
        out["disasm"] = f"{name.lower()} {dst}, {s1}, {s2}, {s3}"
        return out

    out["disasm"] = f".word 0x{word:08X} ; unknown opcode 0x{raw_opcode:02X}"
    return out

def pica_build_instruction_word(mnemonic: str, *, base_word: int = 0, desc_id: int = 0, dst: str = "r0",
                                src1: str = "v0", src2: str = "v0", src3: str = "v0", idx: int = 0,
                                num: int = 0, target: int = 0, condop: int = 0, refx: int = 0, refy: int = 0,
                                uniform_id: int = 0, winding: int = 0, prim_emit: int = 0, vertex_id: int = 0,
                                cmpx: int = 0, cmpy: int = 0) -> int:
    op = MNEMONIC_TO_OPCODE.get(str(mnemonic).strip().upper())
    if op is None:
        raise ValueError(f"Unknown mnemonic {mnemonic!r}")
    word = int(base_word) & 0xFFFFFFFF
    fmt = pica_instruction_format(op, is_word=False)

    if fmt in {"1", "1u", "1i"}:
        word = set_bits(word, 26, 6, op)
        word = set_bits(word, 0, 7, int(desc_id))
        word = set_bits(word, 19, 2, int(idx))
        word = set_bits(word, 21, 5, parse_pica_dest_reg(dst))
        if fmt == "1i":
            word = set_bits(word, 7, 7, parse_pica_src_reg(src2))
            word = set_bits(word, 14, 5, parse_pica_src_reg5(src1))
        else:
            word = set_bits(word, 7, 5, parse_pica_src_reg5(src2))
            word = set_bits(word, 12, 7, parse_pica_src_reg(src1))
        return word & 0xFFFFFFFF

    if fmt == "1c":
        word = set_bits(word, 27, 5, 0x17)  # CMP's actual opcode field. bit 26 belongs to cmpx.
        word = set_bits(word, 0, 7, int(desc_id))
        word = set_bits(word, 7, 5, parse_pica_src_reg5(src2))
        word = set_bits(word, 12, 7, parse_pica_src_reg(src1))
        word = set_bits(word, 19, 2, int(idx))
        word = set_bits(word, 21, 3, int(cmpy))
        word = set_bits(word, 24, 3, int(cmpx))
        return word & 0xFFFFFFFF

    if fmt == "0":
        word = set_bits(word, 26, 6, op)
        return word & 0xFFFFFFFF

    if fmt == "2":
        word = set_bits(word, 26, 6, op)
        word = set_bits(word, 0, 8, int(num))
        word = set_bits(word, 10, 12, int(target))
        word = set_bits(word, 22, 2, int(condop))
        word = set_bits(word, 24, 1, int(refy))
        word = set_bits(word, 25, 1, int(refx))
        return word & 0xFFFFFFFF

    if fmt == "3":
        word = set_bits(word, 26, 6, op)
        word = set_bits(word, 0, 8, int(num))
        word = set_bits(word, 10, 12, int(target))
        word = set_bits(word, 22, 4, int(uniform_id))
        return word & 0xFFFFFFFF

    if fmt == "4":
        word = set_bits(word, 26, 6, op)
        word = set_bits(word, 22, 1, int(winding))
        word = set_bits(word, 23, 1, int(prim_emit))
        word = set_bits(word, 24, 2, int(vertex_id))
        return word & 0xFFFFFFFF

    if fmt in {"5", "5i"}:
        word = set_bits(word, 29, 3, 0x6 if fmt == "5i" else 0x7)
        word = set_bits(word, 0, 5, int(desc_id))
        word = set_bits(word, 17, 5, parse_pica_src_reg5(src1))
        word = set_bits(word, 22, 2, int(idx))
        word = set_bits(word, 24, 5, parse_pica_dest_reg(dst))
        if fmt == "5i":
            word = set_bits(word, 5, 7, parse_pica_src_reg(src3))
            word = set_bits(word, 12, 5, parse_pica_src_reg5(src2))
        else:
            word = set_bits(word, 5, 5, parse_pica_src_reg5(src3))
            word = set_bits(word, 10, 7, parse_pica_src_reg(src2))
        return word & 0xFFFFFFFF

    word = set_bits(word, 26, 6, op)
    return word & 0xFFFFFFFF

def parse_arithmetic_asm_line(line: str) -> Tuple[str, Dict[str, Any], Dict[str, Any]]:
    cleaned = line.split(";", 1)[0].split("#", 1)[0].strip()
    if not cleaned:
        raise ValueError("Empty assembly line")
    parts = cleaned.replace("\t", " ").split(None, 1)
    mnemonic = parts[0].upper()
    if mnemonic not in MNEMONIC_TO_OPCODE:
        raise ValueError(f"Unsupported mnemonic {mnemonic!r}")
    args = [] if len(parts) == 1 else [a.strip() for a in parts[1].split(",")]

    def split_dst(arg: str) -> Tuple[str, str]:
        reg, dot, mask = arg.partition(".")
        return reg.strip(), (mask.strip() if dot else "xyzw")

    def split_src(arg: str) -> Tuple[str, bool, str]:
        arg = arg.strip()
        neg = arg.startswith("-")
        if neg:
            arg = arg[1:].strip()
        reg, dot, swz = arg.partition(".")
        return reg.strip(), neg, (swz.strip() if dot else "xyzw")

    op = MNEMONIC_TO_OPCODE[mnemonic]
    fmt = pica_instruction_format(op, is_word=False)
    instr: Dict[str, Any] = {"mnemonic": mnemonic, "desc_id": 0, "idx": 0}
    opdesc: Dict[str, Any] = {"mask": "xyzw", "src1_swizzle": "xyzw", "src2_swizzle": "xyzw", "src3_swizzle": "xyzw", "src1_neg": False, "src2_neg": False, "src3_neg": False}

    if fmt in {"1", "1i"}:
        if len(args) != 3:
            raise ValueError(f"{mnemonic.lower()} expects: dst, src1, src2")
        dst, mask = split_dst(args[0]); s1, n1, sw1 = split_src(args[1]); s2, n2, sw2 = split_src(args[2])
        instr.update({"dst": dst, "src1": s1, "src2": s2})
        opdesc.update({"mask": mask, "src1_swizzle": sw1, "src2_swizzle": sw2, "src1_neg": n1, "src2_neg": n2})
    elif fmt == "1u":
        if len(args) != 2:
            raise ValueError(f"{mnemonic.lower()} expects: dst, src")
        dst, mask = split_dst(args[0]); s1, n1, sw1 = split_src(args[1])
        instr.update({"dst": dst, "src1": s1, "src2": "v0"})
        opdesc.update({"mask": mask, "src1_swizzle": sw1, "src1_neg": n1})
    elif fmt in {"5", "5i"}:
        if len(args) != 4:
            raise ValueError(f"{mnemonic.lower()} expects: dst, src1, src2, src3")
        dst, mask = split_dst(args[0]); s1, n1, sw1 = split_src(args[1]); s2, n2, sw2 = split_src(args[2]); s3, n3, sw3 = split_src(args[3])
        instr.update({"dst": dst, "src1": s1, "src2": s2, "src3": s3})
        opdesc.update({"mask": mask, "src1_swizzle": sw1, "src2_swizzle": sw2, "src3_swizzle": sw3, "src1_neg": n1, "src2_neg": n2, "src3_neg": n3})
    else:
        raise ValueError("Simple ASM parser supports arithmetic instructions only. Use field/raw editing for flow-control.")
    return mnemonic, instr, opdesc



DEFAULT_REGISTER_SYMBOLS = {
    # Keep empty, honestly this is just from tests and I dont wanna break anything tbf-
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

    # keeps the suffixes such as swizzles/masks intact: 'Name (c17).xy' -> 'c17.xy' :/ I forgot todo this, and it'd break shaders...
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

        # Real DVLE input names 'can' already include display components, but idk. QoL just in case 
        # e.g. bTexCoord.xy. Also allow the base symbol so bTexCoord.xyzz can become vN.xyzz instead of bTexCoord.xy.xyzz. 
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

    # Replace longest names first so CHUNK_ORIGIN does not partly replace
    # CHUNK_ORIGIN_AND_SCALE. A dot after the symbol is allowed because it could maybe the instruction mask/swizzle?
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
        # cmp eq, lt, v0, c0
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
        if op == 0x23:  # BREAKC has no target in its displayed form.
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
        # ifu target, num, b0 | loop target, num, i0
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

def float_to_pica24(value: float) -> int:
    # Converts Python Float32 values to  PICA200 24-bit Floats. I hated this math ngl...
    if value == 0:
        return 0
    try:
        packed = struct.pack("<f", float(value))
        raw = struct.unpack("<I", packed)[0]
    except (OverflowError, ValueError):
        return 0

    sign = (raw >> 31) & 1
    exp = (raw >> 23) & 0xFF
    mant = raw & 0x7FFFFF
    new_exp = exp - 127 + 63

    if new_exp <= 0:
        return 0
    if new_exp >= 0x7F:
        new_exp = 0x7F

    new_mant = mant >> 7
    return ((sign << 23) | (new_exp << 16) | new_mant) & 0xFFFFFF

def pica24_to_float(value: int) -> float:
    value &= 0xFFFFFF
    if value == 0:
        return 0.0

    sign = (value >> 23) & 1
    exp = (value >> 16) & 0x7F
    mant = value & 0xFFFF
    new_exp = exp - 63 + 127
    new_mant = mant << 7
    raw = ((sign << 31) | (new_exp << 23) | new_mant) & 0xFFFFFFFF
    return struct.unpack("<f", struct.pack("<I", raw))[0]

def component_mask(mask: int) -> str:
    letters = "xyzw"
    result = "".join(letters[i] for i in range(4) if mask & (1 << i))
    return result or "-"

def hexdump(data: bytes | bytearray, start: int = 0, size: int = 0x80) -> str:
    if not data:
        return ""
    start = max(0, min(start, len(data)))
    end = min(len(data), start + max(0, size))
    lines = []
    for off in range(start, end, 16):
        chunk = data[off:off + 16]
        hex_part = " ".join(f"{b:02X}" for b in chunk)
        ascii_part = "".join(chr(b) if 32 <= b <= 126 else "." for b in chunk)
        lines.append(f"{off:08X}  {hex_part:<47}  {ascii_part}")
    return "\n".join(lines)

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
        # Do not re-inject defaults after the user deletes/clears aliases/names. Updated since last :/
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
        # Validate the register syntax enough to avoid typos. This does not create new PICA registers;
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
            # 5-bit source fields only encode vN/rN. Constants require a 7-bit source slot.
            regs.extend(f"v{i}" for i in range(16))
            regs.extend(f"r{i}" for i in range(16))
        else:
            # 7-bit source fields encode vN/rN/cN.
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
            for inst in self.dvlp.instructions:
                for lab in inst.fields.get("labels_here", []):
                    name = str(lab.get("name") or f"label_{lab.get('opcode_address', inst.index)}").replace(" ", "_")
                    f.write(f"{name}:\n")
                ann = inst.fields.get("annotated_disasm", inst.disasm)
                ann = str(ann)
                desc = inst.fields.get("desc_id")
                desc_comment = f" desc_id={desc}" if desc is not None else ""
                f.write(f"{inst.index:04d}: {ann:<58} ; word=0x{inst.word:08X}{desc_comment}\n")

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
        # Include per-DVLE alias names too; duplicate names prefer the first seen register.
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
        self.parse()  # Refresh the parsed views after editting assembly. Also forgot this... lmfao
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


class ShaderPreview3D(ttk.LabelFrame):
    SUPPORTED_OPS = {
        "ADD", "MUL", "MAD", "MADI", "MOV", "DP3", "DP4", "DPH", "MIN", "MAX",
        "RCP", "RSQ", "FLR", "EX2", "LG2", "SGE", "SLT", "DST", "MOVA",
    }

    def __init__(self, master: tk.Misc) -> None:
        super().__init__(master, text="Live 3D Shader Preview", padding=4)
        self.parser: Optional[SHBINParser] = None
        self.current_dvle_index: Optional[int] = None
        self.selected_instruction: Optional[int] = None
        self.yaw = -0.65
        self.pitch = 0.35
        self.zoom = 260.0
        self._drag_last: Optional[Tuple[int, int]] = None
        self._last_render_note = "Open a shader to preview it."

        self.mesh_var = tk.StringVar(value="Cube")
        self.material_var = tk.StringVar(value="Preview")
        self.shader_var = tk.StringVar(value="")
        self.autorotate_var = tk.BooleanVar(value=False)
        self.wire_var = tk.BooleanVar(value=True)
        self.light_enabled_var = tk.BooleanVar(value=True)
        self.light_x_var = tk.DoubleVar(value=2.2)
        self.light_y_var = tk.DoubleVar(value=2.8)
        self.light_z_var = tk.DoubleVar(value=-2.4)
        self.light_power_var = tk.DoubleVar(value=1.65)
        self.ambient_var = tk.DoubleVar(value=0.45)

        controls = ttk.Frame(self)
        controls.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        controls.columnconfigure(1, weight=1)
        controls.columnconfigure(3, weight=1)
        ttk.Label(controls, text="Shader:").grid(row=0, column=0, sticky="w")
        self.shader_combo = ttk.Combobox(controls, textvariable=self.shader_var, state="readonly", width=10)
        self.shader_combo.grid(row=0, column=1, columnspan=3, sticky="ew", padx=(4, 0), pady=(0, 2))
        self.shader_combo.bind("<<ComboboxSelected>>", lambda _e: self._on_shader_combo())
        ttk.Label(controls, text="Mesh:").grid(row=1, column=0, sticky="w")
        mesh_combo = ttk.Combobox(controls, textvariable=self.mesh_var, state="readonly", width=8, values=["Cube", "Plane", "Pyramid", "Sphere", "UV Sphere"])
        mesh_combo.grid(row=1, column=1, sticky="ew", padx=(4, 8))
        mesh_combo.bind("<<ComboboxSelected>>", lambda _e: self.redraw())
        ttk.Label(controls, text="Material:").grid(row=1, column=2, sticky="w")
        material_combo = ttk.Combobox(controls, textvariable=self.material_var, state="readonly", width=8, values=["Preview", "Shader", "Mixed"])
        material_combo.grid(row=1, column=3, sticky="ew", padx=(4, 0))
        material_combo.bind("<<ComboboxSelected>>", lambda _e: self.redraw())

        controls2 = ttk.Frame(self)
        controls2.grid(row=1, column=0, sticky="ew", pady=(0, 4))
        ttk.Checkbutton(controls2, text="Wire", variable=self.wire_var, command=self.redraw).pack(side=tk.LEFT)
        ttk.Checkbutton(controls2, text="Auto rotate", variable=self.autorotate_var).pack(side=tk.LEFT, padx=(8, 0))
        ttk.Button(controls2, text="Reset View", command=self.reset_view).pack(side=tk.RIGHT)

        light_box = ttk.LabelFrame(self, text="Light source", padding=(4, 3))
        light_box.grid(row=2, column=0, sticky="ew", pady=(0, 4))
        light_top = ttk.Frame(light_box)
        light_top.grid(row=0, column=0, sticky="ew")
        ttk.Checkbutton(light_top, text="Enable", variable=self.light_enabled_var, command=self.redraw).pack(side=tk.LEFT)
        ttk.Button(light_top, text="Reset Light", command=self.reset_light).pack(side=tk.RIGHT)
        self._light_slider(light_box, 1, "X", self.light_x_var, -5.0, 5.0)
        self._light_slider(light_box, 2, "Y", self.light_y_var, -5.0, 5.0)
        self._light_slider(light_box, 3, "Z", self.light_z_var, -5.0, 5.0)
        self._light_slider(light_box, 4, "Power", self.light_power_var, 0.0, 3.0)
        self._light_slider(light_box, 5, "Ambient", self.ambient_var, 0.0, 1.0)
        light_box.columnconfigure(0, weight=1)

        self.canvas = tk.Canvas(self, width=420, height=420, bg="#141820", highlightthickness=1, highlightbackground="#2b3240")
        self.canvas.grid(row=3, column=0, sticky="nsew")
        self.info_var = tk.StringVar(value=self._last_render_note)
        self.info = ttk.Label(self, textvariable=self.info_var, anchor=tk.W, justify=tk.LEFT, wraplength=380)
        self.info.grid(row=4, column=0, sticky="ew", pady=(4, 0))

        self.rowconfigure(3, weight=1)
        self.columnconfigure(0, weight=1)

        self.canvas.bind("<Configure>", self._on_canvas_configure)
        self.canvas.bind("<ButtonPress-1>", self._start_drag)
        self.canvas.bind("<B1-Motion>", self._drag)
        self.canvas.bind("<MouseWheel>", self._wheel)
        self.canvas.bind("<Button-4>", lambda _e: self._zoom_by(1.08))
        self.canvas.bind("<Button-5>", lambda _e: self._zoom_by(1 / 1.08))
        self.after(33, self._tick)

    def set_shader(self, parser: Optional[SHBINParser]) -> None:
        self.parser = parser if parser and parser.loaded else None
        self.selected_instruction = None
        values: List[str] = []
        if self.parser:
            for dvle in self.parser.dvles:
                values.append(f"DVLE {dvle.index} {dvle.shader_type_name}")
        self.shader_combo.configure(values=values)
        if values:
            if self.current_dvle_index is None or self.current_dvle_index >= len(values):
                vertex_idx = next((d.index for d in self.parser.dvles if d.shader_type == 0), self.parser.dvles[0].index)
                self.current_dvle_index = vertex_idx
            self.shader_var.set(f"DVLE {self.current_dvle_index} {self.parser.dvles[self.current_dvle_index].shader_type_name}")
        else:
            self.current_dvle_index = None
            self.shader_var.set("")
        self.redraw()

    def set_selection(self, *, dvle_idx: Optional[int] = None, inst_idx: Optional[int] = None) -> None:
        if dvle_idx is not None and self.parser and 0 <= dvle_idx < len(self.parser.dvles):
            self.current_dvle_index = dvle_idx
            self.shader_var.set(f"DVLE {dvle_idx} {self.parser.dvles[dvle_idx].shader_type_name}")
        self.selected_instruction = inst_idx
        self.redraw()

    def refresh(self) -> None:
        self.set_shader(self.parser)

    def reset_view(self) -> None:
        self.yaw = -0.65
        self.pitch = 0.35
        self.zoom = 260.0
        self.redraw()

    def reset_light(self) -> None:
        self.light_enabled_var.set(True)
        self.light_x_var.set(2.2)
        self.light_y_var.set(2.8)
        self.light_z_var.set(-2.4)
        self.light_power_var.set(1.65)
        self.ambient_var.set(0.45)
        self.redraw()

    def _light_slider(self, parent: tk.Misc, row: int, label: str, var: tk.DoubleVar,
                      lo: float, hi: float) -> None:
        frame = ttk.Frame(parent)
        frame.grid(row=row, column=0, sticky="ew", pady=(2, 0))
        frame.columnconfigure(1, weight=1)
        ttk.Label(frame, text=label, width=7).grid(row=0, column=0, sticky="w")
        scale = ttk.Scale(frame, from_=lo, to=hi, variable=var, command=lambda _v: self.redraw())
        scale.grid(row=0, column=1, sticky="ew", padx=(4, 4))
        value = ttk.Label(frame, width=5, anchor=tk.E)
        value.grid(row=0, column=2, sticky="e")

        def update_label(*_args: Any) -> None:
            try:
                value.configure(text=f"{float(var.get()):.2f}")
            except Exception:
                value.configure(text="?")

        var.trace_add("write", update_label)
        update_label()

    def _on_canvas_configure(self, event: tk.Event) -> None:
        try:
            self.info.configure(wraplength=max(180, int(event.width) - 14))
        except Exception:
            pass
        self.redraw()

    def _on_shader_combo(self) -> None:
        text = self.shader_var.get().strip()
        if text.startswith("DVLE "):
            try:
                self.current_dvle_index = int(text.split()[1])
            except Exception:
                pass
        self.redraw()

    def _start_drag(self, event: tk.Event) -> None:
        self._drag_last = (int(event.x), int(event.y))

    def _drag(self, event: tk.Event) -> None:
        if self._drag_last is None:
            self._drag_last = (int(event.x), int(event.y))
            return
        lx, ly = self._drag_last
        dx = int(event.x) - lx
        dy = int(event.y) - ly
        self._drag_last = (int(event.x), int(event.y))
        self.yaw += dx * 0.012
        self.pitch += dy * 0.012
        self.pitch = max(-1.35, min(1.35, self.pitch))
        self.redraw()

    def _wheel(self, event: tk.Event) -> None:
        self._zoom_by(1.08 if int(event.delta) > 0 else 1 / 1.08)

    def _zoom_by(self, factor: float) -> None:
        self.zoom = max(80.0, min(900.0, self.zoom * factor))
        self.redraw()

    def _tick(self) -> None:
        if self.autorotate_var.get():
            self.yaw += 0.015
            self.redraw()
        self.after(33, self._tick)

    def _active_dvle(self) -> Optional[DVLEInfo]:
        if not self.parser or not self.parser.dvles:
            return None
        idx = self.current_dvle_index if self.current_dvle_index is not None else 0
        if not (0 <= idx < len(self.parser.dvles)):
            idx = 0
        return self.parser.dvles[idx]

    def _mesh(self) -> Tuple[List[Dict[str, Any]], List[Tuple[int, int, int]]]:
        name = self.mesh_var.get()
        if name == "Plane":
            verts = [
                {"pos": (-1.2, -0.75, 0.0, 1.0), "normal": (0.0, 0.0, 1.0, 0.0), "uv": (0.0, 0.0, 0.0, 1.0), "color": (1.0, 0.25, 0.25, 1.0)},
                {"pos": (1.2, -0.75, 0.0, 1.0), "normal": (0.0, 0.0, 1.0, 0.0), "uv": (1.0, 0.0, 0.0, 1.0), "color": (0.25, 1.0, 0.25, 1.0)},
                {"pos": (1.2, 0.75, 0.0, 1.0), "normal": (0.0, 0.0, 1.0, 0.0), "uv": (1.0, 1.0, 0.0, 1.0), "color": (0.25, 0.25, 1.0, 1.0)},
                {"pos": (-1.2, 0.75, 0.0, 1.0), "normal": (0.0, 0.0, 1.0, 0.0), "uv": (0.0, 1.0, 0.0, 1.0), "color": (1.0, 1.0, 0.25, 1.0)},
            ]
            return verts, [(0, 1, 2), (0, 2, 3)]
        if name == "Pyramid":
            verts = [
                {"pos": (-1.0, -0.8, -1.0, 1.0), "normal": (-0.5, -0.3, -0.5, 0.0), "uv": (0.0, 0.0, 0.0, 1.0), "color": (1.0, 0.25, 0.2, 1.0)},
                {"pos": (1.0, -0.8, -1.0, 1.0), "normal": (0.5, -0.3, -0.5, 0.0), "uv": (1.0, 0.0, 0.0, 1.0), "color": (0.2, 1.0, 0.25, 1.0)},
                {"pos": (1.0, -0.8, 1.0, 1.0), "normal": (0.5, -0.3, 0.5, 0.0), "uv": (1.0, 1.0, 0.0, 1.0), "color": (0.25, 0.45, 1.0, 1.0)},
                {"pos": (-1.0, -0.8, 1.0, 1.0), "normal": (-0.5, -0.3, 0.5, 0.0), "uv": (0.0, 1.0, 0.0, 1.0), "color": (1.0, 1.0, 0.25, 1.0)},
                {"pos": (0.0, 1.05, 0.0, 1.0), "normal": (0.0, 1.0, 0.0, 0.0), "uv": (0.5, 0.5, 0.0, 1.0), "color": (1.0, 0.45, 1.0, 1.0)},
            ]
            return verts, [(0, 1, 2), (0, 2, 3), (0, 4, 1), (1, 4, 2), (2, 4, 3), (3, 4, 0)]
        if name in {"Sphere", "UV Sphere"}:
            rings = 10 if name == "Sphere" else 14
            segments = 18 if name == "Sphere" else 26
            verts: List[Dict[str, Any]] = []
            for y in range(rings + 1):
                v = y / rings
                theta = math.pi * v
                sy = math.cos(theta)
                rr = math.sin(theta)
                for x in range(segments):
                    u = x / segments
                    phi = 2.0 * math.pi * u
                    px = rr * math.cos(phi)
                    pz = rr * math.sin(phi)
                    py = sy
                    verts.append({
                        "pos": (px, py, pz, 1.0),
                        "normal": (px, py, pz, 0.0),
                        "uv": (u, v, 0.0, 1.0),
                        "color": (0.25 + 0.75 * u, 0.25 + 0.75 * (1.0 - v), 0.55 + 0.35 * abs(pz), 1.0),
                    })
            faces: List[Tuple[int, int, int]] = []
            for y in range(rings):
                for x in range(segments):
                    a = y * segments + x
                    b = y * segments + ((x + 1) % segments)
                    c = (y + 1) * segments + ((x + 1) % segments)
                    d = (y + 1) * segments + x
                    if y != 0:
                        faces.append((a, b, d))
                    if y != rings - 1:
                        faces.append((b, c, d))
            return verts, faces
        coords = [
            (-1, -1, -1), (1, -1, -1), (1, 1, -1), (-1, 1, -1),
            (-1, -1, 1), (1, -1, 1), (1, 1, 1), (-1, 1, 1),
        ]
        colors = [
            (1, .25, .25, 1), (.25, 1, .25, 1), (.25, .45, 1, 1), (1, 1, .25, 1),
            (1, .45, 1, 1), (.25, 1, 1, 1), (1, .7, .25, 1), (.85, .85, .95, 1),
        ]
        verts = []
        for i, (x, y, z) in enumerate(coords):
            ln = max(0.0001, math.sqrt(x*x + y*y + z*z))
            verts.append({"pos": (x, y, z, 1.0), "normal": (x/ln, y/ln, z/ln, 0.0), "uv": ((x+1)*0.5, (y+1)*0.5, 0.0, 1.0), "color": colors[i]})
        faces = [
            (0, 1, 2), (0, 2, 3), (4, 6, 5), (4, 7, 6),
            (0, 4, 5), (0, 5, 1), (3, 2, 6), (3, 6, 7),
            (1, 5, 6), (1, 6, 2), (0, 3, 7), (0, 7, 4),
        ]
        return verts, faces

    def _constant_registers(self, dvle: DVLEInfo) -> List[List[float]]:
        regs = [[0.0, 0.0, 0.0, 1.0] for _ in range(128)]
        for c in dvle.constants:
            if c.entry_type == 2 and 0 <= c.register_id < len(regs):
                vals = [float(pica24_to_float(v)) for v in c.raw]
                regs[c.register_id] = (vals + [0.0, 0.0, 0.0, 1.0])[:4]
        return regs

    def _attribute_target(self, dvle: DVLEInfo, words: Iterable[str], default_reg: int) -> int:
        for inp in dvle.inputs:
            name = (inp.name or "").lower()
            if any(w in name for w in words):
                return max(0, min(15, int(inp.start)))
        return default_reg

    def _make_input_regs(self, dvle: DVLEInfo, vertex: Dict[str, Any]) -> List[List[float]]:
        regs = [[0.0, 0.0, 0.0, 1.0] for _ in range(16)]
        pos_reg = self._attribute_target(dvle, ("position", "pos", "vertex"), 0)
        nrm_reg = self._attribute_target(dvle, ("normal", "nrm"), 1)
        col_reg = self._attribute_target(dvle, ("color", "colour"), 2)
        uv_reg = self._attribute_target(dvle, ("texcoord", "tex", "uv"), 3)
        regs[pos_reg] = list(vertex.get("pos", (0, 0, 0, 1)))[:4]
        regs[nrm_reg] = list(vertex.get("normal", (0, 0, 1, 0)))[:4]
        regs[col_reg] = list(vertex.get("color", (1, 1, 1, 1)))[:4]
        regs[uv_reg] = list(vertex.get("uv", (0, 0, 0, 1)))[:4]
        return regs

    @staticmethod
    def _swizzle(v: List[float], swizzle: str, neg: bool = False) -> List[float]:
        idx = {"x": 0, "y": 1, "z": 2, "w": 3}
        swizzle = (swizzle or "xyzw").lower()
        out = [v[idx.get(ch, 0)] for ch in (swizzle + "xyzw")[:4]]
        return [-x for x in out] if neg else out

    @staticmethod
    def _component_color(rgb: Tuple[float, float, float], brightness: float = 1.0) -> str:
        vals = []
        for x in rgb:
            if not math.isfinite(float(x)):
                x = 0.0
            vals.append(max(0, min(255, int(255 * max(0.0, min(1.0, float(x) * brightness))))))
        return f"#{vals[0]:02x}{vals[1]:02x}{vals[2]:02x}"

    @staticmethod
    def _safe_rgb(values: Iterable[float], floor: float = 0.0) -> Tuple[float, float, float]:
        out: List[float] = []
        for x in list(values)[:3]:
            try:
                f = float(x)
            except (TypeError, ValueError):
                f = 0.0
            if not math.isfinite(f):
                f = 0.0
            out.append(max(floor, min(1.0, f)))
        while len(out) < 3:
            out.append(floor)
        return out[0], out[1], out[2]

    def _face_material_color(self, face: Tuple[int, int, int],
                             preview_colors: List[List[float]],
                             shader_colors: List[List[float]]) -> Tuple[float, float, float]:
        mode = (self.material_var.get() or "Preview").lower()
        preview = [sum(preview_colors[i][j] for i in face) / 3.0 for j in range(3)]
        shader = [sum(shader_colors[i][j] for i in face) / 3.0 for j in range(3)]

        shader_is_black = max(abs(x) for x in shader) < 0.035
        if mode == "shader":
            return self._safe_rgb(shader, floor=0.0)
        if mode == "mixed" and not shader_is_black:
            return self._safe_rgb([(preview[i] * 0.45) + (shader[i] * 0.55) for i in range(3)], floor=0.04)
        return self._safe_rgb(preview, floor=0.12)

    def _src(self, raw: int, vregs: List[List[float]], rregs: List[List[float]], cregs: List[List[float]]) -> List[float]:
        raw = int(raw)
        if raw < 0x10:
            return list(vregs[raw])
        if raw < 0x20:
            return list(rregs[raw - 0x10])
        cid = raw - 0x20
        if 0 <= cid < len(cregs):
            return list(cregs[cid])
        return [0.0, 0.0, 0.0, 1.0]

    def _write_dest(self, dst_raw: int, mask: str, values: List[float], rregs: List[List[float]], oregs: List[List[float]]) -> None:
        target = oregs[int(dst_raw)] if int(dst_raw) < 0x10 else rregs[int(dst_raw) - 0x10]
        if mask == "-":
            return
        if not mask:
            mask = "xyzw"
        for ch in mask:
            idx = "xyzw".find(ch)
            if 0 <= idx < 4:
                target[idx] = float(values[idx])

    def _execute_vertex(self, dvle: DVLEInfo, vertex: Dict[str, Any]) -> Tuple[List[float], List[float], int]:
        if not self.parser or not self.parser.dvlp:
            return list(vertex.get("pos", (0, 0, 0, 1)))[:4], list(vertex.get("color", (1, 1, 1, 1)))[:4], 0
        vregs = self._make_input_regs(dvle, vertex)
        rregs = [[0.0, 0.0, 0.0, 1.0] for _ in range(16)]
        oregs = [[0.0, 0.0, 0.0, 1.0] for _ in range(16)]
        cregs = self._constant_registers(dvle)
        executed = 0
        start, end = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
        instructions = self.parser.dvlp.instructions
        end = min(end, len(instructions) - 1)
        start = max(0, start)

        for inst in instructions[start:end + 1]:
            name = inst.mnemonic.upper()
            if name == "END":
                break
            if name not in self.SUPPORTED_OPS:
                continue
            f = inst.fields
            desc = f.get("opdesc", {}) if isinstance(f.get("opdesc"), dict) else {}
            executed += 1
            try:
                if inst.fmt in {"1", "1u", "1i", "1c"}:
                    s1 = self._src(int(f.get("src1_raw", 0)), vregs, rregs, cregs)
                    s2 = self._src(int(f.get("src2_raw", 0)), vregs, rregs, cregs)
                    a = self._swizzle(s1, str(desc.get("src1_swizzle", "xyzw")), bool(desc.get("src1_neg", False)))
                    b = self._swizzle(s2, str(desc.get("src2_swizzle", "xyzw")), bool(desc.get("src2_neg", False)))
                    if name == "ADD": out = [a[i] + b[i] for i in range(4)]
                    elif name == "MUL": out = [a[i] * b[i] for i in range(4)]
                    elif name == "MIN": out = [min(a[i], b[i]) for i in range(4)]
                    elif name == "MAX": out = [max(a[i], b[i]) for i in range(4)]
                    elif name == "SGE": out = [1.0 if a[i] >= b[i] else 0.0 for i in range(4)]
                    elif name == "SLT": out = [1.0 if a[i] < b[i] else 0.0 for i in range(4)]
                    elif name == "DP3":
                        d = sum(a[i] * b[i] for i in range(3)); out = [d, d, d, d]
                    elif name == "DP4":
                        d = sum(a[i] * b[i] for i in range(4)); out = [d, d, d, d]
                    elif name == "DPH":
                        d = sum(a[i] * b[i] for i in range(3)) + b[3]; out = [d, d, d, d]
                    elif name == "DST":
                        out = [1.0, a[1] * b[1], a[2], b[3]]
                    elif name in {"MOV", "MOVA"}:
                        out = a
                    elif name == "RCP":
                        out = [1.0 / a[0] if abs(a[0]) > 1e-8 else 0.0] * 4
                    elif name == "RSQ":
                        out = [1.0 / math.sqrt(abs(a[0])) if abs(a[0]) > 1e-8 else 0.0] * 4
                    elif name == "FLR": out = [math.floor(x) for x in a]
                    elif name == "EX2": out = [2.0 ** max(-64.0, min(64.0, x)) for x in a]
                    elif name == "LG2": out = [math.log(max(abs(x), 1e-8), 2.0) for x in a]
                    else: continue
                    if "dst_raw" in f:
                        self._write_dest(int(f.get("dst_raw", 0)), str(desc.get("dest_mask", "xyzw")), out, rregs, oregs)
                elif inst.fmt in {"5", "5i"}:
                    s1 = self._src(int(f.get("src1_raw", 0)), vregs, rregs, cregs)
                    s2 = self._src(int(f.get("src2_raw", 0)), vregs, rregs, cregs)
                    s3 = self._src(int(f.get("src3_raw", 0)), vregs, rregs, cregs)
                    a = self._swizzle(s1, str(desc.get("src1_swizzle", "xyzw")), bool(desc.get("src1_neg", False)))
                    b = self._swizzle(s2, str(desc.get("src2_swizzle", "xyzw")), bool(desc.get("src2_neg", False)))
                    c = self._swizzle(s3, str(desc.get("src3_swizzle", "xyzw")), bool(desc.get("src3_neg", False)))
                    out = [a[i] * b[i] + c[i] for i in range(4)]
                    self._write_dest(int(f.get("dst_raw", 0)), str(desc.get("dest_mask", "xyzw")), out, rregs, oregs)
            except Exception:
                continue

        pos_reg = 0
        color_reg = None
        for out in dvle.outputs:
            out_name = OUTPUT_TYPES.get(out.output_type, "")
            if out_name == "result.position":
                pos_reg = max(0, min(15, int(out.register_id)))
            elif out_name == "result.color":
                color_reg = max(0, min(15, int(out.register_id)))
        pos = list(oregs[pos_reg])
        col = list(vertex.get("color", (1, 1, 1, 1)))[:4]
        if color_reg is not None:
            col = list(oregs[color_reg])
        return pos, col, executed

    def _fit_positions(self, points: List[List[float]], original: List[Tuple[float, float, float]]) -> Tuple[List[Tuple[float, float, float]], bool]:
        out: List[Tuple[float, float, float]] = []
        for p in points:
            w = p[3] if len(p) > 3 else 1.0
            if abs(w) > 1e-7:
                out.append((p[0] / w, p[1] / w, p[2] / w))
            else:
                out.append((p[0], p[1], p[2]))
        finite = all(all(math.isfinite(v) for v in p) for p in out)
        if not finite:
            return original, True
        xs, ys, zs = [p[0] for p in out], [p[1] for p in out], [p[2] for p in out]
        span = max(max(xs) - min(xs), max(ys) - min(ys), max(zs) - min(zs), 1e-9)
        collapsed = span < 0.0001 or max(abs(x) for p in out for x in p) > 1e6
        if collapsed:
            return original, True
        cx, cy, cz = (max(xs) + min(xs)) * 0.5, (max(ys) + min(ys)) * 0.5, (max(zs) + min(zs)) * 0.5
        scale = 2.1 / span
        return [((x - cx) * scale, (y - cy) * scale, (z - cz) * scale) for x, y, z in out], False

    def _rotate_project(self, p: Tuple[float, float, float], width: int, height: int) -> Tuple[float, float, float]:
        x, y, z = p
        cy, sy = math.cos(self.yaw), math.sin(self.yaw)
        cp, sp = math.cos(self.pitch), math.sin(self.pitch)
        x, z = x * cy + z * sy, -x * sy + z * cy
        y, z = y * cp - z * sp, y * sp + z * cp
        dist = 4.0
        base = max(80.0, float(min(width, height)))
        dynamic_zoom = base * 0.62 * (float(self.zoom) / 260.0)
        persp = dynamic_zoom / max(0.25, z + dist)
        return width * 0.5 + x * persp, height * 0.52 - y * persp, z

    def _draw_grid(self, width: int, height: int) -> None:
        self.canvas.create_rectangle(0, 0, width, height, fill="#141820", outline="")
        cx, cy = width * 0.5, height * 0.52
        for i in range(-4, 5):
            x0, y0, _ = self._rotate_project((i * 0.5, -1.35, -2.0), width, height)
            x1, y1, _ = self._rotate_project((i * 0.5, -1.35, 2.0), width, height)
            self.canvas.create_line(x0, y0, x1, y1, fill="#222a35")
            x2, y2, _ = self._rotate_project((-2.0, -1.35, i * 0.5), width, height)
            x3, y3, _ = self._rotate_project((2.0, -1.35, i * 0.5), width, height)
            self.canvas.create_line(x2, y2, x3, y3, fill="#222a35")
        axes = [((0, 0, 0), (1.35, 0, 0), "#d85858", "X"), ((0, 0, 0), (0, 1.35, 0), "#58d878", "Y"), ((0, 0, 0), (0, 0, 1.35), "#5898e8", "Z")]
        for a, b, col, label in axes:
            x0, y0, _ = self._rotate_project(a, width, height)
            x1, y1, _ = self._rotate_project(b, width, height)
            self.canvas.create_line(x0, y0, x1, y1, fill=col, width=2)
            self.canvas.create_text(x1, y1, text=label, fill=col, font=("Segoe UI", 8, "bold"))
        self.canvas.create_oval(cx - 2, cy - 2, cx + 2, cy + 2, fill="#606a78", outline="")

    def _light_position(self) -> Tuple[float, float, float]:
        return (
            float(self.light_x_var.get()),
            float(self.light_y_var.get()),
            float(self.light_z_var.get()),
        )

    @staticmethod
    def _normalize3(v: Tuple[float, float, float]) -> Tuple[float, float, float]:
        x, y, z = v
        length = math.sqrt(x * x + y * y + z * z)
        if length <= 1e-8 or not math.isfinite(length):
            return 0.0, 1.0, 0.0
        return x / length, y / length, z / length

    @staticmethod
    def _face_normal(pts3: List[Tuple[float, float, float]]) -> Tuple[float, float, float]:
        ux = pts3[1][0] - pts3[0][0]
        uy = pts3[1][1] - pts3[0][1]
        uz = pts3[1][2] - pts3[0][2]
        vx = pts3[2][0] - pts3[0][0]
        vy = pts3[2][1] - pts3[0][1]
        vz = pts3[2][2] - pts3[0][2]
        return ShaderPreview3D._normalize3((uy * vz - uz * vy, uz * vx - ux * vz, ux * vy - uy * vx))

    def _light_brightness(self, pts3: List[Tuple[float, float, float]]) -> float:
        ambient = max(0.0, min(1.0, float(self.ambient_var.get())))
        if not self.light_enabled_var.get():
            return 1.0
        nx, ny, nz = self._face_normal(pts3)
        cx = sum(p[0] for p in pts3) / 3.0
        cy = sum(p[1] for p in pts3) / 3.0
        cz = sum(p[2] for p in pts3) / 3.0
        lx, ly, lz = self._light_position()
        to_light = (lx - cx, ly - cy, lz - cz)
        dist_sq = max(0.05, to_light[0] * to_light[0] + to_light[1] * to_light[1] + to_light[2] * to_light[2])
        ldx, ldy, ldz = self._normalize3(to_light)
        
        dot = nx * ldx + ny * ldy + nz * ldz
        diffuse = abs(dot)
        attenuation = min(1.0, 8.0 / dist_sq)
        power = max(0.0, float(self.light_power_var.get()))
        return max(0.0, min(2.2, ambient + diffuse * attenuation * power))

    def _draw_light_gizmo(self, width: int, height: int) -> None:
        if not self.light_enabled_var.get():
            return
        lx, ly, lz = self._light_position()
        sx, sy, sz = self._rotate_project((lx, ly, lz), width, height)
        cx, cy, _ = self._rotate_project((0.0, 0.0, 0.0), width, height)
        radius = max(5.0, min(13.0, 7.0 + float(self.light_power_var.get()) * 2.0))
        self.canvas.create_line(cx, cy, sx, sy, fill="#8a7a35", dash=(4, 3))
        self.canvas.create_oval(sx - radius * 2.2, sy - radius * 2.2, sx + radius * 2.2, sy + radius * 2.2, fill="", outline="#6b5d24")
        self.canvas.create_oval(sx - radius, sy - radius, sx + radius, sy + radius, fill="#ffd966", outline="#fff0a8", width=2)
        self.canvas.create_text(sx + radius + 4, sy, anchor=tk.W, text="Light", fill="#ffe994", font=("Segoe UI", 8, "bold"))

    def redraw(self) -> None:
        width = max(40, int(self.canvas.winfo_width()))
        height = max(40, int(self.canvas.winfo_height()))
        self.canvas.delete("all")
        self._draw_grid(width, height)
        dvle = self._active_dvle()
        if not self.parser or not self.parser.dvlp or dvle is None:
            self.info_var.set("Open a .shbin to see a live 3D shader preview.")
            self.canvas.create_text(width / 2, height / 2, text="No shader loaded", fill="#d0d7e2", font=("Segoe UI", 13, "bold"))
            return

        vertices, faces = self._mesh()
        raw_positions: List[List[float]] = []
        colors: List[List[float]] = []
        preview_colors: List[List[float]] = []
        executed_counts: List[int] = []
        for v in vertices:
            pos, col, executed = self._execute_vertex(dvle, v)
            raw_positions.append(pos)
            colors.append(col)
            preview_colors.append(list(v.get("color", (0.75, 0.75, 0.82, 1.0)))[:4])
            executed_counts.append(executed)
        original = [(float(v["pos"][0]), float(v["pos"][1]), float(v["pos"][2])) for v in vertices]
        fitted, fallback = self._fit_positions(raw_positions, original)
        projected = [self._rotate_project(p, width, height) for p in fitted]

        face_draw: List[Tuple[float, Tuple[int, int, int]]] = []
        for face in faces:
            z = sum(projected[i][2] for i in face) / 3.0
            face_draw.append((z, face))
        face_draw.sort(key=lambda x: x[0])

        for _z, (a, b, c) in face_draw:
            pts3 = [fitted[a], fitted[b], fitted[c]]
            brightness = self._light_brightness(pts3)
            avg_col = self._face_material_color((a, b, c), preview_colors, colors)
            fill = self._component_color(avg_col, brightness)
            outline = "#10141b" if not self.wire_var.get() else "#d6dde8"
            coords: List[float] = []
            for idx in (a, b, c):
                coords.extend([projected[idx][0], projected[idx][1]])
            self.canvas.create_polygon(coords, fill=fill, outline=outline, width=1)

        self._draw_light_gizmo(width, height)

        if self.selected_instruction is not None and self.parser.dvlp and 0 <= self.selected_instruction < len(self.parser.dvlp.instructions):
            inst = self.parser.dvlp.instructions[self.selected_instruction]
            sel_text = f"Selected {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}"
            self.canvas.create_rectangle(6, 6, width - 6, 44, fill="#0f131a", outline="#3a4556")
            self.canvas.create_text(12, 14, anchor=tk.NW, text=sel_text[:92], fill="#e9eef7", font=("Consolas", 9))

        lx, ly, lz = self._light_position()
        light_state = "light off"
        if self.light_enabled_var.get():
            light_state = f"light ({lx:.1f}, {ly:.1f}, {lz:.1f})"
        self._last_render_note = (
            f"{dvle.shader_type_name} DVLE {dvle.index}: entry {dvle.opcode_entry}, end {dvle.opcode_end}; "
            f"executed ~{max(executed_counts or [0])} supported vertex ops; {light_state}; "
            f"material {self.material_var.get()}."
        )
        if fallback:
            self._last_render_note += " Output collapsed/missing, so the preview is using fallback mesh positions."
        self.info_var.set(self._last_render_note)

class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self._configure_initial_window()
        self.parser = SHBINParser()
        self.selected_constant: Optional[Tuple[int, int]] = None
        self.selected_instruction: Optional[int] = None
        self.selected_opdesc: Optional[int] = None
        self.item_ranges: Dict[str, Tuple[int, int]] = {}
        self.filter_var = tk.StringVar()
        self.edit_vars = [tk.StringVar() for _ in range(4)]
        self.raw_vars = [tk.StringVar() for _ in range(4)]
        self.instr_mnemonic_var = tk.StringVar()
        self.instr_raw_var = tk.StringVar()
        self.instr_asm_var = tk.StringVar()
        self.instr_desc_var = tk.StringVar()
        self.instr_dst_var = tk.StringVar()
        self.instr_src1_var = tk.StringVar()
        self.instr_src2_var = tk.StringVar()
        self.instr_src3_var = tk.StringVar()
        self.instr_idx_var = tk.StringVar()
        self.instr_num_var = tk.StringVar()
        self.instr_target_var = tk.StringVar()
        self.instr_condop_var = tk.StringVar()
        self.instr_boolint_var = tk.StringVar()
        self.instr_refx_var = tk.StringVar()
        self.instr_refy_var = tk.StringVar()
        self.instr_cmpx_var = tk.StringVar()
        self.instr_cmpy_var = tk.StringVar()
        self.opdesc_raw_var = tk.StringVar()
        self.opdesc_flags_var = tk.StringVar()
        self.opdesc_mask_var = tk.StringVar()
        self.opdesc_src1_swizzle_var = tk.StringVar()
        self.opdesc_src2_swizzle_var = tk.StringVar()
        self.opdesc_src3_swizzle_var = tk.StringVar()
        self.opdesc_src1_neg_var = tk.BooleanVar(value=False)
        self.opdesc_src2_neg_var = tk.BooleanVar(value=False)
        self.opdesc_src3_neg_var = tk.BooleanVar(value=False)
        self.cfg_dvle_var = tk.StringVar(value="0")
        self.analysis_dvle_var = tk.StringVar(value="0")
        self.symbol_dvle_var = tk.StringVar(value="global")
        self.symbol_register_var = tk.StringVar(value="c17")
        self.symbol_name_var = tk.StringVar(value="CHUNK_ORIGIN_AND_SCALE")
        self.instr_register_widgets: Dict[str, ttk.Combobox] = {}
        self.symbol_tree: Optional[ttk.Treeview] = None
        self.symbol_register_combo: Optional[ttk.Combobox] = None
        self.symbol_scope_combo: Optional[ttk.Combobox] = None
        self._build_ui()

    def _configure_initial_window(self) -> None:
        try:
            sw, sh = int(self.winfo_screenwidth()), int(self.winfo_screenheight())
        except Exception:
            sw, sh = 1540, 820
        width = min(1540, max(980, int(sw * 0.92)))
        height = min(900, max(620, int(sh * 0.86)))
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        self.geometry(f"{width}x{height}+{x}+{y}")
        self.minsize(min(980, max(760, sw - 120)), min(600, max(520, sh - 140)))

    def _build_ui(self) -> None:
        self._build_toolbar()
        self._build_body()
        self._build_statusbar()
        self._set_status("Open a .shbin / DVLB file to begin.")

    def _build_toolbar(self) -> None:
        toolbar_outer = ttk.Frame(self, padding=(4, 4))
        toolbar_outer.pack(side=tk.TOP, fill=tk.X)
        toolbar_outer.columnconfigure(0, weight=1)

        self.toolbar_canvas = tk.Canvas(toolbar_outer, highlightthickness=0, height=34)
        self.toolbar_canvas.grid(row=0, column=0, sticky="ew")
        self.toolbar_scroll = ttk.Scrollbar(toolbar_outer, orient=tk.HORIZONTAL, command=self.toolbar_canvas.xview)
        self.toolbar_scroll.grid(row=1, column=0, sticky="ew")
        self.toolbar_canvas.configure(xscrollcommand=self.toolbar_scroll.set)
        toolbar = ttk.Frame(self.toolbar_canvas)
        self.toolbar_window = self.toolbar_canvas.create_window((0, 0), window=toolbar, anchor="nw")

        def _sync_toolbar(_event: Optional[tk.Event] = None) -> None:
            try:
                self.toolbar_canvas.configure(scrollregion=self.toolbar_canvas.bbox("all"))
                self.toolbar_canvas.configure(height=max(30, toolbar.winfo_reqheight()))
            except Exception:
                pass

        toolbar.bind("<Configure>", _sync_toolbar)
        self.toolbar_canvas.bind("<Configure>", _sync_toolbar)

        ttk.Button(toolbar, text="Open .shbin", command=self.open_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Save", command=self.save_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Save As", command=self.save_file_as).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        ttk.Button(toolbar, text="Export JSON", command=self.export_json).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Import JSON Values", command=self.import_json_values).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Constants CSV", command=self.export_csv).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Disasm", command=self.export_disassembly).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Full ASM", command=self.export_full_asm).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Import Full ASM", command=self.import_full_asm).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        ttk.Button(toolbar, text="Symbols", command=self.show_symbol_tools).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Export Symbol Map", command=self.export_symbol_map).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Import Symbol Map", command=self.import_symbol_map).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=8)
        ttk.Button(toolbar, text="Validate", command=self.show_validation).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Analyze Regs", command=self.show_register_lifetimes).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="CFG", command=self.refresh_cfg).pack(side=tk.LEFT, padx=2)

    def _build_body(self) -> None:
        paned = ttk.Panedwindow(self, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)
        self.main_paned = paned
        self._pane_resize_job: Optional[str] = None
        self._pane_first_fit = True

        left = ttk.Frame(paned, padding=4)
        self.left_pane = left
        paned.add(left, weight=1)
        filter_bar = ttk.Frame(left)
        filter_bar.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 4))
        filter_bar.columnconfigure(1, weight=1)
        ttk.Label(filter_bar, text="Filter:").grid(row=0, column=0, sticky="w", padx=(0, 4))
        filter_entry = ttk.Entry(filter_bar, textvariable=self.filter_var)
        filter_entry.grid(row=0, column=1, sticky="ew", padx=(0, 4))
        filter_entry.bind("<KeyRelease>", lambda _e: self.refresh_tree())
        ttk.Button(filter_bar, text="Clear", command=lambda: (self.filter_var.set(""), self.refresh_tree())).grid(row=0, column=2, sticky="e")

        self.tree = ttk.Treeview(left, columns=("Kind", "Info"), show="tree headings")
        self.tree.heading("#0", text="Section / Entry")
        self.tree.heading("Kind", text="Kind")
        self.tree.heading("Info", text="Info")
        self.tree.column("#0", width=420, minwidth=80, stretch=True)
        self.tree.column("Kind", width=70, minwidth=40, anchor=tk.W, stretch=False)
        self.tree.column("Info", width=90, minwidth=40, anchor=tk.W, stretch=False)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Configure>", self._fit_tree_columns)

        yscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.tree.yview)
        xscroll = ttk.Scrollbar(left, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        self.tree.grid(row=1, column=0, sticky="nsew")
        yscroll.grid(row=1, column=1, sticky="ns")
        xscroll.grid(row=2, column=0, sticky="ew")
        left.rowconfigure(1, weight=1)
        left.columnconfigure(0, weight=1)

        right = ttk.Frame(paned, padding=4)
        self.center_pane = right
        paned.add(right, weight=3)

        self.notebook = ttk.Notebook(right)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.details_text = self._make_text_tab("Details")
        self.edit_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.edit_frame, text="Edit Constant")
        self.instruction_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.instruction_frame, text="Edit Instruction")
        self.opdesc_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.opdesc_frame, text="Edit Opdesc")
        self.hex_text = self._make_text_tab("Hex View")
        self.raw_text = self._make_text_tab("Raw Tables")
        self.analysis_text = self._make_text_tab("Register Analysis")
        self.symbol_frame = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(self.symbol_frame, text="Symbol Map")
        self.cfg_frame = ttk.Frame(self.notebook, padding=4)
        self.notebook.add(self.cfg_frame, text="Control Flow")
        self._build_edit_tab()
        self._build_instruction_tab()
        self._build_opdesc_tab()
        self._build_symbol_tab()
        self._build_cfg_tab()

        self.preview = ShaderPreview3D(paned)
        paned.add(self.preview, weight=2)
        for child, minsize in ((left, 260), (right, 420), (self.preview, 220)):
            try:
                paned.paneconfigure(child, minsize=minsize)
            except Exception:
                pass
        paned.bind("<Configure>", self._queue_fit_main_panes)
        self.after_idle(lambda: self._fit_main_panes(force=True))

    def _queue_fit_main_panes(self, _event: Optional[tk.Event] = None) -> None:
        try:
            if self._pane_resize_job:
                self.after_cancel(self._pane_resize_job)
        except Exception:
            pass
        self._pane_resize_job = self.after(80, self._fit_main_panes)

    def _fit_main_panes(self, force: bool = False) -> None:
        paned = getattr(self, "main_paned", None)
        if paned is None:
            return
        try:
            total = int(paned.winfo_width())
        except Exception:
            return
        if total < 700:
            return

        target_left = max(340, min(520, int(total * 0.30)))
        target_preview = max(280, min(460, int(total * 0.24)))
        min_center = 500
        if target_left + target_preview + min_center > total:
            target_left = max(300, min(target_left, int(total * 0.28)))
            target_preview = max(240, min(target_preview, total - target_left - min_center))
        target_preview = max(230, target_preview)
        second_sash = max(target_left + min_center, total - target_preview)

        try:
            cur_left = int(paned.sashpos(0))
            cur_second = int(paned.sashpos(1))
            cur_preview = total - cur_second
            cur_center = cur_second - cur_left
        except Exception:
            cur_preview = cur_center = 0

        needs_fit = bool(force or getattr(self, "_pane_first_fit", False) or cur_preview < 230 or cur_center < 460)
        if not needs_fit:
            return
        try:
            paned.sashpos(0, target_left)
            paned.sashpos(1, second_sash)
            self._pane_first_fit = False
        except Exception:
            pass

    def _fit_tree_columns(self, _event: Optional[tk.Event] = None) -> None:
        tree = getattr(self, "tree", None)
        if tree is None:
            return
        try:
            width = int(tree.winfo_width())
        except Exception:
            return
        if width <= 80:
            return

        usable = max(80, width - 26)
        kind_w = max(48, min(78, int(usable * 0.14)))
        info_w = max(52, min(112, int(usable * 0.18)))
        section_w = max(120, usable - kind_w - info_w)
        try:
            tree.column("#0", width=section_w, minwidth=60, stretch=True)
            tree.column("Kind", width=kind_w, minwidth=40, stretch=False)
            tree.column("Info", width=info_w, minwidth=40, stretch=False)
        except Exception:
            pass

    def _make_text_tab(self, title: str) -> tk.Text:
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text=title)
        text = tk.Text(frame, wrap=tk.NONE, undo=False, font=("Consolas", 10))
        text.configure(state=tk.DISABLED)
        yscroll = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=text.yview)
        xscroll = ttk.Scrollbar(frame, orient=tk.HORIZONTAL, command=text.xview)
        text.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        text.grid(row=0, column=0, sticky="nsew")
        yscroll.grid(row=0, column=1, sticky="ns")
        xscroll.grid(row=1, column=0, sticky="ew")
        frame.rowconfigure(0, weight=1)
        frame.columnconfigure(0, weight=1)
        return text

    def _build_edit_tab(self) -> None:
        self.edit_name_label = ttk.Label(self.edit_frame, text="Select a constant to edit.", font=("Segoe UI", 10, "bold"))
        self.edit_name_label.grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 10))

        labels = ["X / R", "Y / G", "Z / B", "W / A"]
        for i, label in enumerate(labels):
            ttk.Label(self.edit_frame, text=label, width=8).grid(row=i + 1, column=0, sticky="w", pady=3)
            ttk.Entry(self.edit_frame, textvariable=self.edit_vars[i], width=22).grid(row=i + 1, column=1, sticky="ew", padx=(4, 12), pady=3)
            ttk.Label(self.edit_frame, text="raw").grid(row=i + 1, column=2, sticky="e", pady=3)
            ttk.Entry(self.edit_frame, textvariable=self.raw_vars[i], width=16).grid(row=i + 1, column=3, sticky="ew", padx=(4, 0), pady=3)

        btns = ttk.Frame(self.edit_frame)
        btns.grid(row=6, column=0, columnspan=4, sticky="ew", pady=(14, 0))
        ttk.Button(btns, text="Apply Display Values", command=self.apply_display_values).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Apply Raw Values", command=self.apply_raw_values).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Copy Constant JSON", command=self.copy_constant_json).pack(side=tk.LEFT)

        help_text = (
            "Float uniforms are stored as PICA 24-bit floats inside 32-bit fields.\n"
            "For Float24 constants, edit display values as normal floats or raw as 0x00RRGGBB-style 24-bit values.\n"
            "For Bool constants, only X / raw0 is used. Int constants use byte values 0..255."
        )
        ttk.Label(self.edit_frame, text=help_text, foreground="#555", wraplength=520, justify=tk.LEFT).grid(
            row=7, column=0, columnspan=4, sticky="w", pady=(16, 0)
        )
        self.edit_frame.columnconfigure(1, weight=1)
        self.edit_frame.columnconfigure(3, weight=1)

    def _build_instruction_tab(self) -> None:
        header = ttk.Label(self.instruction_frame, text="Select a decoded instruction to edit.", font=("Segoe UI", 10, "bold"))
        header.grid(row=0, column=0, columnspan=6, sticky="w", pady=(0, 8))
        self.instr_header_label = header

        ttk.Label(self.instruction_frame, text="ASM line").grid(row=1, column=0, sticky="w", pady=3)
        asm_entry = ttk.Entry(self.instruction_frame, textvariable=self.instr_asm_var)
        asm_entry.grid(row=1, column=1, columnspan=4, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.instruction_frame, text="Apply ASM", command=self.apply_instruction_asm).grid(row=1, column=5, sticky="ew", pady=3)

        ttk.Label(self.instruction_frame, text="Raw word").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.instruction_frame, textvariable=self.instr_raw_var, width=18).grid(row=2, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.instruction_frame, text="Apply Raw", command=self.apply_instruction_raw).grid(row=2, column=2, sticky="ew", pady=3)
        ttk.Label(self.instruction_frame, text="Mnemonic").grid(row=2, column=3, sticky="e", padx=(16, 4), pady=3)
        values = sorted(set(MNEMONIC_TO_OPCODE.keys()) - {"EXP", "LOG", "LIT"})
        self.instr_mnemonic_combo = ttk.Combobox(self.instruction_frame, textvariable=self.instr_mnemonic_var, values=values, width=12)
        self.instr_mnemonic_combo.grid(row=2, column=4, sticky="ew", padx=(4, 8), pady=3)
        self.instr_mnemonic_combo.bind("<<ComboboxSelected>>", lambda _e: self._refresh_instruction_register_choices(None))
        self.instr_mnemonic_combo.bind("<KeyRelease>", lambda _e: self.after_idle(lambda: self._refresh_instruction_register_choices(None)))
        ttk.Button(self.instruction_frame, text="Apply Fields", command=self.apply_instruction_fields).grid(row=2, column=5, sticky="ew", pady=3)

        fields = [
            ("Desc ID", self.instr_desc_var), ("DST", self.instr_dst_var), ("SRC1", self.instr_src1_var),
            ("SRC2", self.instr_src2_var), ("SRC3", self.instr_src3_var), ("IDX", self.instr_idx_var),
            ("NUM", self.instr_num_var), ("Target", self.instr_target_var), ("CondOp", self.instr_condop_var),
            ("Bool/Int ID", self.instr_boolint_var), ("RefX", self.instr_refx_var), ("RefY", self.instr_refy_var),
            ("CmpX", self.instr_cmpx_var), ("CmpY", self.instr_cmpy_var),
        ]
        row = 3
        self.instr_register_widgets = {}
        for i, (label, var) in enumerate(fields):
            r = row + i // 2
            c = 0 if i % 2 == 0 else 3
            ttk.Label(self.instruction_frame, text=label).grid(row=r, column=c, sticky="w", pady=3)
            if label in {"DST", "SRC1", "SRC2", "SRC3", "Bool/Int ID", "CondOp", "CmpX", "CmpY"}:
                combo = ttk.Combobox(self.instruction_frame, textvariable=var, width=24)
                if label == "CondOp":
                    combo.configure(values=[CONDOP_NAMES[i] for i in sorted(CONDOP_NAMES)])
                elif label in {"CmpX", "CmpY"}:
                    combo.configure(values=[CMP_OP_NAMES[i] for i in sorted(CMP_OP_NAMES)])
                combo.grid(row=r, column=c + 1, columnspan=2, sticky="ew", padx=(4, 10), pady=3)
                self.instr_register_widgets[label] = combo
            else:
                ttk.Entry(self.instruction_frame, textvariable=var, width=18).grid(row=r, column=c + 1, columnspan=2, sticky="ew", padx=(4, 10), pady=3)

        bottom_row = row + (len(fields) + 1) // 2
        instr_btns = ttk.Frame(self.instruction_frame)
        instr_btns.grid(row=bottom_row, column=0, columnspan=6, sticky="ew", pady=(10, 0))
        for i, (text, command) in enumerate([
            ("Insert NOP Before", self.insert_nop_before_selected),
            ("Delete / Shift Up", self.delete_selected_instruction),
            ("Add ASM Near DVLE End", self.add_asm_instruction_to_active_dvle),
        ]):
            ttk.Button(instr_btns, text=text, command=command).grid(row=0, column=i, sticky="ew", padx=(0 if i == 0 else 4, 0))
            instr_btns.columnconfigure(i, weight=1)

        help_text = (
            "ASM patching supports arithmetic forms like: add r0.xy, v0.xyzw, c0.xyzw  |  "
            "mul r1, r0, c5  |  dp3 o0.xyz, r0, c2  |  mad r2, r0, c1, r1.\n"
            "Flow-control can be edited directly in the ASM line now. Unused dropdowns are disabled per mnemonic. "
            "Register fields accept native names, plain symbols, or dropdown values like CHUNK_ORIGIN_AND_SCALE (c17)."
        )
        self.instr_help_label = ttk.Label(self.instruction_frame, text=help_text, foreground="#555", wraplength=760, justify=tk.LEFT)
        self.instr_help_label.grid(row=bottom_row + 1, column=0, columnspan=6, sticky="w", pady=(16, 0))
        self.instruction_frame.bind("<Configure>", self._fit_instruction_help_text)

        for col, weight in enumerate((0, 1, 1, 0, 1, 1)):
            self.instruction_frame.columnconfigure(col, weight=weight)

    def _fit_instruction_help_text(self, event: Optional[tk.Event] = None) -> None:
        try:
            width = int(event.width if event is not None else self.instruction_frame.winfo_width())
            self.instr_help_label.configure(wraplength=max(360, width - 32))
        except Exception:
            pass

    def _build_opdesc_tab(self) -> None:
        self.opdesc_header_label = ttk.Label(self.opdesc_frame, text="Select an operand descriptor to edit.", font=("Segoe UI", 10, "bold"))
        self.opdesc_header_label.grid(row=0, column=0, columnspan=5, sticky="w", pady=(0, 8))

        ttk.Label(self.opdesc_frame, text="Raw desc").grid(row=1, column=0, sticky="w", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_raw_var, width=18).grid(row=1, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Label(self.opdesc_frame, text="Flags").grid(row=1, column=2, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_flags_var, width=18).grid(row=1, column=3, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.opdesc_frame, text="Apply Raw", command=self.apply_opdesc_raw).grid(row=1, column=4, sticky="ew", pady=3)

        ttk.Label(self.opdesc_frame, text="Dest mask").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_mask_var, width=12).grid(row=2, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Button(self.opdesc_frame, text="Apply Decoded", command=self.apply_opdesc_decoded).grid(row=2, column=4, sticky="ew", pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC1", variable=self.opdesc_src1_neg_var).grid(row=3, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC1 swizzle").grid(row=3, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src1_swizzle_var, width=12).grid(row=3, column=2, sticky="ew", padx=(4, 8), pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC2", variable=self.opdesc_src2_neg_var).grid(row=4, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC2 swizzle").grid(row=4, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src2_swizzle_var, width=12).grid(row=4, column=2, sticky="ew", padx=(4, 8), pady=3)

        ttk.Checkbutton(self.opdesc_frame, text="Neg SRC3", variable=self.opdesc_src3_neg_var).grid(row=5, column=0, sticky="w", pady=3)
        ttk.Label(self.opdesc_frame, text="SRC3 swizzle").grid(row=5, column=1, sticky="e", pady=3)
        ttk.Entry(self.opdesc_frame, textvariable=self.opdesc_src3_swizzle_var, width=12).grid(row=5, column=2, sticky="ew", padx=(4, 8), pady=3)

        help_text = (
            "Opdescs control write masks, source swizzles, and source negation. A lot of ADD/DP3/MUL-style edits need both the opcode word and the referenced opdesc changed.\n"
            "Mask uses xyzw. Swizzles use xyzw/xxxx/yxzw/etc. The flags word is preserved unless you change it manually."
        )
        ttk.Label(self.opdesc_frame, text=help_text, foreground="#555", wraplength=720, justify=tk.LEFT).grid(
            row=7, column=0, columnspan=5, sticky="w", pady=(16, 0)
        )
        for col in range(5):
            self.opdesc_frame.columnconfigure(col, weight=1)


    def _build_symbol_tab(self) -> None:
        ttk.Label(self.symbol_frame, text="Register Symbol Table Editor", font=("Segoe UI", 10, "bold")).grid(row=0, column=0, columnspan=5, sticky="w", pady=(0, 8))

        ttk.Label(self.symbol_frame, text="Scope/DVLE").grid(row=1, column=0, sticky="w", pady=3)
        self.symbol_scope_combo = ttk.Combobox(self.symbol_frame, textvariable=self.symbol_dvle_var, width=12, values=["global"])
        self.symbol_scope_combo.grid(row=1, column=1, sticky="ew", padx=(4, 8), pady=3)
        ttk.Label(self.symbol_frame, text="Register").grid(row=1, column=2, sticky="w", pady=3)
        self.symbol_register_combo = ttk.Combobox(self.symbol_frame, textvariable=self.symbol_register_var, width=24)
        self.symbol_register_combo.grid(row=1, column=3, sticky="ew", padx=(4, 0), pady=3)

        ttk.Label(self.symbol_frame, text="Symbol name").grid(row=2, column=0, sticky="w", pady=3)
        ttk.Entry(self.symbol_frame, textvariable=self.symbol_name_var).grid(row=2, column=1, columnspan=3, sticky="ew", padx=(4, 0), pady=3)
        ttk.Button(self.symbol_frame, text="Load Selected", command=self.load_selected_symbol_row).grid(row=2, column=4, sticky="ew", padx=(8, 0), pady=3)

        btns = ttk.Frame(self.symbol_frame)
        btns.grid(row=3, column=0, columnspan=5, sticky="ew", pady=(8, 8))
        ttk.Button(btns, text="Apply / Update Alias", command=self.apply_register_alias).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Delete Alias", command=self.delete_register_alias).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Export Symbol Map", command=self.export_symbol_map).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Import Symbol Map", command=self.import_symbol_map).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(btns, text="Refresh", command=self.show_symbol_tools).pack(side=tk.LEFT)

        self.symbol_tree = ttk.Treeview(self.symbol_frame, columns=("Scope", "Register", "Symbol", "Source"), show="headings", height=10)
        for col, width in [("Scope", 105), ("Register", 90), ("Symbol", 300), ("Source", 185)]:
            self.symbol_tree.heading(col, text=col)
            self.symbol_tree.column(col, width=width, anchor=tk.W)
        self.symbol_tree.grid(row=4, column=0, columnspan=4, sticky="nsew")
        self.symbol_tree.bind("<<TreeviewSelect>>", self.on_symbol_table_select)
        sy = ttk.Scrollbar(self.symbol_frame, orient=tk.VERTICAL, command=self.symbol_tree.yview)
        sy.grid(row=4, column=4, sticky="ns")
        self.symbol_tree.configure(yscrollcommand=sy.set)

        self.symbol_text = tk.Text(self.symbol_frame, wrap=tk.NONE, font=("Consolas", 9), height=7)
        self.symbol_text.grid(row=5, column=0, columnspan=4, sticky="nsew", pady=(8, 0))
        yscroll = ttk.Scrollbar(self.symbol_frame, orient=tk.VERTICAL, command=self.symbol_text.yview)
        yscroll.grid(row=5, column=4, sticky="ns", pady=(8, 0))
        self.symbol_text.configure(yscrollcommand=yscroll.set)

        help_text = (
            "This editor creates register aliases used by disassembly, direct ASM editing, field dropdowns, full ASM import/export, and reports. "
            "It does not create new hardware registers; it maps names onto existing PICA registers like c17, v0, o2, r3, b0, or i0."
        )
        ttk.Label(self.symbol_frame, text=help_text, foreground="#555", wraplength=860, justify=tk.LEFT).grid(row=6, column=0, columnspan=5, sticky="w", pady=(10, 0))
        self.symbol_frame.columnconfigure(1, weight=1)
        self.symbol_frame.columnconfigure(3, weight=2)
        self.symbol_frame.rowconfigure(4, weight=2)
        self.symbol_frame.rowconfigure(5, weight=1)

    def _build_cfg_tab(self) -> None:
        top = ttk.Frame(self.cfg_frame)
        top.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        ttk.Label(top, text="DVLE:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.cfg_dvle_var, width=6).pack(side=tk.LEFT, padx=(4, 8))
        ttk.Button(top, text="Refresh graph", command=self.refresh_cfg).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Show register lifetimes", command=self.show_register_lifetimes).pack(side=tk.LEFT)
        self.cfg_canvas = tk.Canvas(self.cfg_frame, bg="#10141b", highlightthickness=1, highlightbackground="#2b3240")
        self.cfg_canvas.grid(row=1, column=0, sticky="nsew")
        self.cfg_frame.rowconfigure(1, weight=1)
        self.cfg_frame.columnconfigure(0, weight=1)
        self.cfg_canvas.bind("<Configure>", lambda _e: self.refresh_cfg(redraw_only=True))

    def _build_statusbar(self) -> None:
        self.status_var = tk.StringVar()
        status = ttk.Label(self, textvariable=self.status_var, anchor=tk.W, padding=(4, 2), relief=tk.SUNKEN)
        status.pack(side=tk.BOTTOM, fill=tk.X)

    def _set_status(self, text: str) -> None:
        self.status_var.set(text)

    def _set_text(self, widget: tk.Text, text: str) -> None:
        widget.configure(state=tk.NORMAL)
        widget.delete("1.0", tk.END)
        widget.insert(tk.END, text)
        widget.configure(state=tk.DISABLED)

    def open_file(self) -> None:
        path = filedialog.askopenfilename(filetypes=[("3DS Shader Binary", "*.shbin *.bcsdr *.bin"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.load(path)
        except Exception as exc:
            messagebox.showerror("Open failed", str(exc))
            return
        self.refresh_tree()
        self.refresh_symbol_table()
        self.show_overview()
        self.preview.set_shader(self.parser)
        self._set_status(f"Loaded {os.path.basename(path)} | {len(self.parser.data):,} bytes | {len(self.parser.dvles)} DVLE(s)")

    def save_file(self) -> None:
        if not self._require_loaded():
            return
        if not self.parser.filename:
            self.save_file_as()
            return
        try:
            self.parser.save(self.parser.filename, make_backup=True)
            self._set_status(f"Saved {os.path.basename(self.parser.filename)} and created/updated .bak backup.")
        except Exception as exc:
            messagebox.showerror("Save failed", str(exc))

    def save_file_as(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.asksaveasfilename(defaultextension=".shbin", filetypes=[("Shader Binary", "*.shbin"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.save(path, make_backup=True)
            self._set_status(f"Saved {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Save As failed", str(exc))

    def export_json(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".shader.json").name if self.parser.filename else "shader.json"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".json", filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_json(path)
            self._set_status(f"Exported JSON to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Export failed", str(exc))

    def import_json_values(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            updated = self.parser.import_constant_values_json(path)
            self.refresh_tree()
            self.show_overview()
            self._set_status(f"Imported JSON values: updated {updated} constant(s). Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Import failed", str(exc))

    def export_csv(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".constants.csv").name if self.parser.filename else "constants.csv"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".csv", filetypes=[("CSV", "*.csv"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_constants_csv(path)
            self._set_status(f"Exported constants CSV to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("CSV export failed", str(exc))

    def export_disassembly(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".pica.asm").name if self.parser.filename else "shader.pica.asm"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".asm", filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_disassembly(path)
            self._set_status(f"Exported decoded instruction listing to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Disassembly export failed", str(exc))


    def export_full_asm(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".full.pica.asm").name if self.parser.filename else "shader.full.pica.asm"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".asm", filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_full_asm(path)
            self._set_status(f"Exported reassemblable full ASM to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Full ASM export failed", str(exc))

    def import_full_asm(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("Assembly text", "*.asm *.txt"), ("All files", "*.*")])
        if not path:
            return
        try:
            updated = self.parser.import_full_asm(path)
            self.refresh_tree()
            self.show_overview()
            self.preview.set_shader(self.parser)
            self.refresh_cfg(redraw_only=True)
            self._set_status(f"Imported full ASM: updated {updated} instruction(s). Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Full ASM import failed", str(exc))

    def _parse_symbol_scope(self, text: Optional[str] = None) -> Optional[int]:
        scope = (self.symbol_dvle_var.get() if text is None else str(text)).strip().lower()
        if scope in {"", "global", "all", "none"}:
            return None
        if scope.startswith("dvle:"):
            scope = scope.split(":", 1)[1]
        return int(scope, 0)

    def _active_dvle_for_instruction(self, inst_idx: Optional[int] = None) -> Optional[int]:
        if inst_idx is None:
            inst_idx = self.selected_instruction
        if inst_idx is None:
            return None
        for dvle in self.parser.dvles:
            if self.parser._instruction_in_dvle_range(int(inst_idx), dvle):
                return dvle.index
        try:
            dvle_idx = int(self.cfg_dvle_var.get().strip() or "0", 0)
            if 0 <= dvle_idx < len(self.parser.dvles):
                return dvle_idx
        except Exception:
            pass
        return 0 if self.parser.dvles else None

    def _labels_for_dvle(self, dvle_idx: Optional[int]) -> Dict[str, int]:
        if dvle_idx is None or not (0 <= int(dvle_idx) < len(self.parser.dvles)):
            return {}
        dvle = self.parser.dvles[int(dvle_idx)]
        labels: Dict[str, int] = {}
        for lab in dvle.labels:
            name = self.parser._label_display_name(lab)
            if name:
                labels[name] = lab.opcode_address
                labels[name.replace(" ", "_")] = lab.opcode_address
        return labels

    def _symbol_map_for_instruction(self, inst_idx: Optional[int] = None) -> Dict[str, str]:
        return self.parser.symbol_to_register_map(self._active_dvle_for_instruction(inst_idx))

    @staticmethod
    def _add_symbol_binding(symbol_map: Dict[str, str], symbol: str, register: str, *, prefer: bool = False) -> None:
        sym = str(symbol or "").strip()
        reg = native_register_from_display(register)
        if not sym or not reg:
            return

        def add_one(name: str) -> None:
            if not name:
                return
            if prefer:
                symbol_map[name] = reg
                symbol_map[name.replace(" ", "_")] = reg
            else:
                symbol_map.setdefault(name, reg)
                symbol_map.setdefault(name.replace(" ", "_"), reg)

        add_one(sym)
        stem, component_suffix = split_vector_component_suffix(sym)
        if component_suffix and stem and stem != sym:
            add_one(stem)

    def _symbol_map_for_asm_roundtrip(self, inst_idx: int, dvle_idx: Optional[int]) -> Dict[str, str]:
        merged: Dict[str, str] = {}
        if self.parser.dvlp and 0 <= int(inst_idx) < len(self.parser.dvlp.instructions):
            inst = self.parser.dvlp.instructions[int(inst_idx)]
            for ann in inst.fields.get("register_annotations", []) or []:
                self._add_symbol_binding(merged, ann.get("symbol", ""), ann.get("register", ""), prefer=True)
        for sym, reg in self.parser.symbol_to_register_map(dvle_idx).items():
            self._add_symbol_binding(merged, sym, reg, prefer=False)
        return merged

    def _resolve_register_field(self, text: str, kind: str = "src", inst_idx: Optional[int] = None) -> str:
        raw = str(text or "").strip()
        if not raw:
            return raw
        display = native_register_from_display(raw)
        if display != raw.lower():
            return display
        dvle_idx = self._active_dvle_for_instruction(inst_idx) if inst_idx is not None else None
        symbols = self._symbol_map_for_asm_roundtrip(inst_idx, dvle_idx) if inst_idx is not None else self._symbol_map_for_instruction()
        low_map = {str(k).lower(): v for k, v in symbols.items()}
        if raw in symbols:
            return symbols[raw]
        if raw.lower() in low_map:
            return low_map[raw.lower()]
        return raw

    def _display_register_field(self, register: str, dvle_idx: Optional[int]) -> str:
        return self.parser.register_display_name(register, dvle_idx)

    def _instruction_format_from_editor(self, inst_idx: Optional[int] = None) -> Tuple[Optional[int], str]:
        mnemonic = self.instr_mnemonic_var.get().strip().upper() if hasattr(self, "instr_mnemonic_var") else ""
        if mnemonic in MNEMONIC_TO_OPCODE:
            op = MNEMONIC_TO_OPCODE[mnemonic]
            return op, pica_instruction_format(op, is_word=False)
        if inst_idx is not None and self.parser.dvlp and 0 <= int(inst_idx) < len(self.parser.dvlp.instructions):
            inst = self.parser.dvlp.instructions[int(inst_idx)]
            return inst.opcode, inst.fmt
        return None, "unknown"

    def _used_instruction_dropdowns(self, opcode: Optional[int], fmt: str) -> set[str]:
        used: set[str] = set()
        if fmt in {"1", "1i"}:
            used.update({"DST", "SRC1", "SRC2"})
        elif fmt == "1u":
            used.update({"DST", "SRC1"})
        elif fmt == "1c":
            used.update({"SRC1", "SRC2", "CmpX", "CmpY"})
        elif fmt == "2":
            # CALL is unconditional. The other format-2 flow ops use cond/ref bits.
            if opcode in {0x23, 0x25, 0x28, 0x2C}:
                used.add("CondOp")
        elif fmt == "3":
            # IFU/CALLU/JMPU use bN; LOOP uses iN.
            used.add("Bool/Int ID")
        elif fmt in {"5", "5i"}:
            used.update({"DST", "SRC1", "SRC2", "SRC3"})
        return used

    def _refresh_instruction_register_choices(self, inst_idx: Optional[int] = None) -> None:
        if not hasattr(self, "instr_register_widgets"):
            return
        dvle_idx = self._active_dvle_for_instruction(inst_idx)
        opcode, fmt = self._instruction_format_from_editor(inst_idx)
        used_dropdowns = self._used_instruction_dropdowns(opcode, fmt)

        def src_slot_kind(label: str) -> str:
            # PICA has mixed 5-bit and 7-bit source fields. Only 7-bit fields can hold cN constants.
            if fmt in {"1", "1u", "1c"}:
                return "src" if label == "SRC1" else "src5"
            if fmt == "1i":
                return "src5" if label == "SRC1" else "src"
            if fmt == "5":
                return "src" if label == "SRC2" else "src5"
            if fmt == "5i":
                return "src" if label == "SRC3" else "src5"
            return "src"

        for label, combo in self.instr_register_widgets.items():
            if label == "DST":
                combo.configure(values=self.parser.register_display_choices(dvle_idx, "dst"))
            elif label in {"SRC1", "SRC2", "SRC3"}:
                combo.configure(values=self.parser.register_display_choices(dvle_idx, src_slot_kind(label)))
            elif label == "Bool/Int ID":
                combo.configure(values=self.parser.register_display_choices(dvle_idx, "uniform"))
            elif label == "CondOp":
                combo.configure(values=[CONDOP_NAMES[i] for i in sorted(CONDOP_NAMES)])
            elif label in {"CmpX", "CmpY"}:
                combo.configure(values=[CMP_OP_NAMES[i] for i in sorted(CMP_OP_NAMES)])

            combo.configure(state="normal" if label in used_dropdowns else "disabled")


    def _refresh_symbol_editor_choices(self) -> None:
        if self.symbol_scope_combo is not None:
            scopes = ["global"] + [str(dvle.index) for dvle in self.parser.dvles]
            self.symbol_scope_combo.configure(values=scopes)
        if self.symbol_register_combo is not None:
            dvle_idx = self._parse_symbol_scope()
            choices = []
            choices.extend(self.parser.register_display_choices(dvle_idx, "src"))
            choices.extend(self.parser.register_display_choices(dvle_idx, "dst"))
            choices.extend(self.parser.register_display_choices(dvle_idx, "uniform"))
            seen = set()
            unique = []
            for choice in choices:
                key = native_register_from_display(choice)
                if key not in seen:
                    seen.add(key)
                    unique.append(choice)
            self.symbol_register_combo.configure(values=unique)

    def _detected_symbol_rows(self) -> List[Tuple[str, str, str, str]]:
        rows: List[Tuple[str, str, str, str]] = []
        for dvle in self.parser.dvles:
            scope = str(dvle.index)
            for inp in dvle.inputs:
                lo, hi = sorted((inp.start, inp.end))
                for reg_num in range(lo, hi + 1):
                    name = inp.name if lo == hi else f"{inp.name}[{reg_num - lo}]"
                    if name:
                        rows.append((scope, f"v{reg_num}", name, "Input Register Table"))
            for out in dvle.outputs:
                rows.append((scope, f"o{out.register_id}", OUTPUT_TYPES.get(out.output_type, f"output_{out.output_type}"), "Output Register Table"))
            for c in dvle.constants:
                if c.display_name and c.display_name != c.register_name:
                    rows.append((scope, c.register_name, c.display_name, "Constant Table"))
        return rows

    def refresh_symbol_table(self) -> None:
        if self.symbol_tree is None:
            return
        self.symbol_tree.delete(*self.symbol_tree.get_children())
        maps = self.parser._symbol_maps()
        for scope, regs in sorted(maps.items()):
            shown_scope = "global" if scope == "global" else scope.split(":", 1)[-1]
            for reg, sym in sorted(regs.items()):
                if not sym:
                    continue
                iid = f"alias:{shown_scope}:{reg}"
                self.symbol_tree.insert("", "end", iid=iid, values=(shown_scope, reg, sym, "User Alias"))
        for i, (scope, reg, sym, source) in enumerate(self._detected_symbol_rows()):
            iid = f"detected:{i}"
            self.symbol_tree.insert("", "end", iid=iid, values=(scope, reg, sym, source))
        self._refresh_symbol_editor_choices()

    def load_selected_symbol_row(self) -> None:
        if self.symbol_tree is None:
            return
        sel = self.symbol_tree.selection()
        if not sel:
            return
        vals = self.symbol_tree.item(sel[0], "values")
        if len(vals) >= 3:
            self.symbol_dvle_var.set(str(vals[0]))
            self.symbol_register_var.set(str(vals[1]))
            self.symbol_name_var.set(str(vals[2]))
            self._refresh_symbol_editor_choices()

    def on_symbol_table_select(self, _event: Any = None) -> None:
        self.load_selected_symbol_row()

    def delete_register_alias(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = self._parse_symbol_scope()
            self.parser.remove_register_alias(self.symbol_register_var.get(), dvle_idx)
            self.refresh_tree()
            self.show_symbol_tools()
            self.preview.set_shader(self.parser)
            self._set_status("Register alias deleted from the symbol map.")
        except Exception as exc:
            messagebox.showerror("Delete alias failed", str(exc))

    def export_symbol_map(self) -> None:
        if not self._require_loaded():
            return
        default = Path(self.parser.filename).with_suffix(".register_symbols.json").name if self.parser.filename else "register_symbols.json"
        path = filedialog.asksaveasfilename(initialfile=default, defaultextension=".json", filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            self.parser.export_register_symbol_map(path)
            self.show_symbol_tools()
            self._set_status(f"Exported register symbol map to {os.path.basename(path)}.")
        except Exception as exc:
            messagebox.showerror("Symbol map export failed", str(exc))

    def import_symbol_map(self) -> None:
        if not self._require_loaded():
            return
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        try:
            count = self.parser.import_register_symbol_map(path)
            self.refresh_tree()
            self.show_symbol_tools()
            self.preview.set_shader(self.parser)
            self._set_status(f"Imported {count} register symbol alias(es).")
        except Exception as exc:
            messagebox.showerror("Symbol map import failed", str(exc))

    def show_symbol_tools(self) -> None:
        if not self._require_loaded():
            return
        self.refresh_symbol_table()
        lines = ["Register Symbol Map", ""]
        maps = self.parser._symbol_maps()
        for scope, regs in maps.items():
            lines.append(f"[{scope}]")
            if regs:
                for reg, sym in sorted(regs.items()):
                    lines.append(f"  {reg:6} = {sym}")
            else:
                lines.append("  <empty>")
            lines.append("")
        lines.append("Detected register-backed symbols available to ASM/dropdowns:")
        for scope, reg, sym, source in self._detected_symbol_rows():
            lines.append(f"  DVLE {scope:>2}  {reg:<6} = {sym}  [{source}]")
        self.symbol_text.configure(state=tk.NORMAL)
        self.symbol_text.delete("1.0", tk.END)
        self.symbol_text.insert(tk.END, "\n".join(lines))
        self.symbol_text.configure(state=tk.DISABLED)
        self.notebook.select(self.symbol_frame)

    def apply_register_alias(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = self._parse_symbol_scope()
            self.parser.set_register_alias(self.symbol_register_var.get(), self.symbol_name_var.get(), dvle_idx)
            self.refresh_tree()
            self.show_symbol_tools()
            self._refresh_instruction_register_choices()
            self.preview.set_shader(self.parser)
            self._set_status("Register alias applied to the symbol map.")
        except Exception as exc:
            messagebox.showerror("Alias failed", str(exc))

    def show_register_lifetimes(self) -> None:
        if not self._require_loaded():
            return
        try:
            dvle_idx = int(self.analysis_dvle_var.get().strip() or self.cfg_dvle_var.get().strip() or "0", 0)
        except Exception:
            dvle_idx = 0
        self.analysis_dvle_var.set(str(dvle_idx))
        self._set_text(self.analysis_text, self.parser.register_lifetime_report(dvle_idx))
        self.notebook.select(self.analysis_text.master)

    def refresh_cfg(self, redraw_only: bool = False) -> None:
        if not hasattr(self, "cfg_canvas"):
            return
        self.cfg_canvas.delete("all")
        if not self.parser.loaded or not self.parser.dvlp:
            self.cfg_canvas.create_text(24, 24, anchor=tk.NW, text="Open a shader to view the control-flow graph.", fill="#d0d7e2", font=("Segoe UI", 11, "bold"))
            return
        try:
            dvle_idx = int(self.cfg_dvle_var.get().strip() or "0", 0)
        except Exception:
            dvle_idx = 0
            self.cfg_dvle_var.set("0")
        graph = self.parser.control_flow_graph(dvle_idx)
        nodes = graph.get("nodes", [])
        edges = graph.get("edges", [])
        w = max(600, int(self.cfg_canvas.winfo_width()))
        h = max(420, int(self.cfg_canvas.winfo_height()))
        self.cfg_canvas.create_rectangle(0, 0, w, h, fill="#10141b", outline="")
        if not nodes:
            self.cfg_canvas.create_text(24, 24, anchor=tk.NW, text="No graph nodes decoded.", fill="#d0d7e2")
            return
        node_w, node_h = 220, 54
        x_gap = max(40, (w - node_w) // 2)
        y_gap = 88
        positions: Dict[int, Tuple[int, int]] = {}
        for i, node in enumerate(nodes):
            x = x_gap + (40 if i % 2 else -40)
            y = 30 + i * y_gap
            positions[int(node["start"])] = (x, y)
        for edge in edges:
            src = int(edge.get("from", 0)); dst = int(edge.get("to", 0))
            if src not in positions:
                continue
            dst_start = dst if dst in positions else next((int(n["start"]) for n in nodes if int(n["start"]) >= dst), None)
            if dst_start is None or dst_start not in positions:
                continue
            x1, y1 = positions[src]
            x2, y2 = positions[dst_start]
            sx, sy = x1 + node_w // 2, y1 + node_h
            tx, ty = x2 + node_w // 2, y2
            color = "#6fb2ff" if edge.get("kind") != "fallthrough" else "#73808f"
            self.cfg_canvas.create_line(sx, sy, tx, ty, fill=color, arrow=tk.LAST, width=2, smooth=True)
            self.cfg_canvas.create_text((sx + tx) / 2 + 8, (sy + ty) / 2, text=str(edge.get("kind", "")), fill=color, anchor=tk.W, font=("Segoe UI", 8))
        for node in nodes:
            x, y = positions[int(node["start"])]
            label = f"{node.get('label')}\n{int(node['start']):04d}..{int(node['end']):04d}"
            self.cfg_canvas.create_rectangle(x, y, x + node_w, y + node_h, fill="#1b2533", outline="#86a8d8", width=2)
            self.cfg_canvas.create_text(x + 10, y + 8, anchor=tk.NW, text=label, fill="#eef5ff", font=("Consolas", 10, "bold"))
        if not redraw_only:
            self.notebook.select(self.cfg_frame)
        self._set_status(f"Control-flow graph refreshed for DVLE {graph.get('dvle', dvle_idx)}: {len(nodes)} block(s), {len(edges)} edge(s).")

    def show_validation(self) -> None:
        if not self._require_loaded():
            return
        self._set_text(self.details_text, self.parser.validation_report())
        self.notebook.select(0)

    def _require_loaded(self) -> bool:
        if not self.parser.loaded:
            messagebox.showinfo("No file loaded", "Open a .shbin file first.")
            return False
        return True

    def refresh_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        self.item_ranges.clear()
        if not self.parser.loaded:
            return

        needle = self.filter_var.get().strip().lower()
        terms = [t for t in needle.split() if t]

        root = self.tree.insert("", "end", iid="dvlb", text="DVLB Header", values=("Header", f"{len(self.parser.dvles)} DVLE(s)"), open=True)
        self.item_ranges["dvlb"] = (0, min(0x40, len(self.parser.data)))

        if self.parser.dvlp:
            d = self.parser.dvlp
            dvlp_item = self.tree.insert("", "end", iid="dvlp", text="DVLP Program", values=("Program", f"{d.opcode_count} opcodes / {d.opdesc_count} opdescs"), open=True)
            self.item_ranges["dvlp"] = (d.offset, max(d.size, 0x28))
            self.tree.insert(dvlp_item, "end", iid="dvlp_header", text="Header", values=("Header", f"0x{d.offset:X}"))
            self.item_ranges["dvlp_header"] = (d.offset, 0x28)

            instr_parent = self.tree.insert(dvlp_item, "end", iid="dvlp_instructions", text="Decoded Instructions", values=("Code", f"{len(d.instructions)} instruction(s)"), open=True)
            self.item_ranges["dvlp_instructions"] = (d.offset + d.opcode_offset, d.opcode_count * 4)
            self.tree.insert(dvlp_item, "end", iid="dvlp_opcodes", text="Raw Opcode Table", values=("Table", f"{d.opcode_count} x 4 bytes"))
            self.item_ranges["dvlp_opcodes"] = (d.offset + d.opcode_offset, d.opcode_count * 4)
            current_block_parent = None
            current_block_name = ""
            current_block_hay = ""

            for inst in d.instructions:
                ann_disasm = inst.fields.get("annotated_disasm", inst.disasm)
                labels_here = ", ".join(x.get("name", "") for x in inst.fields.get("labels_here", []) if x.get("name"))

                if labels_here or current_block_parent is None:
                    current_block_name = labels_here or f"entry_{inst.index:04d}"
                    current_block_hay = f"{current_block_name} label block instruction group".lower()
                    block_id = f"inst_block:{inst.index}"
                    current_block_parent = self.tree.insert(
                        instr_parent,
                        "end",
                        iid=block_id,
                        text=current_block_name,
                        values=("Label" if labels_here else "Block", f"starts at instruction {inst.index}"),
                        open=True,
                    )
                    self.item_ranges[block_id] = (inst.offset, 4)

                hay = " ".join([inst.disasm, str(ann_disasm), labels_here, current_block_hay, inst.mnemonic, inst.fmt, f"0x{inst.word:08X}"]).lower()
                if terms and not all(term in hay for term in terms):
                    continue

                item_id = f"inst:{inst.index}"
                display_disasm = str(ann_disasm)
                self.tree.insert(
                    current_block_parent,
                    "end",
                    iid=item_id,
                    text=f"{inst.index:04d}: {display_disasm}",
                    values=(inst.fmt, f"0x{inst.word:08X}"),
                )
                self.item_ranges[item_id] = (inst.offset, 4)

            opdesc_parent = self.tree.insert(dvlp_item, "end", iid="dvlp_opdescs", text="Operand Descriptors", values=("Table", f"{d.opdesc_count} x 8 bytes"), open=True)
            self.item_ranges["dvlp_opdescs"] = (d.offset + d.opdesc_offset, d.opdesc_count * 8)
            for i, (desc, flags) in enumerate(d.opdescs):
                dec = pica_decode_opdesc(desc, flags)
                info = f"mask={dec['dest_mask']} s1={'-' if dec['src1_neg'] else ''}{dec['src1_swizzle']} s2={'-' if dec['src2_neg'] else ''}{dec['src2_swizzle']} s3={'-' if dec['src3_neg'] else ''}{dec['src3_swizzle']}"
                hay = f"opdesc {i} 0x{desc:08x} 0x{flags:08x} {info}".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"opdesc:{i}"
                self.tree.insert(opdesc_parent, "end", iid=item_id, text=f"Opdesc {i:03d}", values=("Opdesc", info))
                self.item_ranges[item_id] = (d.offset + d.opdesc_offset + i * 8, 8)

            self.tree.insert(dvlp_item, "end", iid="dvlp_lines", text="Line Number Table", values=("Table", f"{d.line_count} x 8 bytes"))
            self.item_ranges["dvlp_lines"] = (d.offset + d.line_offset, d.line_count * 8)
            self.tree.insert(dvlp_item, "end", iid="dvlp_filenames", text="Source Filename Symbols", values=("Symbols", f"{len(d.filenames)} strings"))
            self.item_ranges["dvlp_filenames"] = (d.offset + d.filename_symbol_offset, d.filename_symbol_size)

        for dvle in self.parser.dvles:
            dvle_item = self.tree.insert("", "end", iid=f"dvle:{dvle.index}", text=f"DVLE {dvle.index} ({dvle.shader_type_name})", values=("Shader", f"entry {dvle.opcode_entry} end {dvle.opcode_end}"), open=True)
            self.item_ranges[f"dvle:{dvle.index}"] = (dvle.offset, max(dvle.size, 0x40))

            self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:header", text="Header", values=("Header", f"0x{dvle.offset:X}"))
            self.item_ranges[f"dvle:{dvle.index}:header"] = (dvle.offset, 0x40)

            const_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:constants", text="Constants", values=("Table", f"{len(dvle.constants)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:constants"] = (dvle.offset + dvle.const_offset, dvle.const_count * 0x14)
            for c in dvle.constants:
                hay = " ".join([c.display_name, c.register_name, self.parser.register_alias(c.register_name, dvle.index), c.type_name, str(c.values_for_display)]).lower()
                if terms and not all(term in hay for term in terms):
                    continue
                preview = self._constant_preview(c)
                item_id = f"const:{dvle.index}:{c.index}"
                self.tree.insert(const_parent, "end", iid=item_id, text=c.display_name, values=(c.type_name, f"{c.register_name}  {preview}"))
                self.item_ranges[item_id] = (c.offset, 0x14)

            inputs_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:inputs", text="Input Register Table", values=("Table", f"{len(dvle.inputs)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:inputs"] = (dvle.offset + dvle.input_offset, dvle.input_count * 8)
            for inp in dvle.inputs:
                hay = f"{inp.name} 0x{inp.start:02x} 0x{inp.end:02x} input register table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"input:{dvle.index}:{inp.index}"
                self.tree.insert(inputs_parent, "end", iid=item_id, text=inp.name or f"input_{inp.index}", values=("Input", f"regs 0x{inp.start:02X}..0x{inp.end:02X}"))
                self.item_ranges[item_id] = (inp.offset, 8)

            outputs_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:outputs", text="Output Register Table", values=("Table", f"{len(dvle.outputs)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:outputs"] = (dvle.offset + dvle.output_offset, dvle.output_count * 8)
            for out in dvle.outputs:
                type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
                hay = f"{type_name} o{out.register_id} {component_mask(out.mask)} output register table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"output:{dvle.index}:{out.index}"
                self.tree.insert(outputs_parent, "end", iid=item_id, text=type_name, values=("Output", f"o{out.register_id} mask={component_mask(out.mask)}"))
                self.item_ranges[item_id] = (out.offset, 8)

            labels_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:labels", text="Label Table", values=("Table", f"{len(dvle.labels)} entries"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:labels"] = (dvle.offset + dvle.label_offset, dvle.label_count * 0x10)
            for lab in dvle.labels:
                label_name = self.parser._label_display_name(lab)
                hay = f"{label_name} {lab.label_id} {lab.opcode_address} label table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"label:{dvle.index}:{lab.index}"
                self.tree.insert(labels_parent, "end", iid=item_id, text=label_name, values=("Label", f"id={lab.label_id} target={lab.opcode_address}"))
                self.item_ranges[item_id] = (lab.offset, 0x10)

            symbols_parent = self.tree.insert(dvle_item, "end", iid=f"dvle:{dvle.index}:symbols", text="Symbol Table", values=("Symbols", f"{len(dvle.symbols)} strings"), open=True)
            self.item_ranges[f"dvle:{dvle.index}:symbols"] = (dvle.offset + dvle.symbol_offset, dvle.symbol_size)
            for sym_i, (rel, text) in enumerate(dvle.symbols):
                hay = f"{text} 0x{rel:04x} symbol table".lower()
                if terms and not all(term in hay for term in terms):
                    continue
                item_id = f"symbol:{dvle.index}:{sym_i}"
                self.tree.insert(symbols_parent, "end", iid=item_id, text=text or f"symbol_{sym_i}", values=("Symbol", f"rel=0x{rel:04X}"))
                self.item_ranges[item_id] = (dvle.offset + dvle.symbol_offset + rel, max(1, len(text) + 1))

        if needle:
            self._set_status(f"Filter active: {needle!r}")

    def _constant_preview(self, c: ShaderConstant) -> str:
        if c.entry_type == 2:
            vals = [pica24_to_float(x) for x in c.raw]
            return "(" + ", ".join(f"{v:.5g}" for v in vals) + ")"
        if c.entry_type == 0:
            return "true" if c.raw[0] else "false"
        return "(" + ", ".join(str(v) for v in c.raw[:4]) + ")"

    def on_tree_select(self, _event: Any = None) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        item = sel[0]
        self.selected_constant = None
        self.selected_instruction = None
        self.selected_opdesc = None
        if item.startswith("const:"):
            _, dvle_s, const_s = item.split(":")
            self.selected_constant = (int(dvle_s), int(const_s))
            self.preview.set_selection(dvle_idx=int(dvle_s), inst_idx=None)
            self.show_constant(int(dvle_s), int(const_s))
            return
        if item.startswith("inst:"):
            _, inst_s = item.split(":")
            self.selected_instruction = int(inst_s)
            self.preview.set_selection(inst_idx=int(inst_s))
            self.show_instruction(int(inst_s))
            return
        if item.startswith("opdesc:"):
            _, opdesc_s = item.split(":")
            self.selected_opdesc = int(opdesc_s)
            self.preview.set_selection(inst_idx=None)
            self.show_opdesc(int(opdesc_s))
            return
        if item.startswith("dvle:"):
            try:
                self.preview.set_selection(dvle_idx=int(item.split(":")[1]), inst_idx=None)
            except Exception:
                pass
        self.show_item(item)

    def show_overview(self) -> None:
        lines = []
        lines.append(f"File: {self.parser.filename}")
        lines.append(f"Size: 0x{len(self.parser.data):X} ({len(self.parser.data):,} bytes)")
        lines.append(f"DVLE count: {len(self.parser.dvles)}")
        lines.append("")
        if self.parser.dvlp:
            d = self.parser.dvlp
            lines.append("DVLP Program")
            lines.append(f"  Offset: 0x{d.offset:X}")
            lines.append(f"  Version: 0x{d.version:04X}")
            lines.append(f"  Opcode table: 0x{d.offset + d.opcode_offset:X}, count={d.opcode_count}")
            lines.append(f"  Opdesc table: 0x{d.offset + d.opdesc_offset:X}, count={d.opdesc_count}")
            lines.append(f"  Line table: 0x{d.offset + d.line_offset:X}, count={d.line_count}")
            lines.append(f"  Filename symbols: 0x{d.offset + d.filename_symbol_offset:X}, size={d.filename_symbol_size}")
            lines.append("")
        for dvle in self.parser.dvles:
            lines.append(f"DVLE {dvle.index} ({dvle.shader_type_name}) @ 0x{dvle.offset:X}")
            lines.append(f"  Entrypoint: {dvle.opcode_entry}  End: {dvle.opcode_end}")
            lines.append(f"  Constants: {len(dvle.constants)}  Inputs: {len(dvle.inputs)}  Outputs: {len(dvle.outputs)}  Labels: {len(dvle.labels)}")
        lines.append("")
        lines.append(self.parser.validation_report())
        self._set_text(self.details_text, "\n".join(lines))
        self._set_text(self.raw_text, json.dumps(self.parser.to_dict(), indent=2))
        self._set_text(self.hex_text, hexdump(self.parser.data, 0, min(0x200, len(self.parser.data))))
        if hasattr(self, "preview"):
            self.preview.redraw()

    def show_item(self, item: str) -> None:
        details = self._details_for_item(item)
        self._set_text(self.details_text, details)
        start, size = self.item_ranges.get(item, (0, min(0x100, len(self.parser.data))))
        self._set_text(self.hex_text, hexdump(self.parser.data, start, min(max(size, 0x80), 0x1000)))
        self._set_text(self.raw_text, self._raw_table_for_item(item))
        self.notebook.select(0)
        self._clear_edit_tab()

    def _details_for_item(self, item: str) -> str:
        if item.startswith("input:"):
            _, dvle_s, inp_s = item.split(":")
            return self._single_input_details(self.parser.dvles[int(dvle_s)], int(inp_s))
        if item.startswith("output:"):
            _, dvle_s, out_s = item.split(":")
            return self._single_output_details(self.parser.dvles[int(dvle_s)], int(out_s))
        if item.startswith("label:"):
            _, dvle_s, lab_s = item.split(":")
            return self._single_label_details(self.parser.dvles[int(dvle_s)], int(lab_s))
        if item.startswith("symbol:"):
            _, dvle_s, sym_s = item.split(":")
            return self._single_symbol_details(self.parser.dvles[int(dvle_s)], int(sym_s))
        if item == "dvlb":
            return "\n".join([
                "DVLB Header",
                f"Magic: DVLB",
                f"DVLE count: {len(self.parser.dvle_offsets)}",
                "DVLE offsets: " + ", ".join(f"0x{x:X}" for x in self.parser.dvle_offsets),
                f"DVLP expected offset: 0x{8 + len(self.parser.dvle_offsets) * 4:X}",
            ])
        if item.startswith("dvlp"):
            return self._dvlp_details(item)
        if item.startswith("dvle:"):
            parts = item.split(":")
            dvle = self.parser.dvles[int(parts[1])]
            if len(parts) == 2 or parts[2] == "header":
                return self._dvle_header_details(dvle)
            if parts[2] == "inputs":
                return self._inputs_details(dvle)
            if parts[2] == "outputs":
                return self._outputs_details(dvle)
            if parts[2] == "labels":
                return self._labels_details(dvle)
            if parts[2] == "symbols":
                return self._symbols_details("DVLE Symbols", dvle.symbols, dvle.offset + dvle.symbol_offset)
            if parts[2] == "constants":
                return self._constants_details(dvle)
        return self.parser.validation_report()

    def _dvlp_details(self, item: str) -> str:
        d = self.parser.dvlp
        if not d:
            return "No DVLP parsed."
        lines = [
            "DVLP Program Opcodes/Opdescs",
            f"Offset: 0x{d.offset:X}",
            f"Version/type: 0x{d.version:04X}",
            f"Unknown: 0x{d.unknown:04X}",
            f"Opcode table: rel=0x{d.opcode_offset:X}, abs=0x{d.offset + d.opcode_offset:X}, count={d.opcode_count}",
            f"Opdesc table: rel=0x{d.opdesc_offset:X}, abs=0x{d.offset + d.opdesc_offset:X}, count={d.opdesc_count}",
            f"Line table: rel=0x{d.line_offset:X}, abs=0x{d.offset + d.line_offset:X}, count={d.line_count}",
            f"Filename symbols: rel=0x{d.filename_symbol_offset:X}, abs=0x{d.offset + d.filename_symbol_offset:X}, size={d.filename_symbol_size}",
            "",
        ]
        if item in {"dvlp_opcodes", "dvlp_instructions"}:
            lines.append(self._opcodes_details(d))
        elif item == "dvlp_opdescs":
            lines.append(self._opdescs_details(d))
        elif item == "dvlp_lines":
            lines.append(self._line_details(d))
        elif item == "dvlp_filenames":
            lines.append(self._symbols_details("DVLP Filename Symbols", d.filenames, d.offset + d.filename_symbol_offset))
        else:
            lines.append("Select Opcode Table, Opdesc Table, Line Number Table, or Source Filename Symbols to inspect their contents.")
        return "\n".join(lines)

    def _opcodes_details(self, d: DVLPInfo, limit: int = 512) -> str:
        lines = ["Opcode Table", "index  abs_off   word"]
        base = d.offset + d.opcode_offset
        for i, opcode in enumerate(d.opcodes[:limit]):
            lines.append(f"{i:04d}   0x{base + i * 4:06X}  0x{opcode:08X}")
        if len(d.opcodes) > limit:
            lines.append(f"... truncated in viewer; JSON export contains all {len(d.opcodes)} opcodes.")
        return "\n".join(lines)

    def _opdescs_details(self, d: DVLPInfo, limit: int = 512) -> str:
        lines = ["Opdesc Table", "index  abs_off   desc        flags"]
        base = d.offset + d.opdesc_offset
        for i, (desc, flags) in enumerate(d.opdescs[:limit]):
            lines.append(f"{i:04d}   0x{base + i * 8:06X}  0x{desc:08X}  0x{flags:08X}")
        if len(d.opdescs) > limit:
            lines.append(f"... truncated in viewer; JSON export contains all {len(d.opdescs)} opdescs.")
        return "\n".join(lines)

    def _line_details(self, d: DVLPInfo) -> str:
        if not d.lines:
            return "Line Number Table is empty."
        lines = ["Line Number Table", "index  file_off  line  filename"]
        for i, (file_off, line, filename) in enumerate(d.lines):
            lines.append(f"{i:04d}   0x{file_off:04X}    {line:<5} {filename}")
        return "\n".join(lines)

    def _dvle_header_details(self, dvle: DVLEInfo) -> str:
        return "\n".join([
            f"DVLE {dvle.index} Header",
            f"Offset: 0x{dvle.offset:X}",
            f"Version/type: 0x{dvle.version:04X}",
            f"Shader type: {dvle.shader_type_name} ({dvle.shader_type})",
            f"Opcode entry address: {dvle.opcode_entry}",
            f"Opcode end address: {dvle.opcode_end}",
            f"Unknown 0x10: 0x{dvle.unknown_10:08X}",
            f"Unknown 0x14: 0x{dvle.unknown_14:08X}",
            f"Constant table: rel=0x{dvle.const_offset:X}, abs=0x{dvle.offset + dvle.const_offset:X}, count={dvle.const_count}",
            f"Label table: rel=0x{dvle.label_offset:X}, abs=0x{dvle.offset + dvle.label_offset:X}, count={dvle.label_count}",
            f"Output table: rel=0x{dvle.output_offset:X}, abs=0x{dvle.offset + dvle.output_offset:X}, count={dvle.output_count}",
            f"Input table: rel=0x{dvle.input_offset:X}, abs=0x{dvle.offset + dvle.input_offset:X}, count={dvle.input_count}",
            f"Symbol table: rel=0x{dvle.symbol_offset:X}, abs=0x{dvle.offset + dvle.symbol_offset:X}, size={dvle.symbol_size}",
        ])

    def _constants_details(self, dvle: DVLEInfo) -> str:
        lines = ["Constants", "idx  offset    type      reg  name                         values"]
        for c in dvle.constants:
            lines.append(f"{c.index:03d}  0x{c.offset:06X}  {c.type_name:<8} {c.register_name:<4} {c.display_name:<28} {self._constant_preview(c)}")
        return "\n".join(lines)

    def _inputs_details(self, dvle: DVLEInfo) -> str:
        lines = ["Input Register Table", "idx  offset    start end   name"]
        for inp in dvle.inputs:
            lines.append(f"{inp.index:03d}  0x{inp.offset:06X}  0x{inp.start:02X}  0x{inp.end:02X}  {inp.name}")
        return "\n".join(lines)

    def _outputs_details(self, dvle: DVLEInfo) -> str:
        lines = ["Output Register Table", "idx  offset    type                  reg  mask  unknown"]
        for out in dvle.outputs:
            type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
            lines.append(f"{out.index:03d}  0x{out.offset:06X}  {type_name:<21} {out.register_id:<4} {component_mask(out.mask):<5} 0x{out.unknown:04X}")
        return "\n".join(lines)

    def _labels_details(self, dvle: DVLEInfo) -> str:
        lines = ["Label Table", "idx  offset    id  opcode_addr  name"]
        for lab in dvle.labels:
            lines.append(f"{lab.index:03d}  0x{lab.offset:06X}  {lab.label_id:<3} {lab.opcode_address:<12} {lab.name}")
        return "\n".join(lines)

    def _symbols_details(self, title: str, symbols: List[Tuple[int, str]], base_abs: int) -> str:
        lines = [title, "rel_off  abs_off   string"]
        for rel, text in symbols:
            lines.append(f"0x{rel:04X}   0x{base_abs + rel:06X}  {text}")
        if len(lines) == 2:
            lines.append("<empty>")
        return "\n".join(lines)

    def _single_input_details(self, dvle: DVLEInfo, inp_idx: int) -> str:
        inp = dvle.inputs[inp_idx]
        used_by = []
        if self.parser.dvlp:
            for inst in self.parser.dvlp.instructions:
                for ann in inst.fields.get("register_annotations", []):
                    if ann.get("dvle") == dvle.index and ann.get("input_index") == inp.index:
                        used_by.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Input Register: {inp.name or f'input_{inp.index}'}",
            f"DVLE: {dvle.index}",
            f"Index: {inp.index}",
            f"Entry offset: 0x{inp.offset:X}",
            f"Name symbol offset: 0x{inp.name_offset:X}",
            f"Register range: 0x{inp.start:02X}..0x{inp.end:02X}",
            "",
            "Decoded instructions using this input/register range:",
        ]
        lines.extend(used_by or ["  <none detected>"])
        return "\n".join(lines)

    def _single_output_details(self, dvle: DVLEInfo, out_idx: int) -> str:
        out = dvle.outputs[out_idx]
        type_name = OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}")
        used_by = []
        if self.parser.dvlp:
            for inst in self.parser.dvlp.instructions:
                for ann in inst.fields.get("register_annotations", []):
                    if ann.get("dvle") == dvle.index and ann.get("kind") == "output" and ann.get("table_index") == out.index:
                        used_by.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Output Register: {type_name}",
            f"DVLE: {dvle.index}",
            f"Index: {out.index}",
            f"Entry offset: 0x{out.offset:X}",
            f"Register: o{out.register_id}",
            f"Mask: {component_mask(out.mask)}",
            f"Unknown: 0x{out.unknown:04X}",
            "",
            "Decoded instructions writing this output:",
        ]
        lines.extend(used_by or ["  <none detected>"])
        return "\n".join(lines)

    def _single_label_details(self, dvle: DVLEInfo, lab_idx: int) -> str:
        lab = dvle.labels[lab_idx]
        label_name = self.parser._label_display_name(lab)
        target_inst = None
        refs = []
        if self.parser.dvlp:
            if 0 <= lab.opcode_address < len(self.parser.dvlp.instructions):
                target_inst = self.parser.dvlp.instructions[lab.opcode_address]
            for inst in self.parser.dvlp.instructions:
                for target in inst.fields.get("target_annotations", []):
                    if target.get("dvle") == dvle.index and target.get("label_index") == lab.index:
                        refs.append(f"  {inst.index:04d}: {inst.fields.get('annotated_disasm', inst.disasm)}")
                        break
        lines = [
            f"Label: {label_name}",
            f"DVLE: {dvle.index}",
            f"Index: {lab.index}",
            f"Entry offset: 0x{lab.offset:X}",
            f"Label ID: {lab.label_id}",
            f"Opcode address: {lab.opcode_address}",
            f"Name symbol offset: 0x{lab.name_offset:X}",
            f"Unknown A: {lab.unknown_a.hex(' ').upper()}",
            f"Unknown B: 0x{lab.unknown_b:08X}",
            "",
            "Target instruction:",
            f"  {target_inst.index:04d}: {target_inst.fields.get('annotated_disasm', target_inst.disasm)}" if target_inst else "  <outside decoded opcode table>",
            "",
            "Instructions referencing this label:",
        ]
        lines.extend(refs or ["  <none detected>"])
        return "\n".join(lines)

    def _single_symbol_details(self, dvle: DVLEInfo, sym_idx: int) -> str:
        rel, text = dvle.symbols[sym_idx]
        refs = []
        for inp in dvle.inputs:
            if inp.name_offset == rel:
                refs.append(f"Input[{inp.index}] regs 0x{inp.start:02X}..0x{inp.end:02X}")
        for lab in dvle.labels:
            if lab.name_offset == rel:
                refs.append(f"Label[{lab.index}] id={lab.label_id} opcode={lab.opcode_address}")
        for c in dvle.constants:
            if c.mapped_input == text or c.name == text or c.name.startswith(text + "["):
                refs.append(f"Constant[{c.index}] {c.register_name} {c.type_name}")
        lines = [
            f"Symbol: {text}",
            f"DVLE: {dvle.index}",
            f"Index: {sym_idx}",
            f"Relative offset: 0x{rel:X}",
            f"Absolute offset: 0x{dvle.offset + dvle.symbol_offset + rel:X}",
            "",
            "Referenced by:",
        ]
        lines.extend(["  " + r for r in refs] or ["  <no parsed reference>"])
        return "\n".join(lines)

    def _raw_table_for_item(self, item: str) -> str:
        if item.startswith("input:"):
            _, dvle_s, inp_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            inp = dvle.inputs[int(inp_s)]
            return json.dumps({
                "dvle": dvle.index,
                "input": inp.index,
                "name": inp.name,
                "offset": f"0x{inp.offset:X}",
                "name_offset": f"0x{inp.name_offset:X}",
                "start": f"0x{inp.start:02X}",
                "end": f"0x{inp.end:02X}",
            }, indent=2)
        if item.startswith("output:"):
            _, dvle_s, out_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            out = dvle.outputs[int(out_s)]
            return json.dumps({
                "dvle": dvle.index,
                "output": out.index,
                "type": OUTPUT_TYPES.get(out.output_type, f"unknown_{out.output_type}"),
                "type_raw": out.output_type,
                "register": f"o{out.register_id}",
                "mask": component_mask(out.mask),
                "unknown": f"0x{out.unknown:04X}",
                "offset": f"0x{out.offset:X}",
            }, indent=2)
        if item.startswith("label:"):
            _, dvle_s, lab_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            lab = dvle.labels[int(lab_s)]
            return json.dumps({
                "dvle": dvle.index,
                "label": lab.index,
                "name": self.parser._label_display_name(lab),
                "id": lab.label_id,
                "opcode_address": lab.opcode_address,
                "name_offset": f"0x{lab.name_offset:X}",
                "unknown_a": lab.unknown_a.hex(" ").upper(),
                "unknown_b": f"0x{lab.unknown_b:08X}",
                "offset": f"0x{lab.offset:X}",
            }, indent=2)
        if item.startswith("symbol:"):
            _, dvle_s, sym_s = item.split(":")
            dvle = self.parser.dvles[int(dvle_s)]
            rel, text = dvle.symbols[int(sym_s)]
            return json.dumps({
                "dvle": dvle.index,
                "symbol": int(sym_s),
                "text": text,
                "relative_offset": f"0x{rel:X}",
                "absolute_offset": f"0x{dvle.offset + dvle.symbol_offset + rel:X}",
            }, indent=2)
        if item.startswith("const:"):
            _, dvle_s, const_s = item.split(":")
            c = self.parser.dvles[int(dvle_s)].constants[int(const_s)]
            return json.dumps({
                "dvle": int(dvle_s),
                "constant": c.index,
                "name": c.display_name,
                "type": c.type_name,
                "register": c.register_name,
                "offset": f"0x{c.offset:X}",
                "raw": [f"0x{x:X}" for x in c.raw],
                "values": c.values_for_display,
            }, indent=2)
        if item.startswith("inst:") and self.parser.dvlp:
            _, inst_s = item.split(":")
            inst = self.parser.dvlp.instructions[int(inst_s)]
            return json.dumps({
                "index": inst.index,
                "offset": f"0x{inst.offset:X}",
                "word": f"0x{inst.word:08X}",
                "mnemonic": inst.mnemonic,
                "format": inst.fmt,
                "disasm": inst.disasm,
                "fields": inst.fields,
            }, indent=2)
        if item.startswith("opdesc:") and self.parser.dvlp:
            _, op_s = item.split(":")
            idx = int(op_s)
            desc, flags = self.parser.dvlp.opdescs[idx]
            return json.dumps({"index": idx, "desc": f"0x{desc:08X}", "flags": f"0x{flags:08X}", **pica_decode_opdesc(desc, flags)}, indent=2)
        if item.startswith("dvlp") and self.parser.dvlp:
            d = self.parser.dvlp
            return json.dumps(self.parser._dvlp_to_dict(), indent=2)
        if item.startswith("dvle:"):
            parts = item.split(":")
            dvle = self.parser.dvles[int(parts[1])]
            return json.dumps(self.parser._dvle_to_dict(dvle), indent=2)
        return json.dumps(self.parser.to_dict(), indent=2)

    def show_constant(self, dvle_idx: int, const_idx: int) -> None:
        c = self.parser.dvles[dvle_idx].constants[const_idx]
        details = [
            f"Constant: {c.display_name}",
            f"DVLE: {dvle_idx}",
            f"Index: {const_idx}",
            f"Offset: 0x{c.offset:X}",
            f"Type: {c.type_name}",
            f"Register: {c.register_name} (id={c.register_id})",
            f"Mapped input: {c.mapped_input or '-'}",
            f"Length hint byte: {c.length_hint}",
            f"Display values: {c.values_for_display}",
            f"Raw values: {[f'0x{x:X}' for x in c.raw]}",
        ]
        self._set_text(self.details_text, "\n".join(details))
        self._set_text(self.hex_text, hexdump(self.parser.data, c.offset, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"const:{dvle_idx}:{const_idx}"))

        self.edit_name_label.configure(text=f"{c.display_name}   ({c.type_name}, {c.register_name}, offset 0x{c.offset:X})")
        values = c.values_for_display
        values = list(values) + [0, 0, 0, 0]
        for i in range(4):
            if c.entry_type == 2:
                self.edit_vars[i].set(f"{float(values[i]):.8g}")
            elif c.entry_type == 0:
                self.edit_vars[i].set("1" if bool(values[i]) else "0")
            else:
                self.edit_vars[i].set(str(int(values[i])))
            self.raw_vars[i].set(f"0x{c.raw[i]:X}")
        self.notebook.select(1)

    def show_instruction(self, inst_idx: int) -> None:
        if not self.parser.dvlp:
            return
        inst = self.parser.dvlp.instructions[inst_idx]
        f = inst.fields
        annotated = f.get("annotated_disasm", inst.disasm)
        details = [
            f"Instruction {inst.index}",
            f"Offset: 0x{inst.offset:X}",
            f"Raw word: 0x{inst.word:08X}",
            f"Mnemonic: {inst.mnemonic}",
            f"Effective opcode: 0x{inst.opcode:02X}; raw top opcode bits: 0x{inst.raw_opcode:02X}",
            f"Format: {inst.fmt}",
            f"Disasm: {inst.disasm}",
            f"Annotated disasm: {annotated}",
        ]

        source_line = f.get("source_line")
        if source_line:
            details.append(f"Source line: {source_line.get('filename', '')}:{source_line.get('line', '')}")

        if f.get("labels_here"):
            details.append("")
            details.append("Labels at this instruction:")
            for lab in f.get("labels_here", []):
                details.append(f"  DVLE {lab.get('dvle')}: {lab.get('name')} (id={lab.get('label_id')})")

        if f.get("entrypoints") or f.get("end_markers") or f.get("active_dvles"):
            details.append("")
            details.append("DVLE ranges:")
            for ref in f.get("entrypoints", []):
                details.append(f"  Entry for DVLE {ref.get('dvle')} ({ref.get('shader_type')})")
            for ref in f.get("end_markers", []):
                details.append(f"  End marker for DVLE {ref.get('dvle')} ({ref.get('shader_type')})")
            active = ", ".join(f"DVLE {x.get('dvle')}" for x in f.get("active_dvles", []))
            if active:
                details.append(f"  In active range: {active}")

        if f.get("register_annotations"):
            details.append("")
            details.append("Register/symbol mapping:")
            for ann in f.get("register_annotations", []):
                sym = ann.get("symbol") or "-"
                table = ann.get("table") or "-"
                details.append(f"  DVLE {ann.get('dvle')} {ann.get('role')}: {ann.get('register')} -> {sym} ({table})")

        if f.get("target_annotations"):
            details.append("")
            details.append("Branch/call target labels:")
            for ann in f.get("target_annotations", []):
                details.append(f"  DVLE {ann.get('dvle')}: target {ann.get('opcode_address')} -> {ann.get('name')}")

        details.extend(["", "Decoded fields:"])
        hidden = {"opdesc", "source_line", "labels_here", "entrypoints", "end_markers", "active_dvles", "register_annotations", "target_annotations", "annotated_disasm", "annotated_disasm_by_dvle"}
        for key in sorted(k for k in f.keys() if k not in hidden):
            details.append(f"  {key}: {f[key]}")
        if "opdesc" in f:
            details.append("")
            details.append("Referenced operand descriptor:")
            for key, val in f["opdesc"].items():
                details.append(f"  {key}: {val}")
        self._set_text(self.details_text, "\n".join(details))
        self._set_text(self.hex_text, hexdump(self.parser.data, inst.offset, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"inst:{inst_idx}"))

        self.instr_header_label.configure(text=f"Instruction {inst.index}: {f.get('annotated_disasm', inst.disasm)}")
        dvle_idx = self._active_dvle_for_instruction(inst.index)
        self.instr_raw_var.set(f"0x{inst.word:08X}")
        self.instr_mnemonic_var.set(inst.mnemonic)
        self.instr_asm_var.set(str(annotated))
        self.instr_desc_var.set(str(f.get("desc_id", 0)))
        self.instr_dst_var.set(self._display_register_field(str(f.get("dst", "r0")), dvle_idx))
        self.instr_src1_var.set(self._display_register_field(str(f.get("src1", "v0")), dvle_idx))
        self.instr_src2_var.set(self._display_register_field(str(f.get("src2", "v0")), dvle_idx))
        self.instr_src3_var.set(self._display_register_field(str(f.get("src3", "v0")), dvle_idx))
        self.instr_idx_var.set(str(f.get("idx", 0)))
        self.instr_num_var.set(str(f.get("num", 0)))
        self.instr_target_var.set(str(f.get("target", 0)))
        self.instr_condop_var.set(str(f.get("condop_name", f.get("condop", 0))))
        uid = int(f.get("uniform_id", 0) or 0)
        if "uniform_id" in f:
            uniform_reg = ("i" if inst.opcode == 0x29 else "b") + str(uid)
            self.instr_boolint_var.set(self._display_register_field(uniform_reg, dvle_idx))
        else:
            self.instr_boolint_var.set(str(uid))
        self.instr_refx_var.set(str(f.get("refx", 0)))
        self.instr_refy_var.set(str(f.get("refy", 0)))
        self.instr_cmpx_var.set(str(f.get("cmpx_name", f.get("cmpx", 0))))
        self.instr_cmpy_var.set(str(f.get("cmpy_name", f.get("cmpy", 0))))
        self._refresh_instruction_register_choices(inst.index)
        self.notebook.select(2)

    def show_opdesc(self, opdesc_idx: int) -> None:
        if not self.parser.dvlp:
            return
        desc, flags = self.parser.dvlp.opdescs[opdesc_idx]
        dec = pica_decode_opdesc(desc, flags)
        details = [
            f"Operand Descriptor {opdesc_idx}",
            f"Offset: 0x{self.parser.dvlp.offset + self.parser.dvlp.opdesc_offset + opdesc_idx * 8:X}",
            f"Raw desc: 0x{desc:08X}",
            f"Flags: 0x{flags:08X}",
            "",
            f"Destination mask: {dec['dest_mask']} (raw 0x{dec['dest_mask_raw']:X})",
            f"SRC1: {'-' if dec['src1_neg'] else ''}.{dec['src1_swizzle']} raw=0x{dec['src1_swizzle_raw']:02X}",
            f"SRC2: {'-' if dec['src2_neg'] else ''}.{dec['src2_swizzle']} raw=0x{dec['src2_swizzle_raw']:02X}",
            f"SRC3: {'-' if dec['src3_neg'] else ''}.{dec['src3_swizzle']} raw=0x{dec['src3_swizzle_raw']:02X}",
            "",
            "Instructions using this opdesc:",
        ]
        users = []
        for inst in self.parser.dvlp.instructions:
            if inst.fields.get("desc_id") == opdesc_idx:
                users.append(f"  {inst.index:04d}: {inst.disasm}")
        details.extend(users or ["  <none>"])
        self._set_text(self.details_text, "\n".join(details))
        off = self.parser.dvlp.offset + self.parser.dvlp.opdesc_offset + opdesc_idx * 8
        self._set_text(self.hex_text, hexdump(self.parser.data, off, 0x40))
        self._set_text(self.raw_text, self._raw_table_for_item(f"opdesc:{opdesc_idx}"))

        self.opdesc_header_label.configure(text=f"Operand Descriptor {opdesc_idx}")
        self.opdesc_raw_var.set(f"0x{desc:08X}")
        self.opdesc_flags_var.set(f"0x{flags:08X}")
        self.opdesc_mask_var.set(dec["dest_mask"])
        self.opdesc_src1_swizzle_var.set(dec["src1_swizzle"])
        self.opdesc_src2_swizzle_var.set(dec["src2_swizzle"])
        self.opdesc_src3_swizzle_var.set(dec["src3_swizzle"])
        self.opdesc_src1_neg_var.set(bool(dec["src1_neg"]))
        self.opdesc_src2_neg_var.set(bool(dec["src2_neg"]))
        self.opdesc_src3_neg_var.set(bool(dec["src3_neg"]))
        self.notebook.select(3)

    def _clear_instruction_tab(self) -> None:
        if hasattr(self, "instr_header_label"):
            self.instr_header_label.configure(text="Select a decoded instruction to edit.")
        for v in [self.instr_mnemonic_var, self.instr_raw_var, self.instr_asm_var, self.instr_desc_var,
                  self.instr_dst_var, self.instr_src1_var, self.instr_src2_var, self.instr_src3_var,
                  self.instr_idx_var, self.instr_num_var, self.instr_target_var, self.instr_condop_var,
                  self.instr_boolint_var, self.instr_refx_var, self.instr_refy_var, self.instr_cmpx_var, self.instr_cmpy_var]:
            v.set("")
        self._refresh_instruction_register_choices(None)

    def _clear_opdesc_tab(self) -> None:
        if hasattr(self, "opdesc_header_label"):
            self.opdesc_header_label.configure(text="Select an operand descriptor to edit.")
        for v in [self.opdesc_raw_var, self.opdesc_flags_var, self.opdesc_mask_var,
                  self.opdesc_src1_swizzle_var, self.opdesc_src2_swizzle_var, self.opdesc_src3_swizzle_var]:
            v.set("")
        self.opdesc_src1_neg_var.set(False)
        self.opdesc_src2_neg_var.set(False)
        self.opdesc_src3_neg_var.set(False)

    def _current_instruction_index(self) -> int:
        if self.selected_instruction is None:
            raise ValueError("Select an instruction first.")
        return self.selected_instruction

    def _current_opdesc_index(self) -> int:
        if self.selected_opdesc is None:
            raise ValueError("Select an operand descriptor first.")
        return self.selected_opdesc

    def _refresh_after_instruction_edit(self, inst_idx: Optional[int] = None) -> None:
        self.parser.parse()
        self.refresh_tree()
        if inst_idx is not None and self.parser.dvlp and 0 <= inst_idx < len(self.parser.dvlp.instructions):
            iid = f"inst:{inst_idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_instruction = inst_idx
            self.show_instruction(inst_idx)
        self.preview.set_shader(self.parser)
        if inst_idx is not None:
            self.preview.set_selection(inst_idx=inst_idx)
        self._set_status("Instruction/opdesc edit applied. Save to write it to disk.")

    def apply_instruction_raw(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            word = int(self.instr_raw_var.get().strip() or "0", 0)
            self.parser.update_opcode_word(inst_idx, word)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Instruction raw edit failed", str(exc))

    def apply_instruction_fields(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not self.parser.dvlp:
                return
            base_word = self.parser.dvlp.instructions[inst_idx].word
            labels = self._labels_for_dvle(self._active_dvle_for_instruction(inst_idx))
            word = pica_build_instruction_word(
                self.instr_mnemonic_var.get(),
                base_word=base_word,
                desc_id=int(self.instr_desc_var.get().strip() or "0", 0),
                dst=self._resolve_register_field(self.instr_dst_var.get().strip() or "r0", "dst", inst_idx),
                src1=self._resolve_register_field(self.instr_src1_var.get().strip() or "v0", "src", inst_idx),
                src2=self._resolve_register_field(self.instr_src2_var.get().strip() or "v0", "src", inst_idx),
                src3=self._resolve_register_field(self.instr_src3_var.get().strip() or "v0", "src", inst_idx),
                idx=int(self.instr_idx_var.get().strip() or "0", 0),
                num=int(self.instr_num_var.get().strip() or "0", 0),
                target=parse_target_token(self.instr_target_var.get().strip() or "0", labels),
                condop=parse_condop(self.instr_condop_var.get().strip() or "0"),
                refx=int(self.instr_refx_var.get().strip() or "0", 0),
                refy=int(self.instr_refy_var.get().strip() or "0", 0),
                uniform_id=parse_uniform_token(self._resolve_register_field(self.instr_boolint_var.get().strip() or "0", "uniform", inst_idx)),
                cmpx=parse_cmpop(self.instr_cmpx_var.get().strip() or "0"),
                cmpy=parse_cmpop(self.instr_cmpy_var.get().strip() or "0"),
            )
            self.parser.update_opcode_word(inst_idx, word)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Instruction field edit failed", str(exc))

    def apply_instruction_asm(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not self.parser.dvlp:
                return
            existing = self.parser.dvlp.instructions[inst_idx]
            desc_id = int(existing.fields.get("desc_id", 0))
            dvle_idx = self._active_dvle_for_instruction(inst_idx)
            word, opdesc_fields = parse_general_asm_line(
                self.instr_asm_var.get(),
                base_word=existing.word,
                default_desc_id=desc_id,
                labels=self._labels_for_dvle(dvle_idx),
                symbol_to_register=self._symbol_map_for_asm_roundtrip(inst_idx, dvle_idx),
            )
            self.parser.update_opcode_word(inst_idx, word)
            if opdesc_fields is not None and 0 <= desc_id < self.parser.dvlp.opdesc_count:
                old_desc, old_flags = self.parser.dvlp.opdescs[desc_id]
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
                self.parser.update_opdesc(desc_id, desc, flags)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("ASM patch failed", str(exc))


    def insert_nop_before_selected(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not messagebox.askyesno("Insert NOP", "This shifts opcode words down inside the existing opcode table and drops the last opcode. Continue?"):
                return
            self.parser.insert_nop_instruction(inst_idx)
            self._refresh_after_instruction_edit(inst_idx)
        except Exception as exc:
            messagebox.showerror("Insert instruction failed", str(exc))

    def delete_selected_instruction(self) -> None:
        try:
            inst_idx = self._current_instruction_index()
            if not messagebox.askyesno("Delete instruction", "This shifts following opcode words up and fills the final slot with NOP. Continue?"):
                return
            self.parser.delete_instruction_shift_up(inst_idx)
            self._refresh_after_instruction_edit(min(inst_idx, max(0, self.parser.dvlp.opcode_count - 1 if self.parser.dvlp else 0)))
        except Exception as exc:
            messagebox.showerror("Delete instruction failed", str(exc))

    def add_asm_instruction_to_active_dvle(self) -> None:
        if not self._require_loaded():
            return
        asm = simpledialog.askstring("Add ASM instruction", "ASM to insert before the active DVLE end marker:", initialvalue=self.instr_asm_var.get() or "nop")
        if not asm:
            return
        try:
            dvle_idx = self.preview.current_dvle_index if hasattr(self, "preview") and self.preview.current_dvle_index is not None else 0
            idx = self.parser.add_instruction_at_end_of_range(int(dvle_idx), asm)
            self._refresh_after_instruction_edit(idx)
        except Exception as exc:
            messagebox.showerror("Add instruction failed", str(exc))

    def apply_opdesc_raw(self) -> None:
        try:
            idx = self._current_opdesc_index()
            desc = int(self.opdesc_raw_var.get().strip() or "0", 0)
            flags = int(self.opdesc_flags_var.get().strip() or "0", 0)
            self.parser.update_opdesc(idx, desc, flags)
            self.parser.parse()
            self.refresh_tree()
            iid = f"opdesc:{idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_opdesc = idx
            self.show_opdesc(idx)
            self.preview.set_shader(self.parser)
            self._set_status("Operand descriptor raw edit applied. Save to write it to disk.")
        except Exception as exc:
            messagebox.showerror("Opdesc raw edit failed", str(exc))

    def apply_opdesc_decoded(self) -> None:
        try:
            idx = self._current_opdesc_index()
            flags = int(self.opdesc_flags_var.get().strip() or "0", 0)
            desc, flags = pica_encode_opdesc(
                self.opdesc_mask_var.get() or "xyzw",
                self.opdesc_src1_swizzle_var.get() or "xyzw",
                self.opdesc_src2_swizzle_var.get() or "xyzw",
                self.opdesc_src3_swizzle_var.get() or "xyzw",
                self.opdesc_src1_neg_var.get(),
                self.opdesc_src2_neg_var.get(),
                self.opdesc_src3_neg_var.get(),
                preserve_flags=flags,
            )
            self.parser.update_opdesc(idx, desc, flags)
            self.parser.parse()
            self.refresh_tree()
            iid = f"opdesc:{idx}"
            if self.tree.exists(iid):
                self.tree.selection_set(iid)
                self.tree.see(iid)
            self.selected_opdesc = idx
            self.show_opdesc(idx)
            self.preview.set_shader(self.parser)
            self._set_status("Operand descriptor decoded edit applied. Save to write it to disk.")
        except Exception as exc:
            messagebox.showerror("Opdesc decoded edit failed", str(exc))

    def _clear_edit_tab(self) -> None:
        self.edit_name_label.configure(text="Select a constant to edit.")
        for v in self.edit_vars + self.raw_vars:
            v.set("")
        self._clear_instruction_tab()
        self._clear_opdesc_tab()

    def _current_constant(self) -> Optional[ShaderConstant]:
        if self.selected_constant is None:
            return None
        dvle_idx, const_idx = self.selected_constant
        return self.parser.dvles[dvle_idx].constants[const_idx]

    def apply_display_values(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            messagebox.showinfo("No constant selected", "Select a constant entry first.")
            return
        try:
            if c.entry_type == 2:
                raw = [float_to_pica24(float(v.get().strip() or "0")) for v in self.edit_vars]
            elif c.entry_type == 0:
                raw = [1 if self._parse_bool(self.edit_vars[0].get()) else 0, 0, 0, 0]
            else:
                raw = [int(v.get().strip() or "0", 0) & 0xFF for v in self.edit_vars]
            dvle_idx, const_idx = self.selected_constant
            self.parser.update_constant(dvle_idx, const_idx, raw)
            self.parser.parse()
            self.refresh_tree()
            self.tree.selection_set(f"const:{dvle_idx}:{const_idx}")
            self.show_constant(dvle_idx, const_idx)
            self.preview.set_shader(self.parser)
            self.preview.set_selection(dvle_idx=dvle_idx, inst_idx=None)
            self._set_status("Applied constant values. Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Invalid value", str(exc))

    def apply_raw_values(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            messagebox.showinfo("No constant selected", "Select a constant entry first.")
            return
        try:
            raw = [int(v.get().strip() or "0", 0) for v in self.raw_vars]
            if c.entry_type == 2:
                raw = [x & 0xFFFFFF for x in raw]
            elif c.entry_type == 1:
                raw = [x & 0xFF for x in raw]
            elif c.entry_type == 0:
                raw = [1 if raw[0] else 0, 0, 0, 0]
            dvle_idx, const_idx = self.selected_constant
            self.parser.update_constant(dvle_idx, const_idx, raw)
            self.parser.parse()
            self.refresh_tree()
            self.tree.selection_set(f"const:{dvle_idx}:{const_idx}")
            self.show_constant(dvle_idx, const_idx)
            self.preview.set_shader(self.parser)
            self.preview.set_selection(dvle_idx=dvle_idx, inst_idx=None)
            self._set_status("Applied raw constant values. Save to write them to disk.")
        except Exception as exc:
            messagebox.showerror("Invalid raw value", str(exc))

    @staticmethod
    def _parse_bool(text: str) -> bool:
        return text.strip().lower() in {"1", "true", "yes", "on"}

    def copy_constant_json(self) -> None:
        c = self._current_constant()
        if c is None or self.selected_constant is None:
            return
        dvle_idx, _const_idx = self.selected_constant
        payload = {
            "dvle": dvle_idx,
            "index": c.index,
            "name": c.display_name,
            "type": c.type_name,
            "register": c.register_name,
            "offset": f"0x{c.offset:X}",
            "values": c.values_for_display,
            "raw": [f"0x{x:X}" for x in c.raw],
        }
        self.clipboard_clear()
        self.clipboard_append(json.dumps(payload, indent=2))
        self._set_status("Copied constant JSON to clipboard.")

if __name__ == "__main__":
    App().mainloop()

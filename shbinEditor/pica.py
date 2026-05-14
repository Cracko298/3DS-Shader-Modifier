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
    comps = _normalize_pica_components(s, fill_to_four=False)
    mask = 0
    for ch in comps:
        if ch == "x": mask |= 0x8
        elif ch == "y": mask |= 0x4
        elif ch == "z": mask |= 0x2
        elif ch == "w": mask |= 0x1
    return mask & 0xF

def pica_swizzle_to_string(selector: int) -> str:
    letters = "xyzw"
    selector &= 0xFF
    return "".join(letters[(selector >> (6 - i * 2)) & 3] for i in range(4))

def parse_pica_swizzle(text: str) -> int:
    s = str(text).strip().lower().replace(".", "")
    if s.startswith("0x") or s.isdigit():
        return int(s, 0) & 0xFF
    s = _normalize_pica_components(s or "xyzw", fill_to_four=True)
    if len(s) != 4:
        raise ValueError(f"Swizzle must be xyzw, xxxx, yzxw, rgba, stpq, etc.; got {text!r}")
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
        d = pica_decode_opdesc(0x01B01B0F, 0)                                      
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
        word = set_bits(word, 27, 5, 0x17)                                                      
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

__all__ = [name for name in globals() if not name.startswith("__")]

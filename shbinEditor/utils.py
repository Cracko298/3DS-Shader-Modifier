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
    try:
        if _normalize_pica_components(sel, fill_to_four=True) == "xyzw":
            return b
    except Exception:
        pass
                                                                                  
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

def _pica_component_char(ch: str) -> str:
    c = str(ch or "").lower()
    if c in {"x", "r", "s"}:
        return "x"
    if c in {"y", "g", "t"}:
        return "y"
    if c in {"z", "b", "p"}:
        return "z"
    if c in {"w", "a", "q"}:
        return "w"
    raise ValueError(f"Invalid component {ch!r}; use xyzw / rgba / stpq")

def _normalize_pica_components(text: str, *, fill_to_four: bool = False) -> str:
    s = str(text).strip().lower().replace(".", "")
    if not s:
        return "xyzw" if fill_to_four else ""
    out = "".join(_pica_component_char(ch) for ch in s if ch not in "_, ")
    if fill_to_four and out:
        if len(out) > 4:
            raise ValueError(f"Swizzle/mask is too long: {text!r}")
        out += out[-1] * (4 - len(out))
    return out

def parse_dvle_output_mask(text: str) -> int:
    """Parse DVLE output-map component masks.

    Important: DVLE output-map masks are not encoded the same way as PICA
    instruction destination masks.  PICA opdesc masks use x=0x8, y=0x4,
    z=0x2, w=0x1, while DVLE output-map masks use the normal low-to-high
    order: x=0x1, y=0x2, z=0x4, w=0x8.  Reusing parse_pica_dest_mask here
    makes partial outputs like texcoord0.xy become 0xC (zw) instead of 0x3
    (xy), which can make valid VSH files fail linkage/runtime on hardware.
    """
    s = str(text).strip().lower().replace('.', '')
    if not s or s == '-':
        return 0
    if s.startswith('0x') or s.isdigit():
        return int(s, 0) & 0xF
    comps = _normalize_pica_components(s, fill_to_four=False)
    mask = 0
    for ch in comps:
        if ch == 'x':
            mask |= 0x1
        elif ch == 'y':
            mask |= 0x2
        elif ch == 'z':
            mask |= 0x4
        elif ch == 'w':
            mask |= 0x8
    return mask & 0xF

def float_to_pica24(value: float) -> int:
                                                                                        
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

__all__ = [name for name in globals() if not name.startswith("__")]

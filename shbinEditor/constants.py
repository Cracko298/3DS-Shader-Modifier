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

APP_TITLE = "Cracko298's 3DS Shader Assembler/Disassembler & Editor"

                      
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


                                                            
VECTOR_COMPONENT_SUFFIX_RE = re.compile(r"^(?P<base>.+)\.(?P<components>[xyzwrgbastpq]{1,4})$", re.IGNORECASE)

__all__ = [name for name in globals() if not name.startswith("__")]

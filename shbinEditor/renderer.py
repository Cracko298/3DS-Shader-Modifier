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
from .parser import *

class ShaderPreview3D(ttk.LabelFrame):
    SUPPORTED_OPS = {
        "ADD", "MUL", "MAD", "MADI", "MOV", "DP3", "DP4", "DPH", "MIN", "MAX",
        "RCP", "RSQ", "FLR", "EX2", "LG2", "LITP", "SGE", "SLT", "DST",
        "MOVA", "CMP", "DPHI", "DSTI", "SGEI", "SLTI",
        "NOP", "END", "BREAK", "BREAKC", "CALL", "CALLC", "CALLU",
        "IFC", "IFU", "JMPC", "JMPU", "LOOP",
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
        defined = set()
        for c in dvle.constants:
            if c.entry_type == 2 and 0 <= c.register_id < len(regs):
                vals = [float(pica24_to_float(v)) for v in c.raw]
                regs[c.register_id] = (vals + [0.0, 0.0, 0.0, 1.0])[:4]
                defined.add(int(c.register_id))

                                                                                 
                                                                            
                                                                    
        identity_rows = (
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        )
        for i, row in enumerate(identity_rows):
            if i not in defined:
                regs[i] = list(row)
        return regs

    def _integer_registers(self, dvle: DVLEInfo) -> List[List[int]]:
        regs = [[0, 0, 0, 0] for _ in range(16)]
        for c in dvle.constants:
            if c.entry_type == 1 and 0 <= c.register_id < len(regs):
                vals = [int(v) for v in c.raw[:4]]
                regs[c.register_id] = (vals + [0, 0, 0, 0])[:4]
        return regs

    def _boolean_registers(self, dvle: DVLEInfo) -> List[bool]:
        regs = [False for _ in range(16)]
        for c in dvle.constants:
            if c.entry_type == 0 and 0 <= c.register_id < len(regs):
                regs[c.register_id] = bool(c.raw[0])
        return regs

    def _seed_named_preview_uniforms(self, dvle: DVLEInfo, vertex: Dict[str, Any],
                                     cregs: List[List[float]], iregs: List[List[int]],
                                     bregs: List[bool]) -> None:
                                                                

                                                                
                                                                                                                                                                                                                              
                                                          

        defined_c = {int(c.register_id) for c in dvle.constants if c.entry_type == 2}
        defined_i = {int(c.register_id) for c in dvle.constants if c.entry_type == 1}
        defined_b = {int(c.register_id) for c in dvle.constants if c.entry_type == 0}
        current_color = list(vertex.get("color", (1.0, 1.0, 1.0, 1.0)))[:4]
        normal = self._normalize3(tuple(list(vertex.get("normal", (0.0, 0.0, 1.0, 0.0)))[:3]))
        lx, ly, lz = self._light_position()
        ldir = self._normalize3((lx, ly, lz))
        identity_rows = (
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        )

        def set_c(idx: int, vals: Iterable[float], *, force: bool = False) -> None:
            if 0 <= idx < len(cregs) and (force or idx not in defined_c):
                vv = [float(x) for x in list(vals)[:4]]
                cregs[idx] = (vv + [0.0, 0.0, 0.0, 1.0])[:4]

        def set_i(idx: int, vals: Iterable[int], *, force: bool = False) -> None:
            if 0 <= idx < len(iregs) and (force or idx not in defined_i):
                vv = [int(x) for x in list(vals)[:4]]
                iregs[idx] = (vv + [0, 0, 0, 0])[:4]

        def set_b(idx: int, val: bool, *, force: bool = False) -> None:
            if 0 <= idx < len(bregs) and (force or idx not in defined_b):
                bregs[idx] = bool(val)

        for inp in dvle.inputs:
            lo, hi = sorted((int(inp.start), int(inp.end)))
            name = (inp.name or "").lower().replace("$", ".")
            if FLOAT_REG_BASE <= lo < INT_REG_BASE:
                base = lo - FLOAT_REG_BASE
                count = max(1, hi - lo + 1)
                if any(k in name for k in ("worldviewproj", "world_view_proj", "modelviewproj", "mvp", "projection")):
                    for i in range(min(4, count)):
                        set_c(base + i, identity_rows[i])
                elif any(k in name for k in ("current_color", "diffuse", "material", "tint", "color", "colour")):
                    set_c(base, current_color)
                elif "fog" in name:
                    set_c(base, [0.70, 0.82, 1.00, 1.0])
                elif any(k in name for k in ("light_dir", "lightdir", "sun_dir", "sundir")):
                    set_c(base, [ldir[0], ldir[1], ldir[2], 0.0])
                elif "light" in name:
                    set_c(base, [lx, ly, lz, float(self.light_power_var.get())])
                elif any(k in name for k in ("normal", "nrm")):
                    set_c(base, [normal[0], normal[1], normal[2], 0.0])
                elif any(k in name for k in ("camera", "eye", "viewpos")):
                    set_c(base, [0.0, 0.0, -4.0, 1.0])
                elif any(k in name for k in ("time", "frame")):
                    set_c(base, [0.0, 0.0, 0.0, 1.0])
            elif INT_REG_BASE <= lo < BOOL_REG_BASE:
                base = lo - INT_REG_BASE
                if any(k in name for k in ("loop", "count", "num")):
                    set_i(base, [1, 0, 0, 0])
            elif lo >= BOOL_REG_BASE:
                base = lo - BOOL_REG_BASE
                if any(k in name for k in ("enable", "use", "has", "do", "flag")):
                    set_b(base, True)

    def _attribute_target(self, dvle: DVLEInfo, words: Iterable[str], default_reg: int) -> int:
        for inp in dvle.inputs:
                                                                                
                                                                                
                                                                
            if not (0 <= int(inp.start) < 0x10):
                continue
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
    def _clamp_vec4(values: Iterable[float], lo: float = -1.0e20, hi: float = 1.0e20) -> List[float]:
        out: List[float] = []
        for x in list(values)[:4]:
            try:
                f = float(x)
            except Exception:
                f = 0.0
            if not math.isfinite(f):
                f = 0.0
            out.append(max(lo, min(hi, f)))
        while len(out) < 4:
            out.append(0.0 if len(out) < 3 else 1.0)
        return out

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
                                                                               
                                                                            
                                        
            if shader_is_black:
                return self._safe_rgb([x * 0.20 for x in preview], floor=0.025)
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

    def _src_indexed(self, raw: int, idx: int, aregs: List[int],
                     vregs: List[List[float]], rregs: List[List[float]],
                     cregs: List[List[float]]) -> List[float]:
        raw = int(raw)
        add = 0
        if int(idx) == 1:
            add = int(aregs[0])
        elif int(idx) == 2:
            add = int(aregs[1])
        elif int(idx) == 3:
            add = int(aregs[2])
        if raw >= 0x20:
            raw = 0x20 + max(0, min(len(cregs) - 1, raw - 0x20 + add))
        return self._src(raw, vregs, rregs, cregs)

    def _write_dest(self, dst_raw: int, mask: str, values: List[float], rregs: List[List[float]], oregs: List[List[float]]) -> None:
        target = oregs[int(dst_raw)] if int(dst_raw) < 0x10 else rregs[int(dst_raw) - 0x10]
        if mask == "-":
            return
        if not mask:
            mask = "xyzw"
        values = self._clamp_vec4(values)
        for ch in mask:
            idx = "xyzw".find(ch)
            if 0 <= idx < 4:
                target[idx] = float(values[idx])

    @staticmethod
    def _cmp_result(op_id: int, a: float, b: float) -> bool:
        if op_id == 0: return abs(a - b) <= 1e-6
        if op_id == 1: return abs(a - b) > 1e-6
        if op_id == 2: return a < b
        if op_id == 3: return a <= b
        if op_id == 4: return a > b
        if op_id == 5: return a >= b
        return True

    @staticmethod
    def _cond_result(condop: int, refx: int, refy: int, cmp_flags: List[bool]) -> bool:
        x = bool(cmp_flags[0]) == bool(refx)
        y = bool(cmp_flags[1]) == bool(refy)
        if condop == 0: return x or y
        if condop == 1: return x and y
        if condop == 2: return x
        if condop == 3: return y
        return False

    def _execute_vertex(self, dvle: DVLEInfo, vertex: Dict[str, Any]) -> Tuple[List[float], List[float], int]:
        if not self.parser or not self.parser.dvlp:
            return list(vertex.get("pos", (0, 0, 0, 1)))[:4], list(vertex.get("color", (1, 1, 1, 1)))[:4], 0

        vregs = self._make_input_regs(dvle, vertex)
        rregs = [[0.0, 0.0, 0.0, 1.0] for _ in range(16)]
        oregs = [[0.0, 0.0, 0.0, 1.0] for _ in range(16)]
        cregs = self._constant_registers(dvle)
        iregs = self._integer_registers(dvle)
        bregs = self._boolean_registers(dvle)
        self._seed_named_preview_uniforms(dvle, vertex, cregs, iregs, bregs)

        aregs = [0, 0, 0]                                                
        cmp_flags = [False, False]
        executed = 0
        skipped = 0
        max_steps = 2048
        instructions = self.parser.dvlp.instructions
        start, end = sorted((int(dvle.opcode_entry), int(dvle.opcode_end)))
        start = max(0, start)
        end = min(max(start, end), len(instructions) - 1)

        def condition_from_bool(uniform_id: int) -> bool:
            if 0 <= int(uniform_id) < len(bregs):
                return bool(bregs[int(uniform_id)])
            return False

        def execute_arith(inst: ShaderInstruction) -> bool:
            nonlocal executed, skipped
            name = inst.mnemonic.upper()
            f = inst.fields
            desc = f.get("opdesc", {}) if isinstance(f.get("opdesc"), dict) else {}
            try:
                if inst.fmt in {"1", "1u", "1i", "1c"}:
                    idx = int(f.get("idx", 0))
                    s1 = self._src_indexed(int(f.get("src1_raw", 0)), idx, aregs, vregs, rregs, cregs)
                    s2 = self._src_indexed(int(f.get("src2_raw", 0)), 0, aregs, vregs, rregs, cregs)
                    a = self._swizzle(s1, str(desc.get("src1_swizzle", "xyzw")), bool(desc.get("src1_neg", False)))
                    b = self._swizzle(s2, str(desc.get("src2_swizzle", "xyzw")), bool(desc.get("src2_neg", False)))

                    if name == "CMP":
                        cmp_flags[0] = self._cmp_result(int(f.get("cmpx", 0)), a[0], b[0])
                        cmp_flags[1] = self._cmp_result(int(f.get("cmpy", 0)), a[1], b[1])
                        executed += 1
                        return True
                    if name == "ADD": out = [a[i] + b[i] for i in range(4)]
                    elif name == "MUL": out = [a[i] * b[i] for i in range(4)]
                    elif name == "MIN": out = [min(a[i], b[i]) for i in range(4)]
                    elif name == "MAX": out = [max(a[i], b[i]) for i in range(4)]
                    elif name in {"SGE", "SGEI"}: out = [1.0 if a[i] >= b[i] else 0.0 for i in range(4)]
                    elif name in {"SLT", "SLTI"}: out = [1.0 if a[i] < b[i] else 0.0 for i in range(4)]
                    elif name == "DP3":
                        d = sum(a[i] * b[i] for i in range(3)); out = [d, d, d, d]
                    elif name in {"DP4", "DPHI"}:
                        d = sum(a[i] * b[i] for i in range(4)); out = [d, d, d, d]
                    elif name == "DPH":
                        d = sum(a[i] * b[i] for i in range(3)) + b[3]; out = [d, d, d, d]
                    elif name in {"DST", "DSTI"}:
                        out = [1.0, a[1] * b[1], a[2], b[3]]
                    elif name == "MOV": out = a
                    elif name == "MOVA":
                        mask = str(desc.get("dest_mask", "xyzw")) or "xyzw"
                        if "x" in mask: aregs[0] = int(math.floor(a[0]))
                        if "y" in mask: aregs[1] = int(math.floor(a[1]))
                        executed += 1
                        return True
                    elif name == "RCP": out = [1.0 / a[0] if abs(a[0]) > 1e-8 else 0.0] * 4
                    elif name == "RSQ": out = [1.0 / math.sqrt(abs(a[0])) if abs(a[0]) > 1e-8 else 0.0] * 4
                    elif name == "FLR": out = [math.floor(x) for x in a]
                    elif name == "EX2": out = [2.0 ** max(-64.0, min(64.0, x)) for x in a]
                    elif name == "LG2": out = [math.log(max(abs(x), 1e-8), 2.0) for x in a]
                    elif name == "LITP":
                                                                        
                        nx = max(a[0], 0.0)
                        ny = max(a[1], 0.0) if nx > 0.0 else 0.0
                        power = max(-128.0, min(128.0, a[3]))
                        out = [1.0, nx, ny ** power if ny > 0.0 else 0.0, 1.0]
                    else:
                        skipped += 1
                        return False
                    if "dst_raw" in f:
                        self._write_dest(int(f.get("dst_raw", 0)), str(desc.get("dest_mask", "xyzw")), out, rregs, oregs)
                    executed += 1
                    return True

                if inst.fmt in {"5", "5i"}:
                    idx = int(f.get("idx", 0))
                    if inst.fmt == "5i":
                        s1 = self._src_indexed(int(f.get("src1_raw", 0)), 0, aregs, vregs, rregs, cregs)
                        s2 = self._src_indexed(int(f.get("src2_raw", 0)), 0, aregs, vregs, rregs, cregs)
                        s3 = self._src_indexed(int(f.get("src3_raw", 0)), idx, aregs, vregs, rregs, cregs)
                    else:
                        s1 = self._src_indexed(int(f.get("src1_raw", 0)), 0, aregs, vregs, rregs, cregs)
                        s2 = self._src_indexed(int(f.get("src2_raw", 0)), idx, aregs, vregs, rregs, cregs)
                        s3 = self._src_indexed(int(f.get("src3_raw", 0)), 0, aregs, vregs, rregs, cregs)
                    a = self._swizzle(s1, str(desc.get("src1_swizzle", "xyzw")), bool(desc.get("src1_neg", False)))
                    b = self._swizzle(s2, str(desc.get("src2_swizzle", "xyzw")), bool(desc.get("src2_neg", False)))
                    c = self._swizzle(s3, str(desc.get("src3_swizzle", "xyzw")), bool(desc.get("src3_neg", False)))
                    out = [a[i] * b[i] + c[i] for i in range(4)]
                    self._write_dest(int(f.get("dst_raw", 0)), str(desc.get("dest_mask", "xyzw")), out, rregs, oregs)
                    executed += 1
                    return True
            except Exception:
                skipped += 1
                return False
            skipped += 1
            return False

        def run_block(pc_start: int, pc_end: int, depth: int = 0) -> None:
            nonlocal executed, skipped, max_steps
            if depth > 8:
                return
            pc = max(0, int(pc_start))
            local_end = min(int(pc_end), len(instructions) - 1)
            while pc <= local_end and max_steps > 0:
                max_steps -= 1
                inst = instructions[pc]
                name = inst.mnemonic.upper()
                f = inst.fields
                if name == "END":
                    executed += 1
                    break
                if name in {"NOP", "BREAK", "EMIT", "SETEMIT"}:
                    executed += 1
                    if name == "BREAK":
                        break
                    pc += 1
                    continue
                if name in {"ADD", "MUL", "MAD", "MADI", "MOV", "DP3", "DP4", "DPH", "MIN", "MAX", "RCP", "RSQ", "FLR", "EX2", "LG2", "LITP", "SGE", "SGEI", "SLT", "SLTI", "DST", "DSTI", "DPHI", "MOVA", "CMP"}:
                    execute_arith(inst)
                    pc += 1
                    continue

                if name in {"BREAKC", "CALL", "CALLC", "IFC", "JMPC"}:
                    cond = True
                    if name != "CALL":
                        cond = self._cond_result(int(f.get("condop", 0)), int(f.get("refx", 0)), int(f.get("refy", 0)), cmp_flags)
                    target = max(0, min(len(instructions) - 1, int(f.get("target", pc + 1))))
                    num = max(0, int(f.get("num", 0)))
                    if name == "BREAKC":
                        executed += 1
                        if cond:
                            break
                        pc += 1
                        continue
                    if name in {"CALL", "CALLC"}:
                        executed += 1
                        if cond:
                                                                                               
                                                                                         
                            run_block(target, min(len(instructions) - 1, target + max(1, num) - 1), depth + 1)
                        pc += 1
                        continue
                    if name == "JMPC":
                        executed += 1
                        pc = target if cond else pc + 1
                        continue
                    if name == "IFC":
                        executed += 1
                        pc = pc + 1 if cond else target
                        continue

                if name in {"CALLU", "IFU", "JMPU", "LOOP"}:
                    target = max(0, min(len(instructions) - 1, int(f.get("target", pc + 1))))
                    num = max(0, int(f.get("num", 0)))
                    uid = int(f.get("uniform_id", 0))
                    cond = condition_from_bool(uid)
                    if name == "CALLU":
                        executed += 1
                        if cond:
                            run_block(target, min(len(instructions) - 1, target + max(1, num) - 1), depth + 1)
                        pc += 1
                        continue
                    if name == "JMPU":
                        executed += 1
                        pc = target if cond else pc + 1
                        continue
                    if name == "IFU":
                        executed += 1
                        pc = pc + 1 if cond else target
                        continue
                    if name == "LOOP":
                        executed += 1
                        count = 1
                        if 0 <= uid < len(iregs):
                            count = max(0, min(16, int(iregs[uid][0]) + 1))
                        elif num:
                            count = max(0, min(16, num))
                        body_start = pc + 1
                        body_end = min(local_end, target if target > pc else pc + max(1, num))
                        for loop_i in range(count):
                            aregs[2] = loop_i
                            run_block(body_start, body_end, depth + 1)
                        pc = body_end + 1
                        continue

                skipped += 1
                pc += 1

        run_block(start, end)

        pos_reg: Optional[int] = None
        color_reg: Optional[int] = None
        normalquat_reg: Optional[int] = None
        for out in dvle.outputs:
            out_name = OUTPUT_TYPES.get(out.output_type, "")
            if out_name == "result.position":
                pos_reg = max(0, min(15, int(out.register_id)))
            elif out_name == "result.color":
                color_reg = max(0, min(15, int(out.register_id)))
            elif out_name == "result.normalquat":
                normalquat_reg = max(0, min(15, int(out.register_id)))

        if pos_reg is not None:
            pos = list(oregs[pos_reg])
        else:
                                                                                    
            if max(abs(x) for x in oregs[0]) > 1e-6:
                pos = list(oregs[0])
            else:
                pos = list(vertex.get("pos", (0, 0, 0, 1)))[:4]
        col = list(vertex.get("color", (1, 1, 1, 1)))[:4]
        if color_reg is not None:
            col = list(oregs[color_reg])
        elif normalquat_reg is not None:
            n = self._normalize3(tuple(oregs[normalquat_reg][:3]))
            col = [(n[0] * 0.5) + 0.5, (n[1] * 0.5) + 0.5, (n[2] * 0.5) + 0.5, 1.0]

                                                        
        self._last_vm_skipped = getattr(self, "_last_vm_skipped", 0) + skipped
        self._last_vm_steps_left = max_steps
        return self._clamp_vec4(pos), self._clamp_vec4(col, 0.0, 1.0), executed

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
        self._last_vm_skipped = 0
        self._last_vm_steps_left = 0
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
            f"executed ~{max(executed_counts or [0])} VM ops/vertex; skipped approx {int(getattr(self, '_last_vm_skipped', 0))}; {light_state}; "
            f"material {self.material_var.get()}."
        )
        if fallback:
            self._last_render_note += " Output collapsed/missing, so the preview is using fallback mesh positions."
        self.info_var.set(self._last_render_note)

__all__ = [name for name in globals() if not name.startswith("__")]

# 3DS Shader Modifier
- A Custom-Disassembler, and Shader Editor/Modifier for (*.shbin) for nearly all Nintendo 3DS Games.
- If you found this repo helpful, or this tool. Please star or give me a follow `^_^`.


---


## Core Shader Editing
- SHBIN / DVLB / DVLP / DVLE loading
- SHBIN saving
- DVLE table inspection
- DVLP opcode stream inspection
- Constant table editing
- Opcode word editing
- Operand descriptor editing
- Hex view
- Raw table view

## PICA200 Instruction Editing
- Instruction decoder
- Instruction encoder
- Mnemonic-based instruction editing
- Raw instruction word editing
- ASM line editing
- Arithmetic instruction editing
- Flow-control instruction editing
- CMP instruction editing
- MAD / MADI instruction support
- NOP insertion
- Instruction deletion / shift-up editing
- ASM insertion near DVLE end

## Assembly Features
- Full ASM export
- Full ASM import
- Reassemblable ASM output
- Indexed ASM line support
- Label support
- `.word` raw instruction support
- Source line comments
- Opcode metadata comments
- DVLE entrypoint annotations

## Symbol Features
- Register symbol table editor
- Global register aliases
- Per-DVLE register aliases
- Symbol map import
- Symbol map export
- Symbol-aware register dropdowns
- Symbol-aware ASM parsing
- Input register symbol mapping
- Output register symbol mapping
- Constant register symbol mapping
- Label symbol usage

## Safety / Validation
- Opcode range validation
- DVLE range validation
- Missing END detection
- Opdesc reference validation
- Branch target validation
- Constant register validation
- Output register validation
- Temp register read/write analysis
- 5-bit vs 7-bit source slot safety
- Invalid register-slot prevention
- Unused opdesc detection
- Warning / error issue panel

## Analysis Features
- Register analysis tab
- Register read tracking
- Register write tracking
- Register lifetime tracking
- Dependency analysis
- Control-flow graph tab
- Basic block detection
- Branch edge visualization
- Fallthrough edge visualization

## UI / Workflow Features
- Multi-pane editor layout
- Always-visible 3D shader preview
- Resizable preview pane
- Resizable tree / editor panes
- Horizontal tree scrolling
- Toolbar horizontal scrolling
- Search / filter box
- Auto-fit tree columns
- Disabled unused instruction fields
- Dropdown-based register selection
- Dropdown-based mnemonic selection
- Instruction-format help text
- Symbol management toolbar
- CFG toolbar action
- Register analysis toolbar action

## Preview Features
- 3D preview window/pane
- Mesh preview
- Light source preview
- Shader-ish visualization preview
- Auto-refresh preview hooks

## Import / Export Features
- JSON export
- Constant JSON import
- Constants CSV export
- Disassembly export
- Full ASM export
- Full ASM import
- Symbol map export
- Symbol map import
- SHBIN save-as workflow

## Main Headline Features

- Full ASM import/export
- Direct ASM line editing
- Symbol table editor
- Register aliasing
- Symbol-aware disassembly
- Symbol-aware ASM assembly
- Stronger shader safety validation
- Register usage analysis
- Control-flow graph viewer
- Better instruction editing UI
- Safer register-slot encoding
- Resizable multi-pane layout
- Always-visible 3D preview

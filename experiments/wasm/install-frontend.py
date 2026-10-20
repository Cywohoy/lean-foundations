"""Install the tested editor adapter into an isolated, patched Lean source tree."""
from pathlib import Path
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('lean_source', type=Path)
args = parser.parse_args()
here = Path(__file__).resolve().parent
source = args.lean_source.resolve()
assert (source / 'src/Lean/Shell.lean').is_file(), source
frontend = (here / 'Frontend.lean').read_text(encoding='utf-8')
frontend = frontend.split('\ndef main (args : List String)')[0]
frontend_path = source / 'src/Lean/BrowserFrontend.lean'
if not frontend_path.exists() or frontend_path.read_text(encoding='utf-8') != frontend:
    frontend_path.write_text(frontend, encoding='utf-8', newline='\n')
shell_path = source / 'src/Lean/Shell.lean'
shell = shell_path.read_text(encoding='utf-8')
if 'import Lean.BrowserFrontend' not in shell:
    shell = shell.replace('import Lean.Compiler.InitAttr', 'import Lean.BrowserFrontend\nimport Lean.Compiler.InitAttr', 1)
if '  let document ← AmpleBrowser.elaborate' not in shell:
    start = shell.index('  let opts : Options := {}', shell.index('def wasmCompile '))
    end = shell.index('  -- Output messages as JSON', start)
    shell = shell[:start] + '''  let document ← AmpleBrowser.elaborate code fileName (some env)
  wasmLastDocument.set (some document)
  let msgLog := document.messages

''' + shell[end:]
shell = shell.replace('let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx',
                      'let (header, _, _) ← Parser.parseHeader inputCtx', 1)
cache_marker = 'private initialize wasmEnvCache :'
if 'private initialize wasmLastDocument' not in shell:
    start = shell.index(cache_marker)
    shell = shell[:start] + '''private initialize wasmLastDocument : IO.Ref (Option AmpleBrowser.Document) ← IO.mkRef none

''' + shell[start:]
if '@[export lean_wasm_goals]' not in shell:
    start = shell.index('/--\nReset the WASM environment cache.')
    shell = shell[:start] + '''/-- Query the most recently compiled document using zero-based UTF-16 coordinates. -/
@[export lean_wasm_goals]
def wasmGoals (line character : UInt32) : IO UInt32 := do
  let some document ← wasmLastDocument.get
    | IO.println (Json.mkObj [("found", toJson false), ("goals", Json.arr #[])]).compress
      return 1
  let state ← AmpleBrowser.goalsAt document ⟨line.toNat, character.toNat⟩
  IO.println state.compress
  return 0

''' + shell[start:]
shell = shell.replace('def wasmReset : IO Unit := do\n  wasmEnvCache',
                      'def wasmReset : IO Unit := do\n  wasmLastDocument.set none\n  wasmEnvCache', 1)
if shell_path.read_text(encoding='utf-8') != shell:
    shell_path.write_text(shell, encoding='utf-8', newline='\n')

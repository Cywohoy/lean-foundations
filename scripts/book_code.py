"""Export checked chapter code for native exercise files and browser contexts."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ["Proof", "SetsFunctions", "NumbersRelations", "CardinalityChapter"]
LEGACY = {
    "Introduction": "Proof", "Proofs": "Proof",
    "Sets": "SetsFunctions", "Functions": "SetsFunctions",
    "Numbers": "NumbersRelations", "Relations": "NumbersRelations",
    "FiniteCardinality": "CardinalityChapter", "InfiniteCardinality": "CardinalityChapter",
    "Cardinality": "CardinalityChapter", "Preliminaries": "NumbersRelations",
}

def library_import(name):
    if name.startswith("AlgebraBook.Tactic."):
        return name.replace("AlgebraBook.Tactic.", "Ample.Tactic.")
    if name == "AlgebraBook.Meta.Notation":
        return "Ample.Notation"
    unit = name.removeprefix("AlgebraBook.")
    unit = LEGACY.get(unit, unit)
    if unit in CHAPTERS:
        return "AmpleBrowserContext.Book." + unit
    if name.startswith("AlgebraBook."):
        raise ValueError("Unsupported browser import: " + name)
    return name

def translate(source):
    imports = list(dict.fromkeys(library_import(n) for n in re.findall(r"^import (\S+)\s*$", source, re.M)))
    body = re.sub(r"^import \S+[ \t]*\n?", "", source, flags=re.M)
    body = re.sub(r"^export_course_compat[ \t]*\n?", "", body, flags=re.M)
    return "".join("import " + n + "\n" for n in imports) + "\n" + body

def export_module(source):
    imports, chunks = [], []
    for kind, flags, body in re.findall(
            r"^```(savedLean|savedImport)([^\n]*)\n(.*?)^```[ \t]*$", source, re.M | re.S):
        if kind == "savedImport":
            imports.append(body)
        elif "-keep" not in flags.split():
            if re.search(r"\b(sorry|axiom)\b", re.sub(r"--[^\n]*", "", body)):
                raise ValueError("Unfinished code cannot become a chapter dependency")
            chunks.append(body)
    return translate("\n".join(imports + chunks))

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "_out/browser-code")
    args = parser.parse_args()
    for chapter in CHAPTERS:
        path = args.output / "AmpleBrowserContext/Book" / (chapter + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(export_module((ROOT / "AlgebraBook" / (chapter + ".lean")).read_text(encoding="utf-8")),
                        encoding="utf-8")
    print(f"Exported {len(CHAPTERS)} checked chapter modules to {args.output}")

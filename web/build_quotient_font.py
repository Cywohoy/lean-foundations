"""Build the two quotient brackets from the bundled Cascadia Code font.

Requires fonttools[woff]. Run from any working directory. No download is needed.
The component brackets retain Cascadia's TrueType instructions. Their horizontal
arms are shortened, and component offsets are rounded to the pixel grid.
"""

from pathlib import Path

from fontTools import subset
from fontTools.ttLib import TTFont
from fontTools.ttLib.tables._g_l_y_f import Glyph, GlyphComponent, ROUND_XY_TO_GRID
from fontTools.varLib.instancer import instantiateVariableFont


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "assets/fonts/BookQuotientSymbols-Cascadia.woff2"


def build() -> None:
    font = instantiateVariableFont(
        TTFont(ROOT / "assets/fonts/CascadiaCode.woff2"),
        {"wght": 400},
        inplace=True,
    )
    source = font.getBestCmap()
    shapes = [
        (0x27E6, ord("["), (6, 7, 10, 11), 760, (-140, 220)),
        (0x27E7, ord("]"), (4, 5, 8, 9), 440, (-220, 140)),
    ]
    for codepoint, source_codepoint, arm_points, arm_x, offsets in shapes:
        base_name = source[source_codepoint]
        base = font["glyf"][base_name]
        if base.isComposite() or len(base.coordinates) != 12:
            raise ValueError("Cascadia bracket outlines changed; review the point mapping.")
        for point in arm_points:
            base.coordinates[point] = (arm_x, base.coordinates[point][1])
        base.recalcBounds(font["glyf"])

        name = f"quotient{codepoint:X}"
        glyph = Glyph()
        glyph.numberOfContours = -1
        glyph.components = []
        for offset in offsets:
            component = GlyphComponent()
            component.glyphName = base_name
            component.x, component.y = offset, 0
            component.flags = ROUND_XY_TO_GRID
            glyph.components.append(component)
        font["glyf"][name] = glyph
        font["hmtx"][name] = (1200, 0)
        font.setGlyphOrder(list(dict.fromkeys(font.getGlyphOrder() + [name])))
        for table in font["cmap"].tables:
            if table.isUnicode():
                table.cmap[codepoint] = name

    options = subset.Options()
    options.name_IDs = ["*"]
    options.name_languages = ["*"]
    options.name_legacy = True
    subsetter = subset.Subsetter(options=options)
    subsetter.populate(unicodes=[0x27E6, 0x27E7])
    subsetter.subset(font)
    for name, glyph in font["glyf"].glyphs.items():
        if glyph.isComposite():
            glyph.recalcBounds(font["glyf"])
            font["hmtx"][name] = (1200, glyph.xMin)

    names = {
        1: "Book Quotient Symbols", 2: "Regular",
        3: "BookQuotientSymbols-Cascadia-1",
        4: "Book Quotient Symbols Regular",
        6: "BookQuotientSymbols-Cascadia",
        16: "Book Quotient Symbols", 17: "Regular",
        18: "Book Quotient Symbols Regular", 25: "BookQuotientSymbols",
    }
    for record in font["name"].names:
        if record.nameID in names:
            record.string = names[record.nameID].encode(record.getEncoding())
    font.flavor = "woff2"
    font.save(OUTPUT)
    print(f"Wrote {OUTPUT} ({OUTPUT.stat().st_size} bytes)")


if __name__ == "__main__":
    build()

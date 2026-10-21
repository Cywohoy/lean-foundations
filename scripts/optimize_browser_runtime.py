"""Defer Emscripten 4.0.22's export-index scan until it is actually needed.

Dynamic symbol lookup needs an export index only when it inserts a new function
into the WASM table for pthread catch-up. Unknown symbols, data symbols, and
functions already in the table need no enumeration. Preserve that catch-up
protocol and avoid assuming that a library's export set never changes.
This transforms generated glue, not Lean's proof checker or the SDK checkout.
"""
import argparse
from pathlib import Path

MARKER = '/* ample-dlsym-lazy-index */'


def optimize(text):
    if MARKER in text:
        return text
    start = text.index('function __dlsym_js(')
    end = text.index('__dlsym_js.sig=', start)
    original = text[start:end]
    old = 'newSymIndex=Object.keys(lib.exports).indexOf(symbol);if(newSymIndex==-1||lib.exports[symbol].stub)'
    new = 'if(!Object.prototype.propertyIsEnumerable.call(lib.exports,symbol)||lib.exports[symbol].stub)'
    insert = 'result=addFunction(result,result.sig);'
    if original.count(old) != 1 or original.count(insert) != 1 or 'orig$' in original:
        raise ValueError('Unsupported Emscripten dlsym implementation; inspect it before updating this transform')
    updated = original.replace(old, new).replace(insert,
        insert + 'newSymIndex=Object.keys(lib.exports).indexOf(symbol);')
    return text[:start] + MARKER + updated + text[end:]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('runtime', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = args.runtime.read_text(encoding='utf-8')
    output = args.output or args.runtime
    output.write_text(optimize(text), encoding='utf-8', newline='\n')
    print(f'Prepared deferred symbol-index lookup: {output}')

"""Serve the same WASM textbook locally as on the public site; no compiler API."""
import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PUBLIC = ROOT / '_out/pages'


class PreviewHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(PUBLIC), **kwargs)

    def end_headers(self):
        # Local hosting can set these directly. GitHub Pages uses the COI worker.
        self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
        self.send_header('Cross-Origin-Embedder-Policy', 'require-corp')
        super().end_headers()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args()
    index = PUBLIC / 'index.html'
    if not index.is_file() or 'content="wasm"' not in index.read_text(encoding='utf-8'):
        raise SystemExit('Prepare the WASM textbook first: python scripts/prepare_pages.py')
    server = ThreadingHTTPServer(('127.0.0.1', args.port), PreviewHandler)
    server.daemon_threads = True
    print(f'Textbook with browser Lean: http://127.0.0.1:{args.port}/', flush=True)
    print('Proofs run in the browser. No native Lean server is started.', flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    main()

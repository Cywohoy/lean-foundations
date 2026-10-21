"""Serve the same WASM textbook locally as on the public site; no compiler API."""
import argparse
import socket
from urllib.parse import urlsplit
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PUBLIC = ROOT / '_out/pages'


class PreviewServer(ThreadingHTTPServer):
    # On Windows, reusable sockets can let an older preview share the port.
    allow_reuse_address = not hasattr(socket, 'SO_EXCLUSIVEADDRUSE')

    def server_bind(self):
        if hasattr(socket, 'SO_EXCLUSIVEADDRUSE'):
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        super().server_bind()


class PreviewHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(PUBLIC), **kwargs)

    def end_headers(self):
        # Fonts are stable bundled files. Re-fetching them on every refresh
        # defeats browser font caching and makes fallback text flash again.
        suffix = Path(urlsplit(self.path).path).suffix.lower()
        self.send_header('Cache-Control', 'public, max-age=86400' if suffix in
                         ('.woff', '.woff2', '.ttf', '.otf') else 'no-store')
        # Local hosting can set these directly. GitHub Pages uses the COI worker.
        self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
        self.send_header('Cross-Origin-Embedder-Policy', 'require-corp')
        super().end_headers()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args()
    index = PUBLIC / 'foundations/index.html'
    if not index.is_file() or 'content="wasm"' not in index.read_text(encoding='utf-8'):
        raise SystemExit('Prepare the WASM textbook first: python scripts/prepare_pages.py')
    server = PreviewServer(('127.0.0.1', args.port), PreviewHandler)
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

"""Local-only editorial workspace. Starts only when explicitly run by its user."""
from __future__ import annotations

import argparse
from http.server import BaseHTTPRequestHandler, HTTPServer
import json
from pathlib import Path
import secrets
import sys
import webbrowser

from review_state import ReviewError, ReviewStore

ASSETS = {"/": ("index.html", "text/html; charset=utf-8"),
          "/app.js": ("app.js", "text/javascript; charset=utf-8"),
          "/style.css": ("style.css", "text/css; charset=utf-8")}


class ReviewHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass

    def send(self, status, body, mime="application/json; charset=utf-8"):
        if not isinstance(body, bytes):
            body = json.dumps(body, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", mime)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'none'")
        self.end_headers()
        self.wfile.write(body)

    def allowed(self):
        host = f"127.0.0.1:{self.server.server_port}"
        return self.headers.get("Host") == host and self.headers.get("Origin", "http://" + host) == "http://" + host

    def do_GET(self):
        if not self.allowed():
            return self.send(403, {"error": "이 관리 도구는 로컬 주소에서만 사용할 수 있습니다."})
        if self.path in ASSETS:
            name, mime = ASSETS[self.path]
            content = (self.server.assets / name).read_bytes()
            if name == "index.html":
                content = content.replace(b"__REVIEW_TOKEN__", self.server.token.encode("ascii"))
            return self.send(200, content, mime)
        return self.send(404, {"error": "페이지를 찾을 수 없습니다."})

    def do_POST(self):
        if not self.allowed() or not secrets.compare_digest(self.headers.get("X-Review-Token", ""), self.server.token):
            return self.send(403, {"error": "관리 화면을 다시 열어 주세요."})
        if self.path != "/api":
            return self.send(404, {"error": "명령을 찾을 수 없습니다."})
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if not 0 < size <= 1_000_000:
                return self.send(413, {"error": "요청 크기를 확인하세요."})
            payload = json.loads(self.rfile.read(size))
            action = payload.get("action", "status")
            if action not in {"status", "scan", "source", "prepare"} and not isinstance(payload.get("revision"), int):
                raise ReviewError("화면의 상태 버전이 없습니다. 새로 불러오세요.")
            result = self.server.store.execute(action, payload.get("args", {}), payload.get("revision"))
            return self.send(200, result)
        except ReviewError as ex:
            return self.send(409, {"error": str(ex)})
        except (ValueError, KeyError, TypeError, AttributeError):
            return self.send(400, {"error": "요청 형식을 확인하세요."})
        except OSError:
            return self.send(500, {"error": "파일을 저장하지 못했습니다. 폴더 권한과 상태 파일을 확인하세요."})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--port", type=int, default=8766)
    parser.add_argument("--open", action="store_true")
    args = parser.parse_args()
    store = ReviewStore(args.root)
    store.load()
    # No background worker, file watcher, external bind, or manuscript write API.
    with HTTPServer(("127.0.0.1", args.port), ReviewHandler) as server:
        server.store = store
        server.assets = Path(__file__).resolve().parents[1] / "review/web"
        server.token = secrets.token_urlsafe(32)
        url = f"http://127.0.0.1:{server.server_port}/"
        print(f"검토 관리: {url}\n종료하려면 이 창에서 Ctrl+C를 누르세요.", flush=True)
        if args.open:
            webbrowser.open(url)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    try:
        main()
    except (OSError, ReviewError) as ex:
        print(str(ex), file=sys.stderr)
        raise SystemExit(1)

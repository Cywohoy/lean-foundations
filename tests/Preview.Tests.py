"""The local preview must serve the public WASM files without a compiler API."""
import importlib.util
from pathlib import Path
import sys
import threading
import unittest
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('wasm_preview', ROOT / 'web/serve.py')
preview = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preview)


class PreviewTests(unittest.TestCase):
    def test_wasm_files_and_no_native_api(self):
        self.assertNotIn('lean_rpc', sys.modules)
        server = preview.ThreadingHTTPServer(('127.0.0.1', 0), preview.PreviewHandler)
        server.daemon_threads = True
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        base = f'http://127.0.0.1:{server.server_port}'
        try:
            with urllib.request.urlopen(base + '/') as response:
                self.assertIn(b'href="foundations/"', response.read())
            with urllib.request.urlopen(base + '/foundations/') as response:
                self.assertIn(b'<meta name="book-mode" content="wasm">', response.read())
                self.assertEqual(response.headers['Cross-Origin-Embedder-Policy'], 'require-corp')
                self.assertEqual(response.headers['Cross-Origin-Opener-Policy'], 'same-origin')
            with urllib.request.urlopen(base + '/foundations/assets/web/exercise-model.js') as response:
                self.assertIn(b'exerciseModel', response.read())
            with self.assertRaises(urllib.error.HTTPError) as missing:
                urllib.request.urlopen(base + '/api/lean/status')
            self.assertEqual(missing.exception.code, 404)
            with self.assertRaises(urllib.error.HTTPError) as rejected:
                urllib.request.urlopen(urllib.request.Request(base + '/api/lean/check', data=b'{}',
                    headers={'Content-Type': 'application/json'}))
            self.assertEqual(rejected.exception.code, 501)
        finally:
            server.shutdown()
            server.server_close()
            thread.join()


if __name__ == '__main__':
    unittest.main()

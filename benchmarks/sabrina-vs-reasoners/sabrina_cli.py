"""Minimal standalone helper to invoke compiled SABRINA Lean 4 binaries."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parents[2]


def find_sabrina_binary(name: str) -> Path:
    env_key = f"SABRINA_{name.upper().replace('-', '_')}_BIN"
    if env_key in os.environ:
        p = Path(os.environ[env_key]).resolve()
        if p.is_file():
            return p
        raise FileNotFoundError(f"Configured {env_key} does not exist: {p}")
    candidate = REPO_ROOT / ".lake" / "build" / "bin" / name
    if candidate.is_file():
        return candidate
    raise FileNotFoundError(f"Could not find {name} binary at {candidate}. Run 'lake build {name}'.")


def run_ofn_query(
    *,
    ofn_path: Optional[str] = None,
    ofn_text: Optional[str] = None,
    query_ofn: str,
    scope_id: str = "query",
    timeout: float = 30.0,
) -> Tuple[bool, Dict[str, Any]]:
    """Invoke `sabrina-alc-query` on an OFN file or string and return `(ok, result_dict)`."""
    if ofn_text is None:
        if ofn_path is None:
            raise ValueError("Either ofn_path or ofn_text must be provided")
        ofn_text = Path(ofn_path).read_text(encoding="utf-8")
    bin_path = find_sabrina_binary("sabrina-alc-query")
    payload = ["sabrina-ofn-query-v1", scope_id, ofn_text, query_ofn]
    proc = subprocess.run(
        [str(bin_path)],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=True,
    )
    res = json.loads(proc.stdout)
    return bool(res.get("lean_verified", False)), res


def inject_ofn_extension(base_ofn: str, extra_axioms_ofn: str) -> str:
    """Insert prefix declarations and axioms from a benchmark fixture."""
    prefixes = []
    axioms = []
    for line in extra_axioms_ofn.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("Prefix("):
            prefixes.append(line)
        else:
            axioms.append("  " + line)

    if prefixes:
        start = base_ofn.index("Ontology(")
        base_ofn = base_ofn[:start] + "\n".join(prefixes) + "\n" + base_ofn[start:]
    if axioms:
        end = base_ofn.rindex(")")
        base_ofn = base_ofn[:end] + "\n" + "\n".join(axioms) + "\n" + base_ofn[end:]
    return base_ofn


class SabrinaSession:
    """Drive the persistent JSON-lines CLI used in the incremental benchmark."""

    def __init__(self) -> None:
        self._process = subprocess.Popen(
            [str(find_sabrina_binary("sabrina-session"))],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

    def _send(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        stdin = self._process.stdin
        stdout = self._process.stdout
        assert stdin is not None and stdout is not None
        stdin.write(json.dumps(payload) + "\n")
        stdin.flush()
        line = stdout.readline()
        if not line:
            raise RuntimeError("sabrina-session closed before replying")
        return json.loads(line)

    def load_tbox(self, *, ofn_text: str) -> Dict[str, Any]:
        return self._send({"cmd": "load_tbox", "id": "session-tbox", "ofn": ofn_text})

    def assert_fact(self, ofn_axiom: str, *, fact_id: str) -> Dict[str, Any]:
        return self._send({"cmd": "assert", "id": fact_id, "ofn": ofn_axiom})

    def retract_fact(self, fact_id: str) -> Dict[str, Any]:
        return self._send({"cmd": "retract", "id": fact_id})

    def query(self, ofn_query: str) -> Dict[str, Any]:
        return self._send({"cmd": "query", "ofn": ofn_query})

    def close(self) -> None:
        with self._process:
            assert self._process.stdin is not None
            self._process.stdin.close()
            try:
                self._process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._process.kill()

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

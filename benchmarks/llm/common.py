"""Shared helpers: everything goes through the emd binary, never a second decoder."""

import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
EMD = ROOT / "target" / "debug" / "emd"
MAX_STEPS = "1000000"
LINE_MAX = 32


def wrapped(dashes):
    """Flat dashes as lines the decoder accepts. The tasks show programs flat."""
    return "\n".join(dashes[i : i + LINE_MAX] for i in range(0, len(dashes), LINE_MAX))


def call(*args, stdin=b""):
    return subprocess.run([str(EMD), *args], input=stdin, capture_output=True, timeout=30)


def with_file(text, *args, stdin=b""):
    """Runs `emd <args> <file>` on text, writing its exact bytes with no newline added."""
    with tempfile.NamedTemporaryFile("wb", suffix=".emd") as f:
        f.write(text.encode("utf-8"))
        f.flush()
        return call(*args, f.name, stdin=stdin)

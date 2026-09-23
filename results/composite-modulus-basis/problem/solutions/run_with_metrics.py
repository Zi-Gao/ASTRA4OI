#!/usr/bin/env python3
"""Run one solver, enforce wall timeout, and record child rusage."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import resource
import subprocess
import time


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stderr", type=Path, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--timeout", type=float, required=True)
    args = parser.parse_args()

    started = time.perf_counter()
    returncode = None
    status = "finished"
    with args.input.open("rb") as stdin, args.output.open("wb") as stdout, \
            args.stderr.open("wb") as stderr:
        try:
            completed = subprocess.run(
                [str(args.binary)], stdin=stdin, stdout=stdout, stderr=stderr,
                timeout=args.timeout,
            )
            returncode = completed.returncode
            if returncode != 0:
                status = "RE"
        except subprocess.TimeoutExpired:
            status = "TLE"
    elapsed = time.perf_counter() - started
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    peak_rss = int(usage.ru_maxrss)
    if platform.system() != "Darwin":
        peak_rss *= 1024
    args.metrics.write_text(json.dumps({
        "status": status,
        "wall_seconds": elapsed,
        "user_seconds": usage.ru_utime,
        "system_seconds": usage.ru_stime,
        "peak_rss_bytes": peak_rss,
        "returncode": returncode,
    }) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

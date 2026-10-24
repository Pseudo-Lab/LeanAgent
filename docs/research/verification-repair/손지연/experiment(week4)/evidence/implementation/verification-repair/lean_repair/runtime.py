"""Fresh processes, distinct wall-clock budgets, raw logs and append-only trace."""
import json
import os
from pathlib import Path
import signal
import subprocess
import time

from .contracts import write_json


class Trace:
    def __init__(self, directory):
        self.directory = Path(directory).resolve()
        self.directory.mkdir(parents=True, exist_ok=False)

    def emit(self, event, **data):
        with (self.directory / "trace.jsonl").open("a") as stream:
            stream.write(json.dumps({"event": event, "time": time.time(), **data}, ensure_ascii=False) + "\n")


class ProcessRunner:
    def __init__(self, trace: Trace, seconds: float):
        self.trace = trace
        self.deadline = time.monotonic() + seconds

    @property
    def remaining(self):
        return max(0, self.deadline - time.monotonic())

    def run(self, argv, cwd, directory, timeout, stdin=None):
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        stdout, stderr = directory / "stdout.log", directory / "stderr.log"
        limit = min(timeout, self.remaining)
        result = {"argv": list(map(str, argv)), "cwd": str(cwd), "returncode": None,
                  "timeout": False, "process_error": None, "wall_time_limit": limit <= 0,
                  "stdout": str(stdout), "stderr": str(stderr), "timeout_seconds": limit}
        if stdin is not None:
            input_file = directory / "stdin.txt"
            input_file.write_text(stdin)
            result["stdin"] = str(input_file)
        start = time.monotonic()
        with stdout.open("xb") as out, stderr.open("xb") as err:
            if limit > 0:
                try:
                    # A regular file avoids pipe-buffer deadlocks for large REPL requests.
                    with (input_file.open("rb") if stdin is not None else open(os.devnull, "rb")) as incoming:
                        proc = subprocess.Popen(result["argv"], cwd=cwd, stdout=out, stderr=err,
                                                stdin=incoming, start_new_session=True)
                    try:
                        proc.wait(timeout=limit)
                    except subprocess.TimeoutExpired:
                        result["timeout"] = True
                        for sig in (signal.SIGTERM, signal.SIGKILL):
                            try:
                                os.killpg(proc.pid, sig)
                            except ProcessLookupError:
                                break
                            try:
                                proc.wait(timeout=1)
                                break
                            except subprocess.TimeoutExpired:
                                pass
                        proc.wait()
                    result["returncode"] = proc.returncode
                except OSError as exc:
                    result["process_error"] = str(exc)
        result["elapsed_ms"] = round((time.monotonic() - start) * 1000)
        result["wall_time_limit"] = result["wall_time_limit"] or self.remaining <= 0
        write_json(directory / "process.json", result)
        self.trace.emit("process", **result)
        return result

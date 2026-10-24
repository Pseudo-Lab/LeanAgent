"""Read subscription quota only. Never starts a thread or sends a model prompt."""
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import time


def read_quota(timeout=30, method="account/rateLimits/read"):
    if method not in ("account/rateLimits/read", "model/list"):
        raise ValueError("only quota/catalog reads are allowed")
    argv = ["codex", "app-server", "--listen", "stdio://", "-c", 'forced_login_method="chatgpt"',
            "-c", "features.apps=false", "-c", "features.plugins=false", "-c", "features.hooks=false"]
    proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                            start_new_session=True)
    poller = selectors.DefaultSelector()
    poller.register(proc.stdout, selectors.EVENT_READ)
    buffer = b""
    deadline = time.monotonic() + timeout
    def send(value):
        proc.stdin.write((json.dumps(value) + "\n").encode())
        proc.stdin.flush()
    def receive(wanted):
        nonlocal buffer
        while time.monotonic() < deadline:
            while b"\n" in buffer:
                line, buffer = buffer.split(b"\n", 1)
                try:
                    result = json.loads(line)
                except ValueError:
                    continue
                if result.get("id") == wanted:
                    return result
            if poller.select(max(0.01, deadline-time.monotonic())):
                chunk = os.read(proc.stdout.fileno(), 65536)
                if not chunk:
                    break
                buffer += chunk
        raise TimeoutError("subscription quota read unavailable")
    try:
        send(dict(id=1, method="initialize", params=dict(clientInfo=dict(
            name="week4_lean_experiment", title="Local Lean experiment", version="1.0"))))
        initialized = receive(1)
        if "error" in initialized:
            raise RuntimeError(initialized["error"])
        send(dict(method="initialized", params={}))
        send(dict(id=2, method=method, **({"params": {"limit": 100}} if method=="model/list" else {})))
        response = receive(2)
        if "error" in response:
            raise RuntimeError(response["error"])
        result = response["result"]
        if method == "model/list":
            return {"data": [{k: model.get(k) for k in ("id", "model", "displayName", "isDefault", "defaultReasoningEffort")}
                             for model in result.get("data", [])], "nextCursor": result.get("nextCursor")}
        # Preserve usage windows and credit flags, never account/email/auth credentials.
        return {k: result.get(k) for k in ("rateLimits", "rateLimitsByLimitId")}
    finally:
        poller.close()
        try:
            os.killpg(proc.pid, signal.SIGTERM)
            proc.wait(timeout=2)
        except (ProcessLookupError, subprocess.TimeoutExpired):
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()


def check_included_quota(data):
    buckets = data.get("rateLimitsByLimitId") or {"codex": data.get("rateLimits")}
    seen = False
    for bucket in buckets.values():
        if not isinstance(bucket, dict):
            continue
        if bucket.get("rateLimitReachedType"):
            return False
        credits = bucket.get("credits") or {}
        if bucket.get("spendControlReached") or credits.get("hasCredits") or credits.get("unlimited"):
            return False
        # Do not use a balance of purchased/workspace credits as an alternative to included quota.
        for key in ("primary", "secondary"):
            window = bucket.get(key)
            if window is not None:
                seen = True
                if window.get("usedPercent", 100) >= 90:
                    return False
    return seen


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--models", action="store_true")
    args = parser.parse_args()
    data = read_quota(method="model/list" if args.models else "account/rateLimits/read")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(dict(included_quota_available=check_included_quota(data), quota=data)))

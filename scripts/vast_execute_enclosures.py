#!/usr/bin/env python3
"""Provision a Vast.ai 8x RTX 4090 (or 4x H100) instance, run bit-exact 128-bit CUDA Chebyshev
enclosures for ALL 88 boxes of Candidate A (n=4..14, seams I, Rz, R4, Rx, b=31/2 & 23),
download the results JSON, and ALWAYS destroy the instance in a finally block!

Reads VAST_API_KEY from environment (passed via ~/Developer/bin/rs9-key get shared/VAST_API_KEY).
"""
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KEY = os.environ["VAST_API_KEY"]
SSH_KEY = sys.argv[1]
OFFER_ID = int(sys.argv[2]) if len(sys.argv) > 2 else None


def api(method: str, path: str, body=None):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(
        f"https://console.vast.ai/api/v0{path}",
        data=data,
        headers={
            "Authorization": f"Bearer {KEY}",
            "Content-Type": "application/json",
            "Accept": "application/json",
        },
        method=method,
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            raw = r.read().decode()
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as e:
        err_body = e.read().decode(errors="replace")
        raise RuntimeError(f"Vast API {method} {path} -> HTTP {e.code}: {err_body}")


def pick_offer():
    if OFFER_ID is not None:
        return OFFER_ID
    q = {
        "rentable": {"eq": True},
        "rented": {"eq": False},
        "verified": {"eq": True},
        "num_gpus": {"eq": 8},
        "gpu_name": {"eq": "RTX 4090"},
        "reliability": {"gte": 0.99},
        "cuda_max_good": {"gte": 12.2},
        "disk_space": {"gte": 40},
        "order": [["dph_total", "asc"]],
        "limit": 5,
    }
    offers = api("POST", "/bundles/", q).get("offers", [])
    if not offers:
        raise RuntimeError("No suitable 8x RTX 4090 offer found!")
    o = offers[0]
    print(f"Selected offer {o['id']}: {o['num_gpus']}x {o['gpu_name']} @ ${o['dph_total']:.2f}/hr "
          f"(RAM={o['cpu_ram']/1024:.0f}GB, rel={o['reliability']:.3f})", flush=True)
    return int(o["id"])


def main():
    offer_id = pick_offer()
    inst_id = None
    t_start = time.monotonic()
    try:
        print(f"Creating Vast.ai instance from offer {offer_id}...", flush=True)
        resp = api("PUT", f"/asks/{offer_id}/", {
            "client_id": "me",
            "image": "nvidia/cuda:12.4.1-devel-ubuntu22.04",
            "disk": 32,
            "runtype": "ssh",
            "ssh": True,
            "direct": True,
        })
        inst_id = resp.get("new_contract")
        if not inst_id:
            raise RuntimeError(f"Unexpected create response: {resp}")
        print(f"Instance {inst_id} created! Waiting for running + SSH...", flush=True)

        ssh_host = ssh_port = None
        for attempt in range(90):
            time.sleep(5)
            info = api("GET", f"/instances/{inst_id}/")
            inst = info.get("instances", info)
            if isinstance(inst, list):
                inst = inst[0]
            status = inst.get("actual_status") or inst.get("cur_state")
            ssh_host = inst.get("ssh_host")
            ssh_port = inst.get("ssh_port")
            if attempt % 4 == 0:
                print(f"  [{attempt*5:3d}s] status={status} ssh={ssh_host}:{ssh_port}", flush=True)
            if status == "running" and ssh_host and ssh_port:
                break
        else:
            raise RuntimeError("Timed out waiting for Vast.ai instance to start")

        ssh_opts = [
            "-i", SSH_KEY,
            "-o", "StrictHostKeyChecking=no",
            "-o", "UserKnownHostsFile=/dev/null",
            "-o", "ConnectTimeout=15",
            "-o", "BatchMode=yes",
        ]

        # Wait until sshd accepts connections
        for attempt in range(30):
            r = subprocess.run(
                ["ssh", *ssh_opts, "-p", str(ssh_port), f"root@{ssh_host}", "nvidia-smi -L && nvcc --version | tail -n 1"],
                capture_output=True, text=True
            )
            if r.returncode == 0:
                print("SSH connected!\n" + r.stdout.strip(), flush=True)
                break
            time.sleep(4)
        else:
            raise RuntimeError(f"SSH never became ready: {r.stderr}")

        # Install python3 + mpmath on Ubuntu CUDA devel image
        print("Installing python3-mpmath on remote node...", flush=True)
        subprocess.run(
            ["ssh", *ssh_opts, "-p", str(ssh_port), f"root@{ssh_host}",
             "mkdir -p /root/work && (python3 -c 'import mpmath' 2>/dev/null || "
             "(apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq python3 python3-mpmath))"],
            check=True,
        )

        # Upload our 5 tiny files
        files = [
            ROOT / "scripts" / "chebyshev_enclose_cuda.cu",
            ROOT / "scripts" / "vast_run_candidate_a.py",
            ROOT / "data" / "candidate_a_cpu_ref.json",
            ROOT / "round2_audit" / "round2-evidence" / "centers_15p5.tsv",
            ROOT / "round2_audit" / "round2-evidence" / "centers_23.tsv",
        ]
        print("Uploading 5 files to remote node...", flush=True)
        subprocess.run(
            ["scp", *ssh_opts, "-P", str(ssh_port), *[str(f) for f in files], f"root@{ssh_host}:/root/work/"],
            check=True,
        )

        # Run full bit-exact verification + n=11,12,13,14 across ALL 4 seams on all 8 GPUs!
        print("Launching remote 8-GPU bit-exact Chebyshev enclosure job...", flush=True)
        subprocess.run(
            ["ssh", *ssh_opts, "-p", str(ssh_port), f"root@{ssh_host}",
             "cd /root/work && python3 -u vast_run_candidate_a.py"],
            check=True,
        )

        # Download final JSON results
        dest = ROOT / "data" / "candidate_a_all88_enclosures.json"
        print(f"Downloading results to {dest}...", flush=True)
        subprocess.run(
            ["scp", *ssh_opts, "-P", str(ssh_port),
             f"root@{ssh_host}:/root/work/candidate_a_all88_enclosures.json", str(dest)],
            check=True,
        )
        print(f"SUCCESS! Downloaded {dest} in {time.monotonic() - t_start:.1f}s total!", flush=True)

    finally:
        if inst_id is not None:
            print(f"Destroying Vast.ai instance {inst_id}...", flush=True)
            try:
                api("DELETE", f"/instances/{inst_id}/")
                print(f"Instance {inst_id} destroyed cleanly!", flush=True)
            except Exception as e:
                print(f"WARNING: failed to destroy {inst_id}: {e}", flush=True)


if __name__ == "__main__":
    main()

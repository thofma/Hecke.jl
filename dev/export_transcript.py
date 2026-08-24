#!/usr/bin/env python3
"""Turn the Claude Code session log into a readable transcript.

    python3 dev/export_transcript.py [outfile]

Reads the newest .jsonl for this project and writes markdown: the prompts, the
replies, and a one-line summary of each tool call (with its command, if any).
Re-run it any time to refresh; it always reads the current state of the log.
"""
import json, sys, glob, os, datetime

PROJ = os.path.expanduser("~/.claude/projects/-home-simonbrandhorst--julia-dev-Hecke-src")
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser(
    "~/.julia/dev/Hecke/dev/transcript.md")

def sessions():
    """All session logs for this project, oldest first."""
    fs = glob.glob(os.path.join(PROJ, "*.jsonl"))
    def first_ts(f):
        with open(f) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if r.get("timestamp"):
                    return r["timestamp"]
        return ""
    return sorted(fs, key=first_ts)

def text_of(content):
    if isinstance(content, str):
        return content
    out = []
    if isinstance(content, list):
        for b in content:
            if not isinstance(b, dict):
                continue
            t = b.get("type")
            if t == "text":
                out.append(b.get("text", ""))
            elif t == "tool_use":
                inp = b.get("input", {}) or {}
                d = inp.get("description") or ""
                cmd = inp.get("command") or inp.get("file_path") or ""
                if isinstance(cmd, str) and len(cmd) > 400:
                    cmd = cmd[:400] + " ..."
                out.append("`[tool: %s]`%s%s" % (
                    b.get("name", "?"),
                    (" " + d) if d else "",
                    ("\n```\n" + cmd + "\n```") if cmd else ""))
    return "\n\n".join(x for x in out if x)

def main():
    srcs = sessions()
    if not srcs:
        print("no session log found", file=sys.stderr)
        return 1
    parts, nu, na = [], 0, 0
    for src in srcs:
      parts.append("# session `%s`\n" % os.path.basename(src)[:8])
      with open(src) as fh:
        for line in fh:
              line = line.strip()
              if not line:
                  continue
              try:
                  rec = json.loads(line)
              except json.JSONDecodeError:
                  continue
              if rec.get("type") not in ("user", "assistant"):
                  continue
              if rec.get("isSidechain"):
                  continue
              msg = rec.get("message") or {}
              body = text_of(msg.get("content"))
              if not body.strip():
                  continue
              # skip the tool results that come back as pseudo user turns
              if rec["type"] == "user" and isinstance(msg.get("content"), list) \
                 and any(isinstance(b, dict) and b.get("type") == "tool_result"
                         for b in msg["content"]):
                  continue
              ts = rec.get("timestamp", "")[:19].replace("T", " ")
              who = "Simon" if rec["type"] == "user" else "Claude"
              nu += rec["type"] == "user"
              na += rec["type"] == "assistant"
              parts.append("## %s%s\n\n%s\n" % (who, (" — " + ts) if ts else "", body))
    hdr = ("# Transcript: definite lattice isometry work\n\n"
           "Sources: %s\nExported: %s\n%d prompts, %d replies\n\n---\n"
           % (", ".join("`" + os.path.basename(f) + "`" for f in srcs),
              datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), nu, na))
    with open(OUT, "w") as fh:
        fh.write(hdr + "\n---\n\n".join(parts))
    print("wrote %s (%d prompts, %d replies, %d session(s))" % (OUT, nu, na, len(srcs)))
    return 0

sys.exit(main())

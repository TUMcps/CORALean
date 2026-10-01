#!/usr/bin/env python
"""GitLab CLI for CORALean: issues, merge requests, pipelines.

The token is never an argument and never lives in the repository. It is read
from `$CORALEAN_GITLAB_TOKEN`, then `$GITLAB_TOKEN`, then the file
`~/.config/coralean/gl.token` -- so any checkout, worktree or agent on this
machine reaches the API the same way, with nothing to pass along.

`git push` needs none of this: the system gitconfig sets credential.helper.

  gl.py issue list [label]         open issues, newest first
  gl.py issue show <iid>
  gl.py issue new <label> <title> <desc-file>
  gl.py issue note <iid> <text>    comment
  gl.py issue edit <iid> <desc-file>
  gl.py issue close <iid> <text>   comment, then close -- never close silently
  gl.py issue reopen <iid> <text>  comment, then reopen -- likewise

  gl.py mr list
  gl.py mr show <iid>
  gl.py mr new <branch> <title> <desc-file>
  gl.py mr note <iid> <text>
  gl.py mr edit <iid> <desc-file>
  gl.py mr merge <iid>             squash, delete source branch
  gl.py mr close <iid> <text>      comment, then close unmerged

  gl.py pipes [ref]                recent pipelines
  gl.py pipe cancel <pipeline-id>  cancel a running pipeline, e.g. one a newer push superseded
  gl.py pipe retry <pipeline-id>   retry its failed or cancelled jobs
  gl.py jobs <pipeline-id>
  gl.py log <job-id>               trace, last 200 lines
"""
import json, os, sys, urllib.request, urllib.error

if hasattr(sys.stdout, "reconfigure"):          # Lean identifiers are not cp1252
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

API = "https://gitlab.lrz.de/api/v4/projects/cps%2Fcoralean"
TOKEN_FILE = os.path.expanduser("~/.config/coralean/gl.token")


def token():
    for var in ("CORALEAN_GITLAB_TOKEN", "GITLAB_TOKEN"):
        if os.environ.get(var):
            return os.environ[var].strip()
    try:
        with open(TOKEN_FILE) as f:
            return f.read().strip()
    except OSError:
        sys.exit("no token: set $CORALEAN_GITLAB_TOKEN or write %s" % TOKEN_FILE)


def call(method, path, payload=None):
    data = json.dumps(payload).encode() if payload is not None else None
    req = urllib.request.Request(
        API + path, data=data, method=method,
        headers={"PRIVATE-TOKEN": token(), "Content-Type": "application/json"})
    try:
        return json.load(urllib.request.urlopen(req, timeout=90))
    except urllib.error.HTTPError as e:
        sys.exit("HTTP %d %s" % (e.code, e.read().decode()[:500]))


def call_all(path):
    """Every page, not just the first. GitLab defaults to 20 per page, so a
    plain GET on `notes` silently dropped everything past the twentieth -- and
    with `sort=asc` the ones dropped were the newest, which is exactly the half
    a reader needs. Correcting an issue by commenting on it only works if the
    comment can be read back."""
    out, page = [], 1
    while True:
        sep = "&" if "?" in path else "?"
        batch = call("GET", "%s%sper_page=100&page=%d" % (path, sep, page))
        out += batch
        if len(batch) < 100:
            return out
        page += 1


def note(kind, iid, text):
    call("POST", "/%s/%s/notes" % (kind, iid), {"body": text})
    print("commented on %s %s" % (kind[:-1], iid))


def edit(kind, iid, path):
    """Rewrite a description from a file, the way `new` reads one: a long
    description passed as an argument is what folded newlines into `<br>`."""
    with open(path, encoding="utf-8") as f:
        call("PUT", "/%s/%s" % (kind, iid), {"description": f.read()})
    print("rewrote %s %s description" % (kind[:-1], iid))


argv = sys.argv[1:]
if not argv:
    sys.exit(__doc__)
group, cmd, rest = argv[0], (argv[1] if len(argv) > 1 else ""), argv[2:]

if group == "issue":
    if cmd == "list":
        q = "/issues?state=opened&order_by=created_at&sort=asc"
        if rest:
            q += "&labels=" + rest[0]
        for i in call_all(q):
            print("#%-3d [%-16s] %s" % (i["iid"], ",".join(i["labels"])[:16], i["title"]))
    elif cmd == "show":
        i = call("GET", "/issues/%s" % rest[0])
        print("#%d %s" % (i["iid"], i["title"]))
        print("state: %s | labels: %s" % (i["state"], ", ".join(i["labels"])))
        print()
        print(i["description"] or "(no description)")
        for n in call_all("/issues/%s/notes?sort=asc" % rest[0]):
            if not n["system"]:
                print("\n--- %s:\n%s" % (n["author"]["username"], n["body"]))
    elif cmd == "new":
        with open(rest[2], encoding="utf-8") as f:
            desc = f.read()
        i = call("POST", "/issues",
                 {"title": rest[1], "description": desc, "labels": rest[0]})
        print("#%d %s" % (i["iid"], i["web_url"]))
    elif cmd == "note":
        note("issues", rest[0], rest[1])
    elif cmd == "edit":
        edit("issues", rest[0], rest[1])
    elif cmd == "close":
        note("issues", rest[0], rest[1])
        call("PUT", "/issues/%s" % rest[0], {"state_event": "close"})
        print("#%s closed" % rest[0])
    elif cmd == "reopen":
        note("issues", rest[0], rest[1])
        call("PUT", "/issues/%s" % rest[0], {"state_event": "reopen"})
        print("#%s reopened" % rest[0])
    else:
        sys.exit(__doc__)

elif group == "mr":
    if cmd == "list":
        for m in call_all("/merge_requests?state=opened"):
            print("!%-3d %-34s %-9s squash=%s  %s"
                  % (m["iid"], m["source_branch"], m["state"], m["squash"], m["title"]))
    elif cmd == "show":
        m = call("GET", "/merge_requests/%s" % rest[0])
        print("!%d %s -> %s" % (m["iid"], m["source_branch"], m["target_branch"]))
        print("state: %s | squash: %s | merge_status: %s"
              % (m["state"], m["squash"], m.get("detailed_merge_status")))
        print("TITLE:", m["title"])
        print(m["description"])
        for n in call_all("/merge_requests/%s/notes?sort=asc" % rest[0]):
            if not n["system"]:
                print("\n--- %s:\n%s" % (n["author"]["username"], n["body"]))
    elif cmd == "new":
        # Description from a file: passing it as an argument is what folded
        # newlines into <br> and needed undoing afterwards.
        with open(rest[2], encoding="utf-8") as f:
            desc = f.read()
        m = call("POST", "/merge_requests",
                 {"source_branch": rest[0], "target_branch": "main",
                  "title": rest[1], "description": desc, "squash": True,
                  "remove_source_branch": True})
        print("!%d %s" % (m["iid"], m["web_url"]))
    elif cmd == "note":
        note("merge_requests", rest[0], rest[1])
    elif cmd == "edit":
        edit("merge_requests", rest[0], rest[1])
    elif cmd == "close":
        note("merge_requests", rest[0], rest[1])
        call("PUT", "/merge_requests/%s" % rest[0], {"state_event": "close"})
        print("!%s closed" % rest[0])
    elif cmd == "merge":
        call("PUT", "/merge_requests/%s" % rest[0],
             {"squash": True, "remove_source_branch": True})
        m = call("PUT", "/merge_requests/%s/merge" % rest[0],
                 {"squash": True, "should_remove_source_branch": True})
        sha = m.get("merge_commit_sha") or m.get("squash_commit_sha") or "?"
        print("!%s -> %s  sha=%s" % (rest[0], m["state"], sha[:12]))
    elif cmd == "close":
        note("merge_requests", rest[0], rest[1])
        call("PUT", "/merge_requests/%s" % rest[0], {"state_event": "close"})
        print("!%s closed unmerged" % rest[0])
    else:
        sys.exit(__doc__)

elif group == "pipes":
    q = "/pipelines?per_page=10"
    if cmd:
        q += "&ref=" + cmd
    for p in call("GET", q):
        print("%-9d %-10s %-28s %s" % (p["id"], p["status"], p["ref"], p["created_at"]))

elif group == "pipe" and cmd in ("cancel", "retry") and rest:
    p = call("POST", "/pipelines/%s/%s" % (rest[0], cmd))
    print("%-9d %s" % (p["id"], p["status"]))

elif group == "jobs":
    for j in call("GET", "/pipelines/%s/jobs" % cmd):
        dur = j.get("duration") or 0
        print("%-9d %-12s %-10s %5.0fs" % (j["id"], j["name"], j["status"], dur))

elif group == "log":
    req = urllib.request.Request(API + "/jobs/%s/trace" % cmd,
                                 headers={"PRIVATE-TOKEN": token()})
    trace = urllib.request.urlopen(req, timeout=90).read().decode("utf-8", "replace")
    print("\n".join(trace.splitlines()[-200:]))

else:
    sys.exit(__doc__)

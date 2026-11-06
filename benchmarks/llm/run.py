#!/usr/bin/env python3
"""Sends tasks to a Claude model through the `claude` CLI and saves the answers.

usage: run.py MODEL [--condition C] [--reps N] [--easy N] [--jobs N] [--budget USD] [--out FILE]

One isolated call per task and repetition: no tools, no project or user settings,
no retries, docs/isa.md as the system prompt. Answers are saved exactly as they
arrive. A finished call is not repeated, so a stopped run can be resumed.

Conditions, what each one changes about the prompt:
  bare      the task as written
  explicit  adds that the reply goes to a strict decoder, and to skip Markdown
  schema    the answer travels in a JSON field, so no formatting channel exists
  plain     the task as written, with the system prompt free of Markdown
"""

import argparse
import hashlib
import codex_cli
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor

from common import ROOT
from score import PROGRAM_KINDS

HERE = pathlib.Path(__file__).parent
TIMEOUT = 900
CONDITIONS = ("bare", "explicit", "schema", "plain")
SCHEMA = json.dumps({
    "type": "object",
    "properties": {"answer": {"type": "string"}},
    "required": ["answer"],
    "additionalProperties": False,
})


def select(tasks, per_kind):
    """The first `per_kind` tasks of each kind, in file order: the same set for every model."""
    seen = {}
    chosen = []
    for task in tasks:
        seen[task["kind"]] = seen.get(task["kind"], 0) + 1
        if seen[task["kind"]] <= per_kind:
            chosen.append(task)
    return chosen


def experiment(tasks, easy):
    """All hard tasks and the first `easy` easy tasks of each kind."""
    easy_tasks = select([t for t in tasks if t.get("tier", "easy") == "easy"], easy)
    return easy_tasks + [t for t in tasks if t.get("tier") == "hard"]


def prompt_for(task, condition):
    if condition != "explicit":
        return task["prompt"]
    # A program needs its newlines, and a listing too: only a copied string has none.
    spacing = "spaces or newlines" if task["kind"] == "copy" else "spaces"
    return (
        task["prompt"]
        + "\nYour entire reply goes unchanged into a strict decoder that rejects anything "
        + f"else: no Markdown, code fences, backticks, bold or extra {spacing}."
    )


def plain_text(markdown):
    """The same document with nothing of Markdown left: no headings, tables, code spans or links."""
    lines = []
    for line in markdown.splitlines():
        if re.fullmatch(r"\|[\s|:-]+\|", line):
            continue
        if line.startswith("|"):
            line = "  ".join(cell.strip() for cell in line.strip("|").split("|"))
        line = re.sub(r"^#+ ", "", line)
        line = re.sub(r"\[([^]]+)\]\([^)]+\)", r"\1", line)
        lines.append(line.replace("`", "").replace("**", "").strip())
    return "\n".join(lines)


def system_prompt(condition):
    document = (ROOT / "docs" / "isa.md").read_text(encoding="utf-8")
    return plain_text(document) if condition == "plain" else document


def ask(cli, model, system, prompt, condition):
    """The CLI's JSON result for one call. The temporary cwd keeps project files out."""
    command = [
        cli, "-p", "--model", model, "--system-prompt", system, "--tools", "",
        "--setting-sources", "", "--strict-mcp-config", "--disable-slash-commands",
        "--no-session-persistence", "--output-format", "json",
    ]
    if condition == "schema":
        command += ["--json-schema", SCHEMA]
    with tempfile.TemporaryDirectory() as cwd:
        done = subprocess.run(
            command, input=prompt.encode("utf-8"), capture_output=True, cwd=cwd, timeout=TIMEOUT
        )
    if done.returncode != 0:
        raise RuntimeError((done.stdout + done.stderr).decode("utf-8", "replace")[:500])
    return json.loads(done.stdout)


def answer_of(result, condition):
    if condition != "schema":
        return result["result"]
    return result["structured_output"]["answer"]


def run(model, tasks, out, condition="bare", reps=1, jobs=1, budget=None, cli=None, provider="claude", effort="medium"):
    """Appends one line per finished call. Returns the number of failed calls."""
    cli = cli or provider
    if provider == "codex" and budget is not None:
        raise ValueError("Codex subscription usage has no reported dollar cost; use --limit instead.")
    if provider == "codex":
        name = "system-prompt-plain.txt" if condition == "plain" else "system-prompt.md"
        system = (HERE / "results" / "v3" / name).read_text(encoding="utf-8")
    else:
        system = system_prompt(condition)
    done = set()
    if out.exists():
        with out.open(encoding="utf-8") as previous:
            for line in previous:
                item = json.loads(line)
                if provider == "codex" and (item.get("provider") != provider or item.get("reasoning_effort") != effort
                        or item.get("requested") != model or item.get("condition") != condition):
                    raise ValueError("Existing answers use a different protocol; choose another output file.")
                done.add((item["id"], item.get("rep", 0)))
    lock = threading.Lock()
    tally = {"failures": 0, "cost": 0.0, "started": 0}
    stopped = threading.Event()
    sink = open(out, "a", encoding="utf-8")

    def one(work):
        task, rep = work
        with lock:
            if stopped.is_set() or (budget is not None and tally["cost"] >= budget):
                return
            tally["started"] += 1
        try:
            result = (codex_cli.ask(cli, model, system, prompt_for(task, condition), condition, effort)
                      if provider == "codex" else ask(cli, model, system, prompt_for(task, condition), condition))
            if result.get("is_error"):
                raise RuntimeError(str(result.get("result"))[:500])
            response = answer_of(result, condition)
        except (RuntimeError, KeyError, TypeError, subprocess.TimeoutExpired, json.JSONDecodeError) as e:
            with lock:
                print(f"{task['id']} rep {rep}: {e}", file=sys.stderr)
                tally["failures"] += 1
                if provider == "codex" and tally["failures"] >= 3:
                    stopped.set()
            return
        line = {
            "id": task["id"],
            "rep": rep,
            "condition": condition,
            "response": response,
            "requested": model,
            "served": sorted(result.get("modelUsage", {})),
            "stop_reason": result.get("stop_reason"),
            "output_tokens": result.get("usage", {}).get("output_tokens"),
            "cost_usd": result.get("total_cost_usd"),
        }
        if provider == "codex":
            line.update(provider=provider, reasoning_effort=effort, usage=result["usage"],
                        system_prompt_sha256=hashlib.sha256(system.encode("utf-8")).hexdigest(),
                        input_tokens=result["usage"].get("input_tokens"),
                        cached_input_tokens=result["usage"].get("cached_input_tokens"))
        with lock:
            tally["cost"] += line["cost_usd"] or 0
            sink.write(json.dumps(line, ensure_ascii=True) + "\n")
            sink.flush()

    work = [(t, r) for r in range(reps) for t in tasks if (t["id"], r) not in done]
    with ThreadPoolExecutor(jobs) as pool:
        list(pool.map(one, work))
    sink.close()
    cost = f"${tally['cost']:.2f}" if provider == "claude" else "subscription; dollar cost unavailable"
    print(f"{model} {condition}: {tally['started']} calls, {tally['failures']} failed, {cost}", file=sys.stderr)
    return tally["failures"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("model")
    parser.add_argument("--provider", choices=("claude", "codex"), default="claude")
    parser.add_argument("--effort", choices=("low", "medium", "high"), default="medium")
    parser.add_argument("--limit", type=int, help="maximum number of selected tasks (for a pilot)")
    parser.add_argument("--condition", choices=CONDITIONS, default="bare")
    parser.add_argument("--reps", type=int, default=1)
    parser.add_argument("--easy", type=int, default=3, help="easy tasks per kind, all hard tasks always run")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--budget", type=float, help="stop starting calls past this many dollars")
    parser.add_argument("--out", type=pathlib.Path)
    args = parser.parse_args()
    tasks = [json.loads(line) for line in (HERE / "tasks.jsonl").read_text(encoding="ascii").splitlines()]
    directory = "codex-v1" if args.provider == "codex" else "v3"
    out = args.out or HERE / "results" / directory / f"{args.model}.{args.condition}.jsonl"
    out.parent.mkdir(parents=True, exist_ok=True)
    chosen = experiment(tasks, args.easy)
    if args.limit is not None:
        if args.limit < 1:
            parser.error("--limit must be positive")
        chosen = chosen[:args.limit]
    failed = run(args.model, chosen, out, args.condition, args.reps, args.jobs, args.budget,
                 provider=args.provider, effort=args.effort)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

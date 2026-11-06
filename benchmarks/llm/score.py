#!/usr/bin/env python3
"""Scores model answers. usage: score.py [--answered] responses.jsonl

--answered scores only the tasks in the file, for a sample of the suite. Without
it a missing answer scores zero.

Each line of responses.jsonl: {"id": ..., "response": ...}. A program counts only
if the real compiler accepts the exact bytes of the answer and the result does what
the task asks. Levels are reported separately: lexical, compiles, runs, task. The
`unwrapped` column scores the task again without Markdown, and `content` also
ignores the line limit, to separate a wrong program from a right one in the wrong
clothes. The strict score stays the result, because the language rejects those clothes.
"""

import json
import pathlib
import sys
from collections import defaultdict

from common import MAX_STEPS, with_file, wrapped

HERE = pathlib.Path(__file__).parent
ALPHABET = set("-‐‑‒–—―−")
PROGRAM_KINDS = {"generate", "complete", "repair"}


def score(task, response):
    """The levels this answer reached, each a bool, or None if it does not apply."""
    kind = task["kind"]
    answer = response.strip()
    if kind == "explain":
        return {"task": [line.strip() for line in answer.splitlines()] == task["expected_listing"]}
    if kind == "distinguish":
        return {"task": answer == str(task["expected_index"])}
    if kind == "copy":
        return {"task": answer == task["expected_text"]}
    # What a consumer would save: the given start, as the prompt shows it, then the answer's exact bytes.
    prefix = task.get("prefix")
    source = (wrapped(prefix) + "\n" if prefix else "") + response
    dashes = source.replace("\n", "")
    lexical = bool(dashes) and set(dashes) <= ALPHABET
    compiles = lexical and with_file(source, "check").returncode == 0
    if not compiles:
        return {"lexical": lexical, "compiles": False, "runs": False, "task": False}
    run = with_file(source, "run", "--max-steps", MAX_STEPS, stdin=task.get("input", "").encode())
    halted = run.returncode == 0
    correct = halted and run.stdout == task["expected_output"].encode()
    return {"lexical": True, "compiles": True, "runs": halted, "task": correct}


def unwrap(task, response):
    """The answer without code fences, surrounding backticks, bold or spaces. A program
    keeps its lines, which are part of the language; a copied string has none."""
    lines = [l for l in response.splitlines() if not l.strip().startswith("```")]
    text = "\n".join(lines).strip().strip("`*").strip()
    if task["kind"] == "copy":
        return "".join(text.split())
    if task["kind"] in PROGRAM_KINDS:
        return "\n".join("".join(line.split()) for line in text.splitlines())
    return text


def relayout(response):
    """The same dashes in lines the compiler accepts, for an answer that passed the limit."""
    return wrapped("".join(response.split()))


def main():
    tasks = {}
    for line in open(HERE / "tasks.jsonl", encoding="ascii"):
        task = json.loads(line)
        tasks[task["id"]] = task
    responses = {}
    answered_only = "--answered" in sys.argv
    path = next(a for a in sys.argv[1:] if a != "--answered")
    for line in open(path, encoding="utf-8"):
        item = json.loads(line)
        responses[item["id"]] = item["response"]

    totals = defaultdict(lambda: defaultdict(int))
    counts = defaultdict(int)
    for task_id, task in tasks.items():
        if answered_only and task_id not in responses:
            continue
        counts[task["kind"]] += 1
        # A missing answer scores zero: skipping a task cannot raise the score.
        for level, reached in score(task, responses.get(task_id, "")).items():
            totals[task["kind"]][level] += int(reached)
        answer = unwrap(task, responses.get(task_id, ""))
        totals[task["kind"]]["unwrapped"] += int(score(task, answer)["task"])
        if task["kind"] in PROGRAM_KINDS:
            answer = relayout(answer)
        totals[task["kind"]]["content"] += int(score(task, answer)["task"])

    print(f"{'kind':<12} {'n':>3} {'lexical':>8} {'compiles':>9} {'runs':>5} {'task':>5} {'unwrapped':>10} {'content':>8}")
    for kind, n in counts.items():
        t = totals[kind]
        cells = [t[l] if kind in PROGRAM_KINDS else "-" for l in ("lexical", "compiles", "runs")]
        print(f"{kind:<12} {n:>3} {cells[0]:>8} {cells[1]:>9} {cells[2]:>5} {t['task']:>5} {t['unwrapped']:>10} {t['content']:>8}")
    total = sum(t["task"] for t in totals.values())
    clothed = sum(t["unwrapped"] for t in totals.values())
    content = sum(t["content"] for t in totals.values())
    print(f"total task score: {total}/{sum(counts.values())}, unwrapped {clothed}, content {content}")


if __name__ == "__main__":
    main()

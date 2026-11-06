#!/usr/bin/env python3
"""Checks the scorer: a perfect answer sheet must score everything, and damaged
answers must lose exactly what they should."""

import json
import os
import pathlib
import re
import tempfile

from analyze import classify, compiles, counts, exact_mcnemar, figure_svg, figure_tikz, load, summarize, write_latex, substitutions, wilson, wrapper
from common import ROOT, wrapped, with_file
from run import answer_of, plain_text, prompt_for, run, select, system_prompt
from score import relayout, score, unwrap

HERE = pathlib.Path(__file__).parent


def answer(task):
    kind = task["kind"]
    if kind == "explain":
        return "\n".join(task["expected_listing"])
    if kind == "distinguish":
        return str(task["expected_index"])
    if kind == "copy":
        return task["expected_text"]
    text = task["expected_output"].replace("\n", "\\n")
    source = with_file(f'PRINT "{text}"\nHALT\n', "asm").stdout.decode("utf-8").replace("\n", "")
    return wrapped(source[len(task.get("prefix", "")):])


FAKE_CLI = """#!/bin/sh
cat > /dev/null
if [ -e "$FAKE_FAIL" ]; then echo '{"is_error": true, "result": "nope"}'; exit 0; fi
echo call >> "$FAKE_LOG"
cat <<'JSON'
{"result": "\\u2013\\u2012\\n", "modelUsage": {"m": {}}, "total_cost_usd": 0}
JSON
"""


def check_analysis(tasks):
    task = next(t for t in tasks if t["kind"] == "generate")
    right = answer(task)
    assert classify(task, right) == "clean"
    assert classify(task, f"```\n{right}\n```") == "wrapped"
    assert classify(task, "\u2013\u2012") == "wrong"
    # Right program, one line past the limit: the compiler refuses, so it is not clean.
    long_task = next(t for t in tasks if t["id"] == "generate-hard-0")
    long_right = answer(long_task)
    one_line = long_right.replace("\n", "")
    assert len(one_line) > 32
    assert classify(long_task, long_right) == "clean"
    assert classify(long_task, one_line) == "layout"
    assert classify(long_task, f"```\n{long_right}\n```") == "wrapped"
    assert classify(long_task, f"```\n{one_line}\n```") == "layout"
    assert wrapper(long_task, one_line) == "long line"
    assert wrapper(long_task, long_right) == "none"
    assert compiles(long_task, long_right) and not compiles(long_task, one_line)
    assert compiles(task, right) and not compiles(task, f"```\n{right}\n```")
    assert compiles(next(t for t in tasks if t["kind"] == "copy"), "x") is None
    assert wrapper(task, right) == "none"
    assert wrapper(task, f"```\n{right}\n```") == "code fence"
    assert wrapper(task, f"`{right}`") == "backticks"
    assert wrapper(task, " ".join(right)) == "spacing"
    assert wrapper(next(t for t in tasks if t["kind"] == "copy"), "-\n-") == "spacing"
    assert wrapper(task, "Here it is: " + right) == "spacing"
    listing = next(t for t in tasks if t["kind"] == "distinguish")
    assert wrapper(listing, "**3**") == "bold" and wrapper(listing, "3") == "none"
    # Known values: 2 of 10 is 20% in [5.67, 50.98]; one side only, of six pairs.
    low, high = wilson(2, 10)
    assert abs(low - 5.67) < 0.01 and abs(high - 50.98) < 0.01
    assert exact_mcnemar(0, 6) == 2 / 64 and exact_mcnemar(3, 3) == 1.0 and exact_mcnemar(0, 0) == 1.0
    # Cost: the failed answer was paid for too, so it weighs on the cost of a clean one.
    rows = [dict(cost=0.5, tokens=10, compiles=True, **{"class": "clean"}),
            dict(cost=1.5, tokens=30, compiles=False, **{"class": "wrong"})]
    c = counts(rows)
    assert (c["cost_usd"], c["cost_per_answer"], c["cost_per_clean"], c["tokens"]) == (2.0, 1.0, 2.0, 40)
    assert counts(rows[1:])["cost_per_clean"] is None
    assert (c["compiled"], c["programs"]) == (1, 2)
    swaps, distance = substitutions("abcd", "abxd")
    assert swaps[("c", "x")] == 1 and distance == 0.25
    assert substitutions("abcd", "abcd")[1] == 0


def check_report(tasks):
    """The tables, numbers and figure, from answers written to files as the runner writes them."""
    chosen = [t for t in tasks if t["id"] in ("generate-0", "generate-hard-0", "distinguish-0", "copy-1024-0", "explain-0")]
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        for model in ("haiku", "sonnet", "opus"):
            for condition in ("bare", "explicit", "schema", "plain"):
                with open(d / f"{model}.{condition}.jsonl", "w", encoding="utf-8") as f:
                    for t in chosen:
                        # Under bare, every answer in a fence; elsewhere as it should be.
                        text = answer(t)
                        if condition == "bare":
                            text = f"```\n{text}\n```"
                        line = {"id": t["id"], "rep": 0, "condition": condition, "response": text,
                                "served": [model], "output_tokens": 10, "cost_usd": 0.5}
                        f.write(json.dumps(line) + "\n")
        summary = summarize(load(d))
        assert summary["answers"] == 60 and summary["cost_usd"] == 30.0
        cell = summary["by_model_condition"]["opus/bare"]
        assert cell["strict_pct"] == 0 and cell["content_pct"] == 100 and cell["format_loss_pct"] == 100
        assert cell["compiled"] == 0 and cell["programs"] == 2
        fine = summary["by_model_condition"]["opus/plain"]
        assert (fine["strict_pct"], fine["compiled"], fine["cost_per_clean"]) == (100, 2, 0.5)
        assert summary["paired_vs_bare"]["all/plain"]["only_other"] == 15
        # A repetition one condition lacks counts for neither side of a task.
        rows = load(d)
        partial = [r for r in rows if not (r["model"] == "opus" and r["condition"] == "plain" and r["id"] == "generate-0")]
        level = summarize(partial)["task_level_vs_bare"]["opus/plain"]
        assert (level["better"], level["worse"], level["tied_or_never"]) == (4, 0, 0)
        out = d / "latex"
        write_latex(summary, out)
        numbers = (out / "numbers.tex").read_text()
        for line in ("\\newcommand{\\benchAnswers}{60}", "\\newcommand{\\benchOpusBareContent}{100.0}",
                     "\\newcommand{\\benchPlainStrict}{100.0}", "\\newcommand{\\benchBareDressCodeFence}{15}",
                     "\\newcommand{\\benchSonnetOpusStrictP}{1.00}", "\\newcommand{\\benchOpusCopyExact}{1}",
                     "\\newcommand{\\benchGenerateEasyLoss}{100.0}"):
            assert line in numbers, line
        assert len(set(re.findall(r"newcommand\{\\(\w+)\}", numbers))) == numbers.count("newcommand"), "a macro twice"
        svg, tikz = figure_svg(summary), figure_tikz(summary)
        assert svg.count("<title>") == 12 and svg.count("<circle") == 26
        assert tikz.count("circle (") == 26 and tikz.startswith("\\begin{tikzpicture}")


def check_runner(tasks):
    """The runner on a fake CLI: same sample per model, exact answers, resumable."""
    chosen = select(tasks, 2)
    assert len(chosen) == 12 and {t["kind"] for t in chosen} == {t["kind"] for t in tasks}
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        cli, log, out, fail = d / "cli", d / "log", d / "out.jsonl", d / "fail"
        cli.write_text(FAKE_CLI)
        cli.chmod(0o755)
        os.environ.update(FAKE_LOG=str(log), FAKE_FAIL=str(fail))
        fail.touch()
        assert run("m", chosen, out, cli=str(cli)) == len(chosen)
        assert not out.exists() or not out.read_text(), "a failure records no answer"
        fail.unlink()
        assert run("m", chosen, out, cli=str(cli)) == 0
        assert run("m", chosen, out, cli=str(cli), jobs=3) == 0
        assert len(log.read_text().splitlines()) == len(chosen), "a finished task is not sent again"
        lines = [json.loads(l) for l in open(out)]
        assert [l["id"] for l in lines] == [t["id"] for t in chosen]
        assert lines[0]["response"] == "\u2013\u2012\n", "answers are stored untouched"
        assert lines[0]["served"] == ["m"]
        # Repetitions add calls without touching finished ones.
        assert run("m", chosen, out, reps=2, cli=str(cli)) == 0
        assert len(log.read_text().splitlines()) == 2 * len(chosen)
        # A budget stops new calls, and the spent budget survives a thread pool.
        calls_before = len(log.read_text().splitlines())
        priced = d / "priced"
        priced.write_text(FAKE_CLI.replace('"total_cost_usd": 0', '"total_cost_usd": 1'))
        priced.chmod(0o755)
        assert run("m", chosen, d / "budget.jsonl", budget=2, cli=str(priced)) == 0
        assert len(log.read_text().splitlines()) - calls_before == 2
        # What each condition sends.
        bare = chosen[0]
        assert prompt_for(bare, "bare") == bare["prompt"] == prompt_for(bare, "schema")
        assert "strict decoder" in prompt_for(bare, "explicit")
        assert answer_of({"structured_output": {"answer": "x"}}, "schema") == "x"
        for kind in ("explain", "generate", "repair", "complete"):
            task = next(t for t in tasks if t["kind"] == kind)
            assert "newlines" not in prompt_for(task, "explicit"), f"{kind} needs its newlines"
        assert prompt_for(bare, "plain") == bare["prompt"]
        copy = next(t for t in tasks if t["kind"] == "copy")
        assert "spaces or newlines" in prompt_for(copy, "explicit")
        # The plain prompt keeps every fact of the document and loses its Markdown.
        document = (ROOT / "docs" / "isa.md").read_text(encoding="utf-8")
        assert system_prompt("bare") == system_prompt("explicit") == system_prompt("schema") == document
        plain = system_prompt("plain")
        assert plain == plain_text(document)
        assert not any(mark in plain for mark in ("`", "|", "**", "](", "\n#"))
        assert not plain.startswith("#")
        for fact in ("HYPHEN-MINUS", "U+2212", "PUSH n", "RET", "NOT", "at most 32 symbols", "\u2015-", "\u2013\u2014"):
            assert fact in plain, fact


def main():
    tasks = [json.loads(l) for l in open(HERE / "tasks.jsonl", encoding="ascii")]
    assert len(tasks) == 87
    assert sum("tier" not in t for t in tasks) == 50
    for task in tasks:
        if "input" in task:
            continue
        assert score(task, answer(task))["task"], task["id"]
        assert not score(task, "wrong")["task"], task["id"]
        assert not score(task, "")["task"], task["id"]

    task = next(t for t in tasks if t["kind"] == "generate")
    right = answer(task)
    # A lookalike outside the alphabet: not even lexically valid.
    level = score(task, right[:-1] + "﹘")
    assert (level["lexical"], level["task"]) == (False, False)
    # The input is hidden: a real cat passes, printing the expected bytes without reading fails.
    cat = next(t for t in tasks if t["id"] == "generate-compute-0")
    real = with_file("loop:\nREAD\nDUP\nPUSH 1\nADD\nJZ end\nWRITE\nJMP loop\nend:\nHALT\n", "asm").stdout.decode()
    assert score(cat, real)["task"]
    assert not score(cat, "\u2013\u2012")["task"]
    copy = next(t for t in tasks if t["kind"] == "copy")
    assert score(copy, copy["expected_text"])["task"]
    assert not score(copy, copy["expected_text"][:-1] + "x")["task"]
    assert score(copy, unwrap(copy, " ".join(copy["expected_text"])))["task"]
    # A fenced answer is not a program: nothing is cleaned up on the model's behalf.
    assert not score(task, f"```\n{right}\n```")["lexical"]
    # But the unwrapped score can tell a right program from its wrapping.
    for dressed in (f"```\n{right}\n```", f"`{right}`", f"**{right}**", " ".join(right)):
        assert score(task, unwrap(task, dressed))["task"], dressed
    # A line break is legal anywhere, an answer in short lines is as good as any.
    assert score(task, "\n".join(right.replace("\n", "")))["task"]
    # A trailing newline is valid source; a trailing space is not.
    assert score(task, right + "\n")["task"] and not score(task, right + " ")["task"]
    # A long line is no program, and the content score can still recognize it.
    hard = next(t for t in tasks if t["id"] == "generate-hard-0")
    one_line = answer(hard).replace("\n", "")
    assert not score(hard, one_line)["compiles"]
    assert score(hard, relayout(unwrap(hard, one_line)))["task"]
    # A started program is continued on a line of its own.
    started = next(t for t in tasks if t["id"] == "complete-hard-0")
    assert len(started["prefix"]) > 32 and score(started, answer(started))["task"]
    assert not score(started, answer(started).replace("\n", ""))["compiles"]
    listing = next(t for t in tasks if t["kind"] == "explain")
    assert unwrap(listing, answer(listing)) == answer(listing), "lines of a listing stay lines"
    # An odd length: lexically valid, syntactically not.
    level = score(task, right[:-1])
    assert (level["lexical"], level["compiles"]) == (True, False)
    # Valid and halting, but the wrong output.
    level = score(task, "–‒")
    assert (level["runs"], level["task"]) == (True, False)
    # Valid, but faults at runtime.
    level = score(task, "--")
    assert (level["compiles"], level["runs"]) == (True, False)
    check_runner(tasks)
    check_analysis(tasks)
    check_report(tasks)
    print(f"selftest ok: {len(tasks)} tasks")


if __name__ == "__main__":
    main()

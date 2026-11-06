#!/usr/bin/env python3
"""Turns results/v3 into the tables of the report: results/v3/summary.md and .json.

usage: analyze.py [DIR] [--latex OUT]

Every answer ends up in one of four classes:
  clean    correct as written: for a program, the compiler accepts these exact bytes
  wrapped  correct only after removing Markdown and spaces
  layout   correct only after also breaking its lines at the limit
  wrong    not correct either way

The figure of interest is the format loss: (wrapped + layout) / (clean + wrapped + layout),
the share of right answers that a strict consumer rejects. Standard library only, so
the numbers can be rebuilt anywhere.
"""

import difflib
import json
import math
import pathlib
import sys
from collections import Counter, defaultdict
from itertools import combinations

from common import LINE_MAX
from score import ALPHABET, PROGRAM_KINDS, relayout, score, unwrap

HERE = pathlib.Path(__file__).parent
MODELS = ("haiku", "sonnet", "opus", "gpt-6-luna", "gpt-6.1-sol")
CONDITIONS = ("bare", "explicit", "schema", "plain")
OTHERS = CONDITIONS[1:]
Z = 1.959964


def wilson(k, n):
    """95% Wilson interval, as percentages."""
    if n == 0:
        return (0.0, 0.0)
    p = k / n
    d = 1 + Z * Z / n
    c = p + Z * Z / (2 * n)
    h = Z * math.sqrt(p * (1 - p) / n + Z * Z / (4 * n * n))
    return (100 * max(0.0, (c - h) / d), 100 * min(1.0, (c + h) / d))


def exact_mcnemar(b, c):
    """Two-sided exact McNemar p value for b and c discordant pairs."""
    n = b + c
    if n == 0:
        return 1.0
    tail = sum(math.comb(n, i) for i in range(min(b, c) + 1)) / 2**n
    return min(1.0, 2 * tail)


def classify(task, response):
    if score(task, response)["task"]:
        return "clean"
    bare_answer = unwrap(task, response)
    if score(task, bare_answer)["task"]:
        return "wrapped"
    if task["kind"] in PROGRAM_KINDS and score(task, relayout(bare_answer))["task"]:
        return "layout"
    return "wrong"


def compiles(task, response):
    """Whether the compiler accepts this exact answer. None for a task that asks for no program."""
    return score(task, response).get("compiles")


def wrapper(task, response):
    """How the answer is dressed, whether or not it is right."""
    text = response.strip()
    if "```" in text:
        return "code fence"
    if "**" in text:
        return "bold"
    if text.startswith("`"):
        return "backticks"
    if task["kind"] == "copy":
        if any(c.isspace() for c in text):
            return "spacing"
        if set(text) - set(ALPHABET):
            return "other text"
    elif task["kind"] in PROGRAM_KINDS:
        if any(c.isspace() and c != "\n" for c in text):
            return "spacing"
        if set(text) - set(ALPHABET) - {"\n"}:
            return "other text"
        if any(len(line) > LINE_MAX for line in text.split("\n")):
            return "long line"
    elif task["kind"] == "distinguish" and not text.isdigit():
        return "other text"
    elif task["kind"] == "explain" and text.splitlines() != [l.strip() for l in text.splitlines()]:
        return "spacing"
    return "none"


def substitutions(expected, got):
    """Code points replaced one for one, and the normalized edit size."""
    swaps = Counter()
    changed = 0
    matcher = difflib.SequenceMatcher(None, expected, got, autojunk=False)
    for tag, a0, a1, b0, b1 in matcher.get_opcodes():
        if tag == "equal":
            continue
        changed += max(a1 - a0, b1 - b0)
        if tag == "replace" and a1 - a0 == b1 - b0:
            swaps.update(zip(expected[a0:a1], got[b0:b1]))
    return swaps, changed / max(1, len(expected))


def load(directory):
    tasks = {}
    for line in (HERE / "tasks.jsonl").read_text(encoding="ascii").splitlines():
        task = json.loads(line)
        tasks[task["id"]] = task
    rows = []
    for model in MODELS:
        for condition in CONDITIONS:
            path = directory / f"{model}.{condition}.jsonl"
            if not path.exists():
                continue
            for line in path.read_text(encoding="utf-8").splitlines():
                item = json.loads(line)
                task = tasks[item["id"]]
                rows.append({
                    "model": model,
                    "condition": condition,
                    "id": item["id"],
                    "rep": item.get("rep", 0),
                    "kind": task["kind"],
                    "tier": task.get("tier", "easy"),
                    "class": classify(task, item["response"]),
                    "compiles": compiles(task, item["response"]),
                    "wrapper": wrapper(task, item["response"]),
                    "served": item.get("served", []),
                    "tokens": item.get("output_tokens") or 0,
                    "cost": item.get("cost_usd"),
                    "task": task,
                    "response": item["response"],
                })
    return rows


def counts(rows):
    c = Counter(r["class"] for r in rows)
    n = len(rows)
    unwrapped = c["clean"] + c["wrapped"]
    content = unwrapped + c["layout"]
    lost = c["wrapped"] + c["layout"]
    programs = [r for r in rows if r["compiles"] is not None]
    cost = sum(r["cost"] for r in rows) if all(r["cost"] is not None for r in rows) else None
    compiled = sum(r["compiles"] for r in programs)
    return {
        "n": n,
        "clean": c["clean"],
        "wrapped": c["wrapped"],
        "layout": c["layout"],
        "wrong": c["wrong"],
        "programs": len(programs),
        "compiled": compiled,
        "compiles_pct": 100 * compiled / len(programs) if programs else 0.0,
        "compiles_ci": wilson(compiled, len(programs)),
        "strict_pct": 100 * c["clean"] / n if n else 0.0,
        "strict_ci": wilson(c["clean"], n),
        "unwrapped_pct": 100 * unwrapped / n if n else 0.0,
        "unwrapped_ci": wilson(unwrapped, n),
        "content_pct": 100 * content / n if n else 0.0,
        "content_ci": wilson(content, n),
        "format_loss_pct": 100 * lost / content if content else 0.0,
        "format_loss_ci": wilson(lost, content),
        "cost_usd": cost,
        "cost_per_answer": cost / n if n and cost is not None else None,
        # What it takes to get one answer a program can use as it stands.
        "cost_per_clean": cost / c["clean"] if c["clean"] and cost is not None else None,
        "tokens": sum(r["tokens"] for r in rows),
    }


def fmt(pct, ci):
    return f"{pct:.1f} [{ci[0]:.1f}, {ci[1]:.1f}]"


def summarize(rows):
    out = {"answers": len(rows), "cost_usd": counts(rows)["cost_usd"]}
    out["served"] = sorted({s for r in rows for s in r["served"]})
    out["by_model_condition"] = {}
    for model in MODELS:
        for condition in CONDITIONS:
            selected = [r for r in rows if r["model"] == model and r["condition"] == condition]
            if selected:
                out["by_model_condition"][f"{model}/{condition}"] = counts(selected)
    out["by_condition"] = {c: counts([r for r in rows if r["condition"] == c]) for c in CONDITIONS}
    present = [m for m in MODELS if any(r["model"] == m for r in rows)]
    out["by_model"] = {m: counts([r for r in rows if r["model"] == m]) for m in present}
    out["by_kind_bare"] = {}
    for kind in sorted({r["kind"] for r in rows}):
        for tier in ("easy", "hard"):
            selected = [r for r in rows if r["kind"] == kind and r["tier"] == tier and r["condition"] == "bare"]
            if selected:
                out["by_kind_bare"][f"{kind}/{tier}"] = counts(selected)
    out["wrappers"] = {
        c: dict(Counter(r["wrapper"] for r in rows if r["condition"] == c).most_common()) for c in CONDITIONS
    }
    out["wrappers_by_model_bare"] = {
        m: dict(Counter(r["wrapper"] for r in rows if r["condition"] == "bare" and r["model"] == m).most_common())
        for m in present
    }
    # Paired on the same task, repetition and model: does a condition change strict success?
    keyed = {(r["model"], r["id"], r["rep"], r["condition"]): r["class"] == "clean" for r in rows}
    out["paired_vs_bare"] = {}
    for model in (*present, "all"):
        for condition in OTHERS:
            only_bare = only_other = 0
            for (m, task, rep, c), passed in keyed.items():
                if c != "bare" or (model != "all" and m != model):
                    continue
                other = keyed.get((m, task, rep, condition))
                if other is None:
                    continue
                only_bare += passed and not other
                only_other += other and not passed
            out["paired_vs_bare"][f"{model}/{condition}"] = {
                "only_bare": only_bare, "only_other": only_other, "p": exact_mcnemar(only_bare, only_other),
            }
    # Repetitions of a task are not independent, so the pairs above overstate the evidence.
    # This counts each task once: did it pass more often under the other condition?
    out["task_level_vs_bare"] = {}
    for model in (*present, "all"):
        for condition in OTHERS:
            # Only repetitions both conditions have: a missing answer is not a failed one.
            per_task = defaultdict(lambda: [0, 0])
            for (m, task, rep, c), passed in keyed.items():
                if c != "bare" or (model != "all" and m != model):
                    continue
                other = keyed.get((m, task, rep, condition))
                if other is not None:
                    per_task[task][0] += passed
                    per_task[task][1] += other
            better = sum(o > b for b, o in per_task.values())
            worse = sum(b > o for b, o in per_task.values())
            out["task_level_vs_bare"][f"{model}/{condition}"] = {
                "better": better, "worse": worse, "tied_or_never": len(per_task) - better - worse,
                "p": exact_mcnemar(better, worse),
            }
    # Does formatting change which model looks better? Same task and repetition, condition bare.
    out["model_gaps_bare"] = {}
    classes = {(r["model"], r["id"], r["rep"]): r["class"] for r in rows if r["condition"] == "bare"}
    pairs = [("sonnet", "opus"), ("haiku", "sonnet"), ("haiku", "opus")]
    pairs += [(a, b) for a, b in combinations(present, 2) if a.startswith("gpt-") or b.startswith("gpt-")]
    for a, b in pairs:
        if a not in present or b not in present:
            continue
        strict = [0, 0]
        relaxed = [0, 0]
        for (m, task, rep), cls in classes.items():
            other = classes.get((b, task, rep))
            if m != a or other is None:
                continue
            strict[0] += cls == "clean" and other != "clean"
            strict[1] += other == "clean" and cls != "clean"
            relaxed[0] += cls != "wrong" and other == "wrong"
            relaxed[1] += other != "wrong" and cls == "wrong"
        out["model_gaps_bare"][f"{a} vs {b}"] = {
            "strict": strict, "strict_p": exact_mcnemar(*strict),
            "content": relaxed, "content_p": exact_mcnemar(*relaxed),
        }
    out["served_counts"] = dict(Counter(",".join(r["served"]) for r in rows).most_common())
    # Copying has no meaning to lean on: only code points.
    swaps = Counter()
    copy = defaultdict(list)
    for r in rows:
        if r["kind"] != "copy" or r["condition"] != "schema":
            continue
        answer = unwrap(r["task"], r["response"])
        s, distance = substitutions(r["task"]["expected_text"], answer)
        swaps.update(s)
        copy[(r["model"], len(r["task"]["expected_text"]))].append(distance)
    out["copy_distance"] = {
        f"{m}/{n}": sum(v) / len(v) for (m, n), v in sorted(copy.items())
    }
    out["copy_exact"] = {}
    for r in rows:
        if r["kind"] == "copy" and r["condition"] == "schema":
            key = f"{r['model']}/{len(r['task']['expected_text'])}"
            hit = unwrap(r["task"], r["response"]) == r["task"]["expected_text"]
            k, n = out["copy_exact"].get(key, (0, 0))
            out["copy_exact"][key] = (k + hit, n + 1)
    out["substitutions"] = {f"U+{ord(a):04X}>U+{ord(b):04X}": n for (a, b), n in swaps.most_common(12)}
    return out


def money(value, digits=2):
    return "--" if value is None else f"{value:.{digits}f}"


def markdown(s):
    lines = [f"{s['answers']} answers. Reported cost: {money(s['cost_usd'])} USD. Served: {', '.join(s['served']) or 'not exposed by CLI'}.", ""]
    lines += ["## By model and condition", "",
              "Percentages with 95% Wilson intervals. Compiles: program tasks whose exact answer the compiler accepts. Strict: correct as written. Content: correct once Markdown and line layout are undone. Format loss: right answers rejected only for their clothes.", "",
              "| Model / condition | n | Compiles % | Strict % | Unwrapped % | Content % | Format loss % |", "| --- | --- | --- | --- | --- | --- | --- |"]
    for key, c in s["by_model_condition"].items():
        lines.append(f"| {key} | {c['n']} | {fmt(c['compiles_pct'], c['compiles_ci'])} | {fmt(c['strict_pct'], c['strict_ci'])} | {fmt(c['unwrapped_pct'], c['unwrapped_ci'])} | {fmt(c['content_pct'], c['content_ci'])} | {fmt(c['format_loss_pct'], c['format_loss_ci'])} |")
    lines += ["", "## By task, condition bare", "", "| Kind / tier | n | Compiles % | Strict % | Unwrapped % | Content % | Format loss % |", "| --- | --- | --- | --- | --- | --- | --- |"]
    for key, c in s["by_kind_bare"].items():
        compiled = f"{c['compiles_pct']:.1f}" if c["programs"] else "-"
        lines.append(f"| {key} | {c['n']} | {compiled} | {c['strict_pct']:.1f} | {c['unwrapped_pct']:.1f} | {c['content_pct']:.1f} | {c['format_loss_pct']:.1f} |")
    lines += ["", "## Cost", "", "US dollars at the prices the client reports. Per clean: cost of one answer usable as it stands.", "",
              "| Model / condition | Answers | Output tokens | Cost | Per answer | Per clean |", "| --- | --- | --- | --- | --- | --- |"]
    for key, c in [*s["by_model_condition"].items(), *s["by_model"].items()]:
        per_clean = f"{c['cost_per_clean']:.4f}" if c["cost_per_clean"] is not None else "-"
        lines.append(f"| {key} | {c['n']} | {c['tokens']} | {money(c['cost_usd'])} | {money(c['cost_per_answer'], 4)} | {per_clean} |")
    lines += ["", "## How answers were dressed, by condition", ""]
    for condition, w in s["wrappers"].items():
        lines.append(f"- {condition}: " + ", ".join(f"{k} {v}" for k, v in w.items()))
    lines += ["", "## Strict success against bare, paired (exact McNemar)", "", "| Model / condition | Only bare | Only other | p |", "| --- | --- | --- | --- |"]
    for key, p in s["paired_vs_bare"].items():
        lines.append(f"| {key} | {p['only_bare']} | {p['only_other']} | {p['p']:.2g} |")
    lines += ["", "## Task level against bare: each task counted once (sign test)", "", "| Model / condition | Better | Worse | Same | p |", "| --- | --- | --- | --- | --- |"]
    for key, p in s["task_level_vs_bare"].items():
        lines.append(f"| {key} | {p['better']} | {p['worse']} | {p['tied_or_never']} | {p['p']:.2g} |")
    lines += ["", "## Pairs of models, condition bare", "", "Wins of each side on the same task and repetition.", "", "| Pair | Strict | p | Content | p |", "| --- | --- | --- | --- | --- |"]
    for key, g in s["model_gaps_bare"].items():
        lines.append(f"| {key} | {g['strict'][0]} to {g['strict'][1]} | {g['strict_p']:.2g} | {g['content'][0]} to {g['content'][1]} | {g['content_p']:.2g} |")
    lines += ["", "Served models per call: " + ", ".join(f"{k} ({v})" for k, v in s["served_counts"].items()) + "."]
    lines += ["", "## Copying, condition schema", "", "| Model / length | Exact | Mean edit size |", "| --- | --- | --- |"]
    for key, d in s["copy_distance"].items():
        k, n = s["copy_exact"][key]
        lines.append(f"| {key} | {k}/{n} | {d:.3f} |")
    lines += ["", "Most frequent substitutions: " + (", ".join(f"{k} ({v})" for k, v in s["substitutions"].items()) or "none") + "."]
    return "\n".join(lines) + "\n"


NAMES = {"haiku": "Haiku", "sonnet": "Sonnet", "opus": "Opus", "gpt-6-luna": "Luna", "gpt-6.1-sol": "Sol"}


def camel(text):
    for model in ("gpt-6-luna", "gpt-6.1-sol"):
        text = text.replace(model, NAMES[model])
    return "".join(word.capitalize() for word in text.replace("/", " ").split())


def percent_ci(pct, ci):
    return f"{pct:.1f} ({ci[0]:.1f}--{ci[1]:.1f})"


def p_value(p):
    """Readable in a sentence and in a table: nobody needs 9.1e-06 to four figures."""
    return f"{p:.2f}" if p >= 0.01 else "<0.001" if p < 0.001 else f"{p:.3f}"


def figure_rows(s):
    """(model, condition, strict %, content %) for each row of the figure."""
    rows = []
    for model in MODELS:
        for condition in CONDITIONS:
            c = s["by_model_condition"].get(f"{model}/{condition}")
            if c:
                rows.append((model, condition, c["strict_pct"], c["content_pct"]))
    return rows


def figure_shapes(s):
    """The figure as marks, in points with y going down, for both the SVG and the PDF.
    One row per model and condition: a filled dot as written, a hollow one once the
    clothes are off. The length of the line between them is what formatting cost."""
    left, right, row, gap, top = 92, 320, 14, 9, 30
    x = lambda pct: left + (right - left) * pct / 100
    rows = figure_rows(s)
    groups = len({m for m, *_ in rows})
    bottom = top + row * len(rows) + gap * (groups - 1)
    marks = [("dot", left, 8, True, None), ("text", left + 7, 8, "strict score", "start"),
             ("dot", left + 72, 8, False, None), ("text", left + 79, 8, "content score", "start")]
    for tick in (0, 25, 50, 75, 100):
        marks.append(("grid", x(tick), top - 4, x(tick), bottom))
        marks.append(("text", x(tick), bottom + 9, f"{tick}%", "middle"))
    y, last = top + row / 2, None
    for model, condition, strict, content in rows:
        if last and model != last:
            y += gap
        if model != last:
            marks.append(("label", 0, y, NAMES[model], "start"))
        marks.append(("text", left - 6, y, condition, "end"))
        marks.append(("line", x(strict), y, x(content), y))
        marks.append(("dot", x(content), y, False, f"{NAMES[model]}, {condition}: {strict:.1f}% strict, {content:.1f}% content"))
        marks.append(("dot", x(strict), y, True, None))
        y += row
        last = model
    return marks, right + 18, bottom + 14


def figure_svg(s):
    marks, width, height = figure_shapes(s)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" class="paper-figure" role="img" '
           'aria-label="Share of correct answers by model and condition, strict and content scores. The same numbers are in the table above." '
           'font-size="9" font-family="inherit" fill="currentColor">']
    for mark in marks:
        kind = mark[0]
        if kind == "grid":
            out.append(f'<line x1="{mark[1]:.1f}" y1="{mark[2]}" x2="{mark[3]:.1f}" y2="{mark[4]}" stroke="currentColor" stroke-opacity=".2"/>')
        elif kind == "line":
            out.append(f'<line x1="{mark[1]:.1f}" y1="{mark[2]}" x2="{mark[3]:.1f}" y2="{mark[4]}" stroke="currentColor" stroke-width="2"/>')
        elif kind == "dot":
            title = f"<title>{mark[4]}</title>" if mark[4] else ""
            fill = "currentColor" if mark[3] else "var(--bg, #fff)"
            out.append(f'<circle cx="{mark[1]:.1f}" cy="{mark[2]}" r="3.5" fill="{fill}" stroke="currentColor" stroke-width="1.5">{title}</circle>')
        else:
            weight = ' font-weight="600"' if kind == "label" else ""
            out.append(f'<text x="{mark[1]:.1f}" y="{mark[2] + 3}" text-anchor="{mark[4]}"{weight}>{mark[3]}</text>')
    return "".join(out) + "</svg>\n"


def figure_tikz(s):
    marks, width, height = figure_shapes(s)
    anchors = {"start": "west", "end": "east", "middle": "center"}
    out = ["\\begin{tikzpicture}[x=0.68pt,y=-0.68pt,font=\\scriptsize]"]
    for mark in marks:
        kind = mark[0]
        if kind == "grid":
            out.append(f"\\draw[black!20] ({mark[1]:.1f},{mark[2]}) -- ({mark[3]:.1f},{mark[4]});")
        elif kind == "line":
            out.append(f"\\draw[line width=1.2pt] ({mark[1]:.1f},{mark[2]}) -- ({mark[3]:.1f},{mark[4]});")
        elif kind == "dot":
            fill = "black" if mark[3] else "white"
            out.append(f"\\filldraw[fill={fill},draw=black,line width=0.8pt] ({mark[1]:.1f},{mark[2]}) circle (2.2pt);")
        else:
            text = f"\\textbf{{{mark[3]}}}" if kind == "label" else mark[3].replace("%", "\\%")
            out.append(f"\\node[anchor={anchors[mark[4]]},inner sep=0pt] at ({mark[1]:.1f},{mark[2]}) {{{text}}};")
    return "\n".join(out + ["\\end{tikzpicture}"]) + "\n"


def write_latex(s, out):
    """The experiment report's tables, numbers and figure."""
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for model in MODELS:
        for i, condition in enumerate(CONDITIONS):
            c = s["by_model_condition"].get(f"{model}/{condition}")
            if not c:
                continue
            per_clean = f"{c['cost_per_clean']:.3f}" if c["cost_per_clean"] is not None else "--"
            rows.append(f"{NAMES[model] if i == 0 else ''} & {condition} & {c['compiles_pct']:.1f} & "
                        f"{percent_ci(c['strict_pct'], c['strict_ci'])} & {percent_ci(c['content_pct'], c['content_ci'])} & "
                        f"{c['format_loss_pct']:.1f} & {money(c['cost_usd'])} & {per_clean} \\\\")
        rows.append("\\addlinespace")
    (out / "by-model.tex").write_text("\n".join(rows[:-1]) + "\n")
    rows = []
    for key, c in s["by_kind_bare"].items():
        kind, tier = key.split("/")
        compiled = f"{c['compiles_pct']:.1f}" if c["programs"] else "--"
        rows.append(f"{kind} & {tier} & {c['n']} & {compiled} & {c['strict_pct']:.1f} & {c['content_pct']:.1f} & {c['format_loss_pct']:.1f} \\\\")
    (out / "by-kind.tex").write_text("\n".join(rows) + "\n")
    rows = []
    for key, p in s["task_level_vs_bare"].items():
        model, condition = key.split("/")
        q = s["paired_vs_bare"][key]
        rows.append(f"{NAMES.get(model, 'All')} & {condition} & {q['only_other']} / {q['only_bare']} & {p_value(q['p'])} & {p['better']} / {p['worse']} & {p_value(p['p'])} \\\\")
    (out / "paired.tex").write_text("\n".join(rows) + "\n")
    rows = []
    for key, g in s["model_gaps_bare"].items():
        a, b = key.split(" vs ")
        rows.append(f"{NAMES[a]} vs {NAMES[b]} & {g['strict'][0]} / {g['strict'][1]} & {p_value(g['strict_p'])} & {g['content'][0]} / {g['content'][1]} & {p_value(g['content_p'])} \\\\")
    (out / "model-gaps.tex").write_text("\n".join(rows) + "\n")
    (out / "figure.tex").write_text(figure_tikz(s))
    (out / "figure.svg").write_text(figure_svg(s))

    numbers = {"benchAnswers": s["answers"], "benchCost": money(s['cost_usd'])}
    metrics = {"Compiles": "compiles_pct", "Strict": "strict_pct", "Unwrapped": "unwrapped_pct", "Content": "content_pct", "Loss": "format_loss_pct"}
    def put(prefix, c):
        for name, field in metrics.items():
            numbers[f"bench{prefix}{name}"] = f"{c[field]:.1f}"
        numbers[f"bench{prefix}Cost"] = f"{money(c['cost_usd'])}"
        numbers[f"bench{prefix}N"] = c["n"]
        numbers[f"bench{prefix}PerAnswer"] = f"{money(c['cost_per_answer'], 4)}"
        if c["cost_per_clean"] is not None:
            numbers[f"bench{prefix}CostPerClean"] = f"{c['cost_per_clean']:.3f}"
    for condition, c in s["by_condition"].items():
        put(camel(condition), c)
    for model, c in s["by_model"].items():
        put(camel(model), c)
    for key, c in s["by_model_condition"].items():
        put(camel(key), c)
    for key, c in s["by_kind_bare"].items():
        put(camel(key), c)
    for condition, wrappers in s["wrappers"].items():
        for kind, count in wrappers.items():
            numbers[f"bench{camel(condition)}Dress{camel(kind)}"] = count
    for key, g in s["model_gaps_bare"].items():
        pair = camel(key.replace(" vs ", " "))
        numbers[f"bench{pair}StrictFirst"], numbers[f"bench{pair}StrictSecond"] = g["strict"]
        numbers[f"bench{pair}StrictP"] = p_value(g["strict_p"])
        numbers[f"bench{pair}ContentFirst"], numbers[f"bench{pair}ContentSecond"] = g["content"]
        numbers[f"bench{pair}ContentP"] = p_value(g["content_p"])
    for key, (k, n) in s["copy_exact"].items():
        model, length = key.split("/")
        if length == "1024":
            numbers[f"bench{camel(model)}CopyExact"], numbers[f"bench{camel(model)}CopyTotal"] = k, n
    numbers["benchSwaps"] = sum(s["substitutions"].values())
    (out / "numbers.tex").write_text("".join(f"\\newcommand{{\\{k}}}{{{v}}}\n" for k, v in numbers.items()))


def main():
    arguments = sys.argv[1:]
    latex = None
    baseline = None
    if "--baseline" in arguments:
        at = arguments.index("--baseline")
        baseline = pathlib.Path(arguments[at + 1])
        del arguments[at : at + 2]
    if "--latex" in arguments:
        at = arguments.index("--latex")
        latex = pathlib.Path(arguments[at + 1])
        del arguments[at : at + 2]
    directory = pathlib.Path(arguments[0]) if arguments else HERE / "results" / "v3"
    rows = load(directory)
    if baseline is not None:
        rows = load(baseline) + rows
    if not rows:
        raise SystemExit("No answers found")
    if latex is None:
        original = HERE / "results" / "v3"
        latex = HERE / "report" / "generated" if directory.resolve() == original.resolve() else directory / "tables"
    summary = summarize(rows)
    (directory / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    (directory / "summary.md").write_text(markdown(summary))
    write_latex(summary, latex)
    print(markdown(summary))


if __name__ == "__main__":
    main()

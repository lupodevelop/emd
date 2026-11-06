# Can a language model write code that compiles?

Ask a model for "the source only" and let a program read the reply. How often does a right answer fail because of its formatting? What fixes that, and what does it cost?

emd is a good place to measure this. Its compiler takes eight dashes and newlines, at most 32 on a line, and nothing else. Scoring exact replies and normalized replies separately exposes the difference between task correctness and usable source.

Here is a real answer. Haiku was asked for a program that writes `A`, "source only":

````
```
-‑‐-‑‑-‑‑‑‐-‑‑-‐‑-—‐–‒
```
````

The program is right. The compiler stops at the first backtick. Asked for a number, the same model answered `**21**`.

## What we found

Haiku and Sonnet, 1150 answers on 49 tasks, US$13.52 in client-reported token cost:

| Model  | Prompt   | Compiles % | Correct as written % | Correct once cleaned % | Right answers lost % | US$ per usable answer |
| ------ | -------- | ---------- | -------------------- | -------------------------- | -------------------- | --------------------- |
| Haiku  | bare     | 29.2       | 47.6                 | 71.4                       | 33.3                 | 0.006                 |
| Haiku  | explicit | 71.8       | 74.7                 | 74.7                       | 0.0                  | 0.004                 |
| Haiku  | schema   | 67.6       | 73.3                 | 74.0                       | 0.9                  | 0.004                 |
| Haiku  | plain    | 33.8       | 52.1                 | 69.2                       | 24.8                 | 0.006                 |
| Sonnet | bare     | 76.4       | 81.6                 | 87.1                       | 6.2                  | 0.023                 |
| Sonnet | explicit | 80.6       | 88.4                 | 90.5                       | 2.3                  | 0.023                 |
| Sonnet | schema   | 80.6       | 87.1                 | 92.5                       | 5.9                  | 0.029                 |
| Sonnet | plain    | 75.4       | 82.3                 | 85.5                       | 3.8                  | 0.022                 |

- **One sentence fixes most of it.** Telling Haiku that a decoder reads the reply takes its compiling programs from 29% to 72%, and it pays for itself: fewer generated answers are discarded, so a usable one gets cheaper.
- **Markdown in the system prompt doesn't look like the cause.** Taking it out changes nothing we can detect. The fences stay.
- **A JSON field stops the fences, not every mistake.** Sonnet under `schema` still lost 5% of its answers to lines past the limit, a rule its prompt states.
- **Formatting exaggerates the gap between models.** Sonnet beats Haiku 55 to 5 on tasks scored as written, and 30 to 7 once answers are cleaned.
- **Exact copying is often successful.** Both models copy 1024 random dashes almost perfectly in the sampled structured-output tasks. Program-construction tasks score lower, though this does not isolate the cause of their errors.

If a program reads the reply, say so, or use a structured channel, and validate anyway. If you run a benchmark, report content and formatting separately.

## How to read the table

- **The prompts.** `bare`: the task as written, which already says "Answer with the source only". `explicit`: adds that the whole reply goes to a strict decoder, so no Markdown. `schema`: the answer travels in a JSON field. `plain`: like `bare`, with no Markdown in the system prompt.
- **Compiles.** Of the program tasks, how many exact answers the compiler accepts, right or not.
- **Correct as written.** The answer works exactly as it arrived.
- **Correct once cleaned.** It works after removing code fences, backticks, bold and spaces, and breaking long lines.
- **Right answers lost.** How many right answers failed only because of formatting.
- **US$ per usable answer.** What the row cost, divided by the answers correct as written, at the prices the client reports.

## The tasks

Six kinds: `generate` a program, `complete` one from its start, `repair` the one wrong character, `explain` by listing the instructions, `distinguish` two strings by where they differ, and `copy` up to 1024 random dashes. There are 87 tasks. A run uses 49 of them, three times each. Some programs read input the model never sees, so printing the expected bytes can't pass.

## The limits

- There are no Opus results. The last repetition of Sonnet under `plain` is incomplete (124 of 147), and three Haiku calls failed and were not sent again.
- The table above covers two models from one provider through a CLI that adds a preamble we cannot inspect. The OpenAI CLI sample below uses a separate protocol; client and provider effects cannot be separated.
- An earlier run measured 17.2% lost for Sonnet under `bare`, against 6.2% here, on an older version of the language and a different scorer. We don't know why, so don't read these sizes as constants. It's in [`results/earlier`](results/earlier), and `results/v3` holds the prompts, every raw answer and the full report.

## Run it

Requires a built `emd` binary and the corresponding CLI. Calls consume provider usage; Codex uses its existing ChatGPT login. Reported token costs are distinct from subscription charges.

```
cargo build -p emd-cli
python3 selftest.py                  # checks the scorer, free
./experiment.sh 3 6                  # every model under every condition; resumes if stopped
python3 analyze.py                   # experiment tables, numbers and figure
python3 score.py --answered FILE     # any file with {"id": ..., "response": ...} per line, from any provider
```

### Codex

```sh
./experiment.sh --codex 3
```

Runs GPT-6 Luna and GPT-6.1 Sol with medium reasoning, the same 49 tasks and the saved v3 system prompts. Each call is isolated, with tools, skills and memory disabled. Results and the comparison with v3 are written under `results/codex-v1`; outputs stay in the benchmark directory. Codex reports token usage but no dollar cost, so raw `cost_usd` fields remain null. The summary estimates API-equivalent token costs separately, using the rates recorded in `protocol.json`.

The [separate experiment report](report/experiment.pdf) covers the CLI study independently of the language and verification paper.

## OpenAI CLI sample

The collection stopped at 573 completed answers. Sol has complete `bare` and `explicit` cells (147 answers each); Luna and Sol `schema` are partial, and `plain` was not collected. Percentages and denominators are in [`results/codex-v1/summary.md`](results/codex-v1/summary.md). Raw replies, recorded tokens and rate assumptions are retained alongside the report.

The completed-call API-equivalent estimate is US$5.95 at the published rates recorded in `protocol.json`. This is not an allocated subscription charge and excludes unreported usage of timed-out or cancelled calls.

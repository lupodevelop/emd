#!/usr/bin/env python3
"""Writes tasks.jsonl: the Emotional Damage Evaluation Suite. Deterministic.

JSON escapes every dash as \\uXXXX, so no editor or terminal in the path can
change a code point of a task.
"""

import json
import pathlib
import random

from common import ROOT, with_file, wrapped

HERE = pathlib.Path(__file__).parent
ALPHABET = "-‐‑‒–—―−"
TEXTS = ["A", "ok", "hi", "emd", "42", "no", "dash", "AI", "yes", "x\n"]


def flat(source):
    """A program without its line breaks, so that positions in it count instructions."""
    return source.replace("\n", "")


def compile_print(text):
    source = 'PRINT "%s"\nHALT\n' % text.replace("\n", "\\n")
    return flat(with_file(source, "asm").stdout.decode("utf-8"))


def assemble(listing):
    return flat(with_file(listing, "asm").stdout.decode("utf-8"))


def hard_tasks(rng):
    """Longer sources, programs that must really compute, and pure copying."""
    tasks = []
    long_texts = ["Hello, world!\n", "dashes are code", "0123456789", "emotional damage"]
    for i, text in enumerate(long_texts):
        tasks.append({
            "id": f"generate-hard-{i}", "kind": "generate", "tier": "hard", "expected_output": text,
            "prompt": f"Write an emd program that writes exactly the bytes of {text!r} to "
                      "stdout and halts. Answer with the source only.",
        })
    # The input stays hidden from the model, so printing the expected bytes cannot pass.
    computed = [
        ("copies every byte of its input to stdout, then halts at end of input", "emd\n", "emd\n"),
        ("writes its input reversed, then halts. The input is at most 8 bytes", "dash", "hsad"),
        ("reads two ASCII digits and writes their sum as one ASCII digit. The sum is below 10", "34", "7"),
    ]
    for i, (what, stdin, expected) in enumerate(computed):
        tasks.append({
            "id": f"generate-compute-{i}", "kind": "generate", "tier": "hard",
            "input": stdin, "expected_output": expected,
            "prompt": f"Write an emd program that {what}. Answer with the source only.",
        })
    for i, text in enumerate(long_texts):
        source = compile_print(text)
        cut = 2 * rng.randrange(len(source) // 8, len(source) // 4)
        tasks.append({
            "id": f"complete-hard-{i}", "kind": "complete", "tier": "hard",
            "expected_output": text, "prefix": source[:cut],
            "prompt": "This is the start of an emd program that should write exactly the bytes "
                      f"of {text!r} to stdout and halt:\n{wrapped(source[:cut])}\n"
                      "Answer with only the code points that complete it.",
        })
    for i, text in enumerate(long_texts):
        source = compile_print(text)
        while True:
            at = rng.randrange(len(source))
            wrong = rng.choice([c for c in ALPHABET if c != source[at]])
            broken = source[:at] + wrong + source[at + 1:]
            result = with_file(wrapped(broken), "run", "--max-steps", "1000000")
            if result.stdout != text.encode():
                break
        tasks.append({
            "id": f"repair-hard-{i}", "kind": "repair", "tier": "hard", "expected_output": text,
            "prompt": f"This emd program should write exactly the bytes of {text!r} and halt, "
                      f"but one code point is wrong:\n{wrapped(broken)}\n"
                      "Answer with the corrected source only.",
        })
    instrs = ["PUSH 1", "PUSH 2", "PUSH 7", "DUP", "DROP", "SWAP", "OVER", "ROT", "ADD", "SUB", "MUL",
              "LOAD", "STORE", "EQ", "LT", "GT", "NOT", "READ", "WRITE", "JMP", "JZ", "JNZ", "CALL", "RET"]
    for i in range(5):
        listing = [rng.choice(instrs) for _ in range(40)] + ["HALT"]
        source = assemble("\n".join(listing))
        tasks.append({
            "id": f"explain-hard-{i}", "kind": "explain", "tier": "hard", "expected_listing": listing,
            "prompt": f"List the instructions of this emd program:\n{wrapped(source)}\n"
                      "Answer with one mnemonic per line, such as PUSH 3 or ADD, and nothing else.",
        })
    for i in range(5):
        source = compile_print(long_texts[i % len(long_texts)])
        at = rng.randrange(len(source))
        wrong = rng.choice([c for c in ALPHABET if c != source[at]])
        other = source[:at] + wrong + source[at + 1:]
        tasks.append({
            "id": f"distinguish-hard-{i}", "kind": "distinguish", "tier": "hard", "expected_index": at,
            "prompt": "These two strings differ in exactly one code point:\n"
                      f"{source}\n{other}\n"
                      "Answer with its 0-based index only.",
        })
    # No meaning to lean on: this measures code points alone.
    for length in (16, 64, 256, 1024):
        for i in range(3):
            text = "".join(rng.choice(ALPHABET) for _ in range(length))
            tasks.append({
                "id": f"copy-{length}-{i}", "kind": "copy", "tier": "hard" if length > 64 else "easy",
                "expected_text": text,
                "prompt": f"Reproduce this string exactly:\n{text}\nAnswer with the string only.",
            })
    return tasks


def main():
    rng = random.Random(20261103)
    tasks = []

    for i, text in enumerate(TEXTS):
        tasks.append({
            "id": f"generate-{i}", "kind": "generate", "expected_output": text,
            "prompt": f"Write an emd program that writes exactly the bytes of {text!r} to "
                      "stdout and halts. Answer with the source only.",
        })

    for i, text in enumerate(TEXTS):
        source = compile_print(text)
        cut = 2 * rng.randrange(1, len(source) // 2)
        tasks.append({
            "id": f"complete-{i}", "kind": "complete", "expected_output": text, "prefix": source[:cut],
            "prompt": "This is the start of an emd program that should write exactly the bytes "
                      f"of {text!r} to stdout and halt:\n{wrapped(source[:cut])}\n"
                      "Answer with only the code points that complete it.",
        })

    for i, text in enumerate(TEXTS):
        source = compile_print(text)
        while True:
            at = rng.randrange(len(source))
            wrong = rng.choice([c for c in ALPHABET if c != source[at]])
            broken = source[:at] + wrong + source[at + 1:]
            result = with_file(wrapped(broken), "run", "--max-steps", "1000000")
            if result.stdout != text.encode():
                break
        tasks.append({
            "id": f"repair-{i}", "kind": "repair", "expected_output": text,
            "prompt": f"This emd program should write exactly the bytes of {text!r} and halt, "
                      f"but one code point is wrong:\n{wrapped(broken)}\n"
                      "Answer with the corrected source only.",
        })

    instrs = ["PUSH 1", "PUSH 2", "PUSH 7", "DUP", "DROP", "SWAP", "OVER", "ADD", "SUB",
              "MUL", "LOAD", "STORE", "EQ", "LT", "GT", "NOT", "READ", "WRITE"]
    for i in range(10):
        listing = [rng.choice(instrs) for _ in range(6)] + ["HALT"]
        source = assemble("\n".join(listing))
        tasks.append({
            "id": f"explain-{i}", "kind": "explain", "expected_listing": listing,
            "prompt": f"List the instructions of this emd program:\n{wrapped(source)}\n"
                      "Answer with one mnemonic per line, such as PUSH 3 or ADD, and nothing else.",
        })

    for i in range(10):
        source = compile_print(TEXTS[i])
        at = rng.randrange(len(source))
        wrong = rng.choice([c for c in ALPHABET if c != source[at]])
        other = source[:at] + wrong + source[at + 1:]
        tasks.append({
            "id": f"distinguish-{i}", "kind": "distinguish", "expected_index": at,
            "prompt": "These two strings differ in exactly one code point:\n"
                      f"{source}\n{other}\n"
                      "Answer with its 0-based index only.",
        })

    tasks += hard_tasks(rng)

    with open(HERE / "tasks.jsonl", "w", encoding="ascii") as f:
        for task in tasks:
            f.write(json.dumps(task, ensure_ascii=True) + "\n")
    print(f"{len(tasks)} tasks written ({ROOT.name})")


if __name__ == "__main__":
    main()

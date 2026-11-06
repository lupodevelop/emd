#!/bin/sh
# The experiment behind the results: every model under every condition. Resumable.
# usage: experiment.sh [--codex] [reps] [Claude budget per model and condition, USD]
set -u
provider=claude
if [ "${1:-}" = "--codex" ]; then provider=codex; shift; fi
cd "$(dirname "$0")"
reps="${1:-3}"
budget="${2:-6}"
if [ "$provider" = codex ]; then
  for model in gpt-6-luna gpt-6.1-sol; do
    for condition in bare explicit schema plain; do
      python3 run.py "$model" --provider codex --condition "$condition" --reps "$reps" --jobs 2 --effort medium || exit 1
    done
  done
  python3 analyze.py results/codex-v1 --baseline results/v3
  exit $?
fi
for model in haiku sonnet opus; do
  for condition in bare explicit schema plain; do
    python3 run.py "$model" --condition "$condition" --reps "$reps" --budget "$budget"
  done
done

1323 answers, $23.70. Served: claude-haiku-5-5, claude-opus-5-5, claude-sonnet-5, claude-sonnet-5-5.

## By model and condition

Percentages with 95% Wilson intervals. Format loss: correct answers rejected only for their wrapping.

| Model / condition | n | Strict % | Unwrapped % | Format loss % |
| --- | --- | --- | --- | --- |
| haiku/bare | 147 | 46.3 [38.4, 54.3] | 65.3 [57.3, 72.5] | 29.2 [21.0, 38.9] |
| haiku/explicit | 147 | 68.0 [60.1, 75.0] | 68.0 [60.1, 75.0] | 0.0 [0.0, 3.7] |
| haiku/schema | 147 | 68.0 [60.1, 75.0] | 69.4 [61.5, 76.3] | 2.0 [0.5, 6.9] |
| sonnet/bare | 147 | 72.1 [64.4, 78.7] | 87.1 [80.7, 91.6] | 17.2 [11.6, 24.7] |
| sonnet/explicit | 147 | 89.8 [83.8, 93.7] | 89.8 [83.8, 93.7] | 0.0 [0.0, 2.8] |
| sonnet/schema | 147 | 88.4 [82.3, 92.7] | 90.5 [84.6, 94.2] | 2.3 [0.8, 6.4] |
| opus/bare | 147 | 73.5 [65.8, 79.9] | 98.6 [95.2, 99.6] | 25.5 [19.1, 33.2] |
| opus/explicit | 147 | 99.3 [96.2, 99.9] | 99.3 [96.2, 99.9] | 0.0 [0.0, 2.6] |
| opus/schema | 147 | 98.6 [95.2, 99.6] | 98.6 [95.2, 99.6] | 0.0 [0.0, 2.6] |

## By task, condition bare

| Kind / tier | n | Strict % | Unwrapped % | Format loss % |
| --- | --- | --- | --- | --- |
| complete/easy | 27 | 77.8 | 88.9 | 12.5 |
| complete/hard | 36 | 55.6 | 55.6 | 0.0 |
| copy/easy | 27 | 100.0 | 100.0 | 0.0 |
| copy/hard | 54 | 90.7 | 90.7 | 0.0 |
| distinguish/easy | 27 | 66.7 | 100.0 | 33.3 |
| distinguish/hard | 45 | 53.3 | 75.6 | 29.4 |
| explain/easy | 27 | 100.0 | 100.0 | 0.0 |
| explain/hard | 45 | 80.0 | 80.0 | 0.0 |
| generate/easy | 27 | 18.5 | 96.3 | 80.8 |
| generate/hard | 63 | 27.0 | 73.0 | 63.0 |
| repair/easy | 27 | 63.0 | 96.3 | 34.6 |
| repair/hard | 36 | 58.3 | 75.0 | 22.2 |

## Wrapping, by condition

- bare: none 324, code fence 61, bold 23, spacing 23, backticks 8, other text 2
- explicit: none 434, spacing 7
- schema: none 425, spacing 13, other text 3

## Strict success against bare, paired (exact McNemar)

| Model / condition | Only bare | Only other | p |
| --- | --- | --- | --- |
| haiku/explicit | 10 | 42 | 9.1e-06 |
| haiku/schema | 10 | 42 | 9.1e-06 |
| sonnet/explicit | 3 | 29 | 2.6e-06 |
| sonnet/schema | 4 | 28 | 1.9e-05 |
| opus/explicit | 1 | 39 | 7.5e-11 |
| opus/schema | 0 | 37 | 1.5e-11 |
| all/explicit | 14 | 110 | 1.2e-19 |
| all/schema | 14 | 107 | 6.5e-19 |

## Task level against bare: each task counted once (sign test)

| Model / condition | Better | Worse | Same | p |
| --- | --- | --- | --- | --- |
| haiku/explicit | 26 | 5 | 18 | 0.00019 |
| haiku/schema | 23 | 4 | 22 | 0.00031 |
| sonnet/explicit | 15 | 2 | 32 | 0.0023 |
| sonnet/schema | 16 | 2 | 31 | 0.0013 |
| opus/explicit | 20 | 0 | 29 | 1.9e-06 |
| opus/schema | 20 | 0 | 29 | 1.9e-06 |
| all/explicit | 31 | 2 | 16 | 1.3e-07 |
| all/schema | 34 | 2 | 13 | 1.9e-08 |

## Pairs of models, condition bare

Wins of each side on the same task and repetition.

| Pair | Strict | p | Unwrapped | p |
| --- | --- | --- | --- | --- |
| sonnet vs opus | 24 to 26 | 0.89 | 2 to 19 | 0.00022 |
| haiku vs sonnet | 6 to 44 | 3.2e-08 | 6 to 38 | 9.4e-07 |
| haiku vs opus | 13 to 53 | 7.2e-07 | 1 to 50 | 4.6e-14 |

Served models per call: claude-haiku-5-5 (441), claude-opus-5-5 (441), claude-sonnet-5-5 (436), claude-sonnet-5,claude-sonnet-5-5 (5).

## Copying, condition schema

| Model / length | Exact | Mean edit size |
| --- | --- | --- |
| haiku/16 | 9/9 | 0.000 |
| haiku/256 | 9/9 | 0.000 |
| haiku/1024 | 6/9 | 0.000 |
| opus/16 | 9/9 | 0.000 |
| opus/256 | 9/9 | 0.000 |
| opus/1024 | 9/9 | 0.000 |
| sonnet/16 | 9/9 | 0.000 |
| sonnet/256 | 9/9 | 0.000 |
| sonnet/1024 | 9/9 | 0.000 |

Most frequent substitutions: U+2010>U+2012 (2).

1150 answers, $13.52. Served: claude-haiku-5-5, claude-sonnet-5, claude-sonnet-5-5.

## By model and condition

Percentages with 95% Wilson intervals. Compiles: program tasks whose exact answer the compiler accepts. Strict: correct as written. Content: correct once Markdown and line layout are undone. Format loss: right answers rejected only for their clothes.

| Model / condition | n | Compiles % | Strict % | Unwrapped % | Content % | Format loss % |
| --- | --- | --- | --- | --- | --- | --- |
| haiku/bare | 147 | 29.2 [19.9, 40.5] | 47.6 [39.7, 55.7] | 70.7 [62.9, 77.5] | 71.4 [63.7, 78.1] | 33.3 [25.0, 42.8] |
| haiku/explicit | 146 | 71.8 [60.5, 81.0] | 74.7 [67.0, 81.0] | 74.7 [67.0, 81.0] | 74.7 [67.0, 81.0] | 0.0 [0.0, 3.4] |
| haiku/schema | 146 | 67.6 [56.1, 77.3] | 73.3 [65.6, 79.8] | 74.0 [66.3, 80.4] | 74.0 [66.3, 80.4] | 0.9 [0.2, 5.1] |
| haiku/plain | 146 | 33.8 [23.9, 45.4] | 52.1 [44.0, 60.0] | 69.2 [61.3, 76.1] | 69.2 [61.3, 76.1] | 24.8 [17.4, 34.0] |
| sonnet/bare | 147 | 76.4 [65.4, 84.7] | 81.6 [74.6, 87.1] | 85.7 [79.1, 90.5] | 87.1 [80.7, 91.6] | 6.2 [3.2, 11.8] |
| sonnet/explicit | 147 | 80.6 [70.0, 88.0] | 88.4 [82.3, 92.7] | 88.4 [82.3, 92.7] | 90.5 [84.6, 94.2] | 2.3 [0.8, 6.4] |
| sonnet/schema | 147 | 80.6 [70.0, 88.0] | 87.1 [80.7, 91.6] | 87.1 [80.7, 91.6] | 92.5 [87.1, 95.8] | 5.9 [3.0, 11.2] |
| sonnet/plain | 124 | 75.4 [63.7, 84.2] | 82.3 [74.6, 88.0] | 83.1 [75.5, 88.6] | 85.5 [78.2, 90.6] | 3.8 [1.5, 9.3] |

## By task, condition bare

| Kind / tier | n | Compiles % | Strict % | Unwrapped % | Content % | Format loss % |
| --- | --- | --- | --- | --- | --- | --- |
| complete/easy | 18 | 88.9 | 88.9 | 88.9 | 88.9 | 0.0 |
| complete/hard | 24 | 29.2 | 20.8 | 33.3 | 45.8 | 54.5 |
| copy/easy | 18 | - | 100.0 | 100.0 | 100.0 | 0.0 |
| copy/hard | 36 | - | 97.2 | 97.2 | 97.2 | 0.0 |
| distinguish/easy | 18 | - | 61.1 | 100.0 | 100.0 | 38.9 |
| distinguish/hard | 30 | - | 60.0 | 86.7 | 86.7 | 30.8 |
| explain/easy | 18 | - | 94.4 | 94.4 | 94.4 | 0.0 |
| explain/hard | 30 | - | 70.0 | 70.0 | 70.0 | 0.0 |
| generate/easy | 18 | 55.6 | 55.6 | 77.8 | 77.8 | 28.6 |
| generate/hard | 42 | 38.1 | 33.3 | 64.3 | 64.3 | 48.1 |
| repair/easy | 18 | 83.3 | 77.8 | 83.3 | 83.3 | 6.7 |
| repair/hard | 24 | 50.0 | 45.8 | 62.5 | 62.5 | 26.7 |

## Cost

US dollars at the prices the client reports. Per clean: cost of one answer usable as it stands.

| Model / condition | Answers | Output tokens | Cost | Per answer | Per clean |
| --- | --- | --- | --- | --- | --- |
| haiku/bare | 147 | 758483 | 0.41 | 0.0028 | 0.0059 |
| haiku/explicit | 146 | 788517 | 0.42 | 0.0029 | 0.0038 |
| haiku/schema | 146 | 917959 | 0.48 | 0.0033 | 0.0045 |
| haiku/plain | 146 | 882043 | 0.46 | 0.0032 | 0.0061 |
| sonnet/bare | 147 | 239767 | 2.76 | 0.0188 | 0.0230 |
| sonnet/explicit | 147 | 262415 | 3.03 | 0.0206 | 0.0233 |
| sonnet/schema | 147 | 279425 | 3.74 | 0.0254 | 0.0292 |
| sonnet/plain | 124 | 191158 | 2.22 | 0.0179 | 0.0218 |
| haiku | 585 | 3347002 | 1.77 | 0.0030 | 0.0049 |
| sonnet | 565 | 972765 | 11.75 | 0.0208 | 0.0245 |

## How answers were dressed, by condition

- bare: none 217, code fence 42, bold 17, spacing 9, long line 6, other text 2, backticks 1
- explicit: none 276, spacing 9, long line 7, other text 1
- schema: none 270, long line 14, spacing 5, other text 4
- plain: none 204, code fence 37, bold 10, long line 10, spacing 8, backticks 1

## Strict success against bare, paired (exact McNemar)

| Model / condition | Only bare | Only other | p |
| --- | --- | --- | --- |
| haiku/explicit | 7 | 46 | 4e-08 |
| haiku/schema | 8 | 45 | 2.4e-07 |
| haiku/plain | 16 | 22 | 0.42 |
| sonnet/explicit | 7 | 17 | 0.064 |
| sonnet/schema | 11 | 19 | 0.2 |
| sonnet/plain | 11 | 12 | 1 |
| all/explicit | 14 | 63 | 1.4e-08 |
| all/schema | 19 | 64 | 7.4e-07 |
| all/plain | 27 | 34 | 0.44 |

## Task level against bare: each task counted once (sign test)

| Model / condition | Better | Worse | Same | p |
| --- | --- | --- | --- | --- |
| haiku/explicit | 24 | 4 | 21 | 0.00018 |
| haiku/schema | 22 | 2 | 25 | 3.6e-05 |
| haiku/plain | 14 | 10 | 25 | 0.54 |
| sonnet/explicit | 10 | 5 | 34 | 0.3 |
| sonnet/schema | 13 | 7 | 29 | 0.26 |
| sonnet/plain | 8 | 6 | 35 | 0.79 |
| all/explicit | 26 | 3 | 20 | 1.5e-05 |
| all/schema | 24 | 5 | 20 | 0.00055 |
| all/plain | 15 | 9 | 25 | 0.31 |

## Pairs of models, condition bare

Wins of each side on the same task and repetition.

| Pair | Strict | p | Content | p |
| --- | --- | --- | --- | --- |
| haiku vs sonnet | 5 to 55 | 1e-11 | 7 to 30 | 0.00019 |

Served models per call: claude-haiku-5-5 (585), claude-sonnet-5-5 (562), claude-sonnet-5,claude-sonnet-5-5 (3).

## Copying, condition schema

| Model / length | Exact | Mean edit size |
| --- | --- | --- |
| haiku/16 | 9/9 | 0.000 |
| haiku/256 | 9/9 | 0.000 |
| haiku/1024 | 8/9 | 0.000 |
| sonnet/16 | 9/9 | 0.000 |
| sonnet/256 | 9/9 | 0.000 |
| sonnet/1024 | 9/9 | 0.000 |

Most frequent substitutions: U+2010>U+2012 (1).

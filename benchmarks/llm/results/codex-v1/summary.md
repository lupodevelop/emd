573 completed OpenAI CLI answers. Collection stopped early; missing responses are not scored as incorrect.

| Requested model | Condition | n | Compiles | Strict % | Content % | API-equivalent USD | Per strict success USD |
| --- | --- | ---: | --- | ---: | ---: | ---: | ---: |
| gpt-6-luna | bare | 67 | 21.2 (7/33) | 26.9 | 26.9 | 0.0557 | 0.0031 |
| gpt-6-luna | explicit | 16 | 42.9 (3/7) | 18.8 | 18.8 | 0.0120 | 0.0040 |
| gpt-6-luna | schema | 80 | 30.4 (14/46) | 36.2 | 37.5 | 0.0770 | 0.0027 |
| gpt-6.1-sol | bare | 147 | 100.0 (72/72) | 98.6 | 98.6 | 2.4459 | 0.0169 |
| gpt-6.1-sol | explicit | 147 | 100.0 (72/72) | 100.0 | 100.0 | 1.6561 | 0.0113 |
| gpt-6.1-sol | schema | 116 | 100.0 (57/57) | 100.0 | 100.0 | 1.6990 | 0.0146 |

Illustrative API-equivalent Standard short-context text-token cost for completed CLI responses, not invoiced subscription expenditure. Unreported failed/aborted usage excluded.

Completed-call API-equivalent total: USD 5.9456. No dollar cost is imputed to missing usage.

Sol bare versus explicit: 0 only bare, 2 only explicit, exact McNemar p=0.50; 147 matched answers.

Rates and calculation: see protocol.json and summary.json.

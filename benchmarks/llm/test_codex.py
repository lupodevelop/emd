"""Offline checks for the Codex CLI adapter; never calls a model."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import codex_cli
from run import run


def events(answer='–‒\n'):
    return '\n'.join(json.dumps(item) for item in [
        {'type': 'thread.started', 'thread_id': 'private'},
        {'type': 'turn.started'},
        {'type': 'item.completed', 'item': {'type': 'reasoning', 'text': 'not an answer'}},
        {'type': 'item.completed', 'item': {'type': 'agent_message', 'text': answer}},
        {'type': 'turn.completed', 'usage': {'input_tokens': 20, 'cached_input_tokens': 4, 'output_tokens': 7}},
    ])


class CodexTests(unittest.TestCase):
    def test_exact_answer_and_usage_without_invented_cost(self):
        result = codex_cli.parse_events(events())
        self.assertEqual(result['result'], '–‒\n')
        self.assertEqual(result['usage']['output_tokens'], 7)
        self.assertIsNone(result['total_cost_usd'])
        self.assertEqual(result['modelUsage'], {})

    def test_failed_incomplete_and_tool_using_turns_are_rejected(self):
        for text in [events().rsplit('\n', 1)[0], events() + '\n' + json.dumps({'type': 'turn.failed'}),
                     events() + '\n' + json.dumps({'type': 'item.completed', 'item': {'type': 'command_execution'}})]:
            with self.assertRaises(RuntimeError):
                codex_cli.parse_events(text)

    def test_startup_warning_is_not_a_tool_call(self):
        warning = json.dumps({'type': 'item.completed', 'item': {'type': 'error', 'message': 'Under-development features enabled: skip_host_skill_discovery'}})
        self.assertEqual(codex_cli.parse_events(warning + '\n' + events())['result'], '–‒\n')

    def test_schema_extracts_only_the_answer_field(self):
        result = codex_cli.parse_events(events('{"answer":"–‒\\n"}'), schema=True)
        self.assertEqual(result['structured_output']['answer'], '–‒\n')
        for answer in ['{}', '{"answer":1}', '{"answer":"x","extra":1}', '```json\n{"answer":"x"}\n```']:
            with self.assertRaises((ValueError, RuntimeError)):
                codex_cli.parse_events(events(answer), schema=True)

    def test_command_uses_isolated_context_and_only_the_task_as_stdin(self):
        captured = {}
        def fake(command, **kwargs):
            captured.update(command=command, **kwargs)
            root = Path(kwargs['cwd'])
            self.assertEqual((root / 'instructions.txt').read_text(), 'THE ISA')
            self.assertEqual(json.loads((root / 'answer.schema.json').read_text())['required'], ['answer'])
            return type('Done', (), {'returncode': 0, 'stdout': events('{"answer":"–‒\\n"}').encode(), 'stderr': b''})()
        with patch('codex_cli.subprocess.run', fake):
            codex_cli.ask('codex', 'gpt-6-luna', 'THE ISA', 'THE TASK', 'schema', 'medium')
        command = captured['command']
        for option in ['--ignore-user-config', '--ignore-rules', '--ephemeral', '--skip-git-repo-check', '--json', '--output-schema']:
            self.assertIn(option, command)
        self.assertEqual(captured['input'], b'THE TASK')
        self.assertIn('project_doc_max_bytes=0', command)
        self.assertNotIn('OPENAI_API_KEY', captured['env'])
        self.assertNotIn('CODEX_API_KEY', captured['env'])

    def test_resume_preserves_codex_answers_and_metadata(self):
        tasks = [{'id': 'one', 'kind': 'generate', 'prompt': 'source only'}]
        with tempfile.TemporaryDirectory() as directory, patch('run.codex_cli.ask', return_value=codex_cli.parse_events(events())) as ask:
            out = Path(directory) / 'answers.jsonl'
            self.assertEqual(run('gpt-6-luna', tasks, out, provider='codex'), 0)
            self.assertEqual(run('gpt-6-luna', tasks, out, provider='codex'), 0)
            self.assertEqual(ask.call_count, 1)
            row = json.loads(out.read_text())
            self.assertEqual(row['response'], '–‒\n')
            self.assertEqual(row['provider'], 'codex')
            self.assertEqual(row['reasoning_effort'], 'medium')
            self.assertIsNone(row['cost_usd'])
            self.assertEqual(row['input_tokens'], 20)
            with self.assertRaises(ValueError):
                run('gpt-6-luna', tasks, out, provider='codex', effort='high')


    def test_repeated_transport_failures_stop_the_run(self):
        tasks = [{'id': str(i), 'kind': 'copy', 'prompt': 'copy'} for i in range(10)]
        with tempfile.TemporaryDirectory() as directory, patch('run.codex_cli.ask', side_effect=RuntimeError('transport failed')) as ask:
            self.assertEqual(run('gpt-6-luna', tasks, Path(directory) / 'answers.jsonl', provider='codex'), 3)
            self.assertEqual(ask.call_count, 3)

    def test_analysis_keeps_subscription_cost_unknown(self):
        from analyze import counts, load, summarize, markdown, write_latex
        self.assertIsNone(counts([{'class': 'clean', 'cost': None, 'tokens': 7, 'compiles': None}])['cost_usd'])
        tasks = [json.loads(line) for line in (Path(__file__).parent / 'tasks.jsonl').read_text().splitlines()]
        task = next(t for t in tasks if t['kind'] == 'distinguish')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'gpt-6-luna.bare.jsonl').write_text(json.dumps({
                'id': task['id'], 'response': str(task['expected_index']), 'cost_usd': None,
                'served': [], 'input_tokens': 20, 'output_tokens': 7,
            }) + '\n')
            summary = summarize(load(root))
            self.assertEqual(summary['by_model']['gpt-6-luna']['clean'], 1)
            self.assertIsNone(summary['cost_usd'])
            self.assertNotIn('$0.00', markdown(summary))
            write_latex(summary, root / 'tables')
            self.assertIn('benchLunaBareStrict', (root / 'tables/numbers.tex').read_text())


if __name__ == '__main__':
    unittest.main()

"""One isolated Codex CLI turn, using the existing ChatGPT login."""
import json
import os
import pathlib
import subprocess
import tempfile

DISABLED = ('shell_tool', 'apps', 'plugins', 'memories', 'multi_agent', 'browser_use',
            'computer_use', 'in_app_browser', 'sleep_tool', 'skill_search', 'hooks', 'tool_suggest')


def parse_events(text, schema=False):
    answer = None
    usage = None
    for line in text.splitlines():
        if not line.strip():
            continue
        event = json.loads(line)
        kind = event.get('type')
        if kind in ('turn.failed', 'error'):
            raise RuntimeError('Codex turn failed')
        item = event.get('item')
        if item:
            if item.get('type') == 'error' and item.get('message', '').startswith('Under-development features enabled:'):
                continue
            if item.get('type') not in ('reasoning', 'agent_message'):
                raise RuntimeError(f"Codex used a tool: {item.get('type')}")
            if kind == 'item.completed' and item.get('type') == 'agent_message':
                answer = item['text']
        if kind == 'turn.completed':
            usage = event.get('usage', {})
    if answer is None or usage is None:
        raise RuntimeError('Codex did not return a completed answer')
    result = {'result': answer, 'usage': usage, 'modelUsage': {}, 'total_cost_usd': None}
    if schema:
        value = json.loads(answer)
        if not isinstance(value, dict) or set(value) != {'answer'} or not isinstance(value['answer'], str):
            raise RuntimeError('Codex answer does not match the schema')
        result['structured_output'] = value
    return result


def ask(cli, model, system, prompt, condition, effort='medium'):
    from run import SCHEMA, TIMEOUT
    with tempfile.TemporaryDirectory(prefix='emd-codex-') as directory:
        root = pathlib.Path(directory)
        instructions = root / 'instructions.txt'
        instructions.write_text(system, encoding='utf-8')
        command = [cli, 'exec', '--ignore-user-config', '--ignore-rules', '--strict-config',
                   '--ephemeral', '--skip-git-repo-check', '--sandbox', 'read-only',
                   '--json', '--color', 'never', '--model', model]
        settings = [
            'model_provider="openai"', 'approval_policy="never"',
            'model_instructions_file=' + json.dumps(str(instructions)),
            'model_reasoning_effort=' + json.dumps(effort), 'project_doc_max_bytes=0',
            'skills.include_instructions=false', 'skills.bundled.enabled=false',
            'web_search="disabled"', 'tools.update_plan.enabled=false',
            'tools.experimental_request_user_input.enabled=false',
            'history.persistence="none"', 'features.skip_host_skill_discovery=true',
            'suppress_unstable_features_warning=true',
        ]
        settings += [f'features.{feature}=false' for feature in DISABLED]
        for setting in settings:
            command += ['-c', setting]
        if condition == 'schema':
            schema = root / 'answer.schema.json'
            schema.write_text(SCHEMA)
            command += ['--output-schema', str(schema)]
        command += ['-']
        env = dict(os.environ)
        # This experiment uses the subscription login, never environment API keys.
        for name in list(env):
            if name == 'OPENAI_API_KEY' or (name.startswith('CODEX_') and name != 'CODEX_HOME'):
                env.pop(name, None)
        done = subprocess.run(command, input=prompt.encode('utf-8'), capture_output=True,
                              cwd=directory, env=env, timeout=TIMEOUT)
    if done.returncode:
        detail = done.stderr.decode('utf-8', 'replace')[-800:]
        raise RuntimeError(detail or f'Codex exited with status {done.returncode}')
    return parse_events(done.stdout.decode('utf-8'), schema=condition == 'schema')

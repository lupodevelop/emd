"""Check the release tag against Cargo.toml and print its changelog section."""
import re
import os
import sys
import tomllib
from pathlib import Path

version = tomllib.loads(Path('Cargo.toml').read_text())['workspace']['package']['version']
if len(sys.argv) != 2 or sys.argv[1] != f'v{version}':
    sys.exit(f'The release tag must match Cargo.toml: v{version}')

section = re.search(
    rf'^## \[{re.escape(version)}\][^\n]*\n(.*?)(?=^## |\Z)',
    Path('CHANGELOG.md').read_text(), re.M | re.S,
)
if not section:
    sys.exit(f'CHANGELOG.md needs a section [{version}]')
notes = section[1].strip()
if not re.sub(r'<!--.*?-->', '', notes, flags=re.S).strip():
    sys.exit(f'CHANGELOG.md section [{version}] is empty')
logo = f'https://raw.githubusercontent.com/{os.environ.get("GITHUB_REPOSITORY", "lupodevelop/emd")}/{sys.argv[1]}/assets'
print(f'<picture><source media="(prefers-color-scheme: dark)" srcset="{logo}/logo-on-dark.svg"><img src="{logo}/logo-on-light.svg" alt="emd" width="240"></picture>\n')
print(notes)

#!/usr/bin/env python3
"""Render editable SVG social cards and crawler-friendly PNGs; requires rsvg-convert."""
import json
import subprocess
from html import escape
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CARDS = json.loads((ROOT / 'website/src/lib/social-cards.json').read_text())
SOURCES = ROOT / 'assets/social'
PUBLIC = ROOT / 'website/public/social'


def main():
    SOURCES.mkdir(parents=True, exist_ok=True)
    PUBLIC.mkdir(parents=True, exist_ok=True)
    logo = (ROOT / 'assets/logo-on-dark.svg').read_text()
    logo = logo.replace('<svg ', '<svg x="64" y="40" width="268" height="99" ', 1)
    for key, card in CARDS.items():
        lines = ''.join(f'<text x="64" y="{285 + i * 85}">{escape(line)}</text>'
                        for i, line in enumerate(card['headline']))
        svg = f'''<svg xmlns="http://www.w3.org/2000/svg" width="1200" height="630" viewBox="0 0 1200 630">
  <title>{escape(card['alt'])}</title>
  <rect width="1200" height="630" fill="#1b1820"/>
  <path d="M64 172H1136M64 552H1136" stroke="#52475e" stroke-width="2"/>
  {logo}
  <g font-family="Menlo, monospace">
    <text x="1136" y="106" text-anchor="end" font-size="19" letter-spacing="2" fill="#bcace8">{escape(card['label'])}</text>
    <g fill="#f0e9e0" font-size="66" font-weight="bold" letter-spacing="-3">{lines}</g>
    <text x="66" y="434" font-size="22" fill="#b5a9be">{escape(card['detail'])}</text>
    <text x="64" y="515" font-size="43" letter-spacing="15" fill="#bcace8">- ‐ ‑ ‒ – — ― −</text>
    <text x="64" y="593" font-size="18" fill="#b5a9be">lupodevelop.github.io/emd</text>
    <text x="1136" y="593" text-anchor="end" font-size="18" fill="#bcace8">EMOTIONAL DAMAGE.</text>
  </g>
</svg>
'''
        source = SOURCES / f'{key}.svg'
        source.write_text(svg)
        subprocess.run(['rsvg-convert', '-o', str(PUBLIC / f'{key}.png'), str(source)], check=True)
    icon = SOURCES / 'apple-touch-icon.svg'
    icon.write_text(f'''<svg xmlns="http://www.w3.org/2000/svg" width="180" height="180" viewBox="0 0 180 180">
  <rect width="180" height="180" rx="32" fill="#1b1820"/>
  {logo.replace('x="64" y="40" width="268" height="99"', 'x="22" y="64" width="136" height="51"')}
</svg>''')
    subprocess.run(['rsvg-convert', '-o', str(ROOT / 'website/public/apple-touch-icon.png'), str(icon)], check=True)
    print(f'Rendered {len(CARDS)} social cards (1200 × 630) and the touch icon (180 × 180).')


if __name__ == '__main__':
    main()

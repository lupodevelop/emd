# Website

Requires Rust, Node.js 26, npm and Python 3.

From the repository root:

```sh
rustup target add wasm32-unknown-unknown
scripts/build-wasm.sh
cd website
npm ci
npm run dev
```

`npm run build` writes `dist/`.

## Editing

| Content | Location |
| --- | --- |
| Manual | `../docs/` |
| Examples | `../examples/` |
| Language paper | `../paper/emd.pdf` and `src/data/paper.json` |
| CLI case study | `../benchmarks/llm/report/experiment.pdf` and `src/data/experiment.json` |
| Page metadata | `src/components/Metadata.astro` and `src/lib/metadata.ts` |
| Social cards | `src/lib/social-cards.json` and `../assets/social/` |
| Public URL and base path | `astro.config.mjs` |

For each paper, update its PDF and web data together. Manual formulas use KaTeX: `$…$` inline,
`$$…$$` for display.

To regenerate the social card PNGs, run `python3 assets/social/render.py` from
the repository root. Requires `rsvg-convert` and Menlo.

The sitemap is served at `/emd/sitemap.xml`. GitHub Pages project sites cannot
set the origin's `/robots.txt`; add the sitemap URL there if you manage that site.

Design inspired by [Omarchy](https://github.com/omacom/omarchy-site).

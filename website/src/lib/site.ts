// Every link inside the site goes through here: it is published under a path, not at a domain's root.
export const url = (path: string) => `${import.meta.env.BASE_URL}${path}`;

import instructions from './instructions.json';

export const sourceLineMax = 32;

export const alphabet = [
  { glyph: '-', key: 'a', code: '002D', name: 'Hyphen-minus', verdict: 'The one on your keyboard.' },
  { glyph: '‐', key: 's', code: '2010', name: 'Hyphen', verdict: 'Already a different character.' },
  { glyph: '‑', key: 'd', code: '2011', name: 'Non-breaking hyphen', verdict: 'Refuses to break. Will break you.' },
  { glyph: '‒', key: 'f', code: '2012', name: 'Figure dash', verdict: 'A figure of your imagination.' },
  { glyph: '–', key: 'g', code: '2013', name: 'En dash', verdict: 'Half an em. Twice the doubt.' },
  { glyph: '—', key: 'h', code: '2014', name: 'Em dash', verdict: 'The reason we are all here.' },
  { glyph: '―', key: 'j', code: '2015', name: 'Horizontal bar', verdict: 'The bar was already low.' },
  { glyph: '−', key: 'k', code: '2212', name: 'Minus sign', verdict: 'Subtracts from your sanity.' },
];

export const themes = [
  { id: 'ash', name: 'Ash', color: '#bcace8' },
  { id: 'matcha', name: 'Matcha', color: '#b6c99a' },
  { id: 'ember', name: 'Ember', color: '#edac8d' },
  { id: 'blueprint', name: 'Blueprint', color: '#9bbdea' },
  { id: 'paper', name: 'Paper', color: '#e9dfc9' },
];

export const manuals = [
  { slug: 'studio', title: 'Write your first program', description: 'Write and debug your first emd program in Neovim Studio: exact letters to type, debugger controls and results to expect.' },
  { slug: 'language-spec', title: 'The language', description: 'The emd source format: eight Unicode dashes, instruction pairs, line limits, decoding errors and canonical layout. No substitutions.' },
  { slug: 'isa', title: 'Instruction set', description: `The ${instructions.length} emd instructions: Unicode encodings, stack operations, arithmetic, memory, control flow and byte input/output.` },
  { slug: 'assembly', title: 'Readable assembly', description: 'Compile readable emd assembly into Unicode dashes: constants, labels, integer synthesis and jump layout, with examples and diagnostics.' },
  { slug: 'semantics', title: 'Semantics', description: 'How emd executes: stack and memory, program counters, arithmetic, input/output, faults and the limits of the Rust virtual machine.' },
  { slug: 'tools', title: 'Tools', description: 'Explore the emd tools: static analysis, backward debugging, native C compilation, Unicode diagnostics, profiling and Neovim Studio.' },
  { slug: 'verification', title: 'Verification', description: 'What is proved and what is tested in emd: Lean and Rocq models, bounded Rust verification, differential tests, mutation testing and limits.' },
];

// Preserve explicit breaks and cursor positions; wrap only overlong lines.
export function wrapSource(text: string, start: number, end: number, limit: number) {
  let value = '', column = 0, offset = 0;
  let nextStart = start, nextEnd = end;
  for (const glyph of text) {
    if (glyph !== '\n' && column === limit) { value += '\n'; column = 0; }
    if (offset === start) nextStart = value.length;
    if (offset === end) nextEnd = value.length;
    value += glyph;
    column = glyph === '\n' ? 0 : column + 1;
    offset += glyph.length;
  }
  if (offset === start) nextStart = value.length;
  if (offset === end) nextEnd = value.length;
  return { value, start: nextStart, end: nextEnd };
}

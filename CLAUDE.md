# Repository guidance

## Comments

Write comments for a reviewer reading *this* version of the code, with no
access to its history and no interest in its future. Explain what the code
does, not how it came to look this way.

- **Keep them short and self-contained.** A comment should make sense on its
  own, next to the code it describes.
- **Describe what the code does**, and only when the code alone doesn't make it
  clear. Prefer no comment over one that restates the code.
- **No history.** Don't mention what the code used to do, what a previous
  approach was, what bug this fixes, what was "unmasked", "regenerated",
  "previously", or any before/after framing. Don't contrast with other backends
  or earlier attempts.
- **`TODO:` is for present, known work** on this item. Keep it accurate: when
  you change the item, update or remove its `TODO`. Don't speculate about
  possible futures ("we could later…").
- **Don't write anything that will go stale.** Avoid line numbers, counts,
  file cross-references, and dates that a later edit will silently falsify.

Good: `// A const cannot be applied in ProVerif, so declare an applied nullary
item as a fun of the observed arity.`

Avoid: `// This used to emit a const, which broke the AC() case we found after
fixing the integer overflow; now we emit a fun instead.`

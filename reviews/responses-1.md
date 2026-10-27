# Round 1: responses (2026-10-27)

Reviewers: Claude (Opus 5.5), GPT (GPT-6.1-Sol), Grok (4.7). No law was false: all three checked
depth 0, depth 31 (works: size 2^31) and depth 32 (`Array.size` wraps to 0 and every access
reaches the last leaf), which the `d < 32` hypotheses already exclude.

| finding | raised by | change |
|---|---|---|
| `slot`, header and `size_count` comments overclaim at depth 32+ and for non-perfect trees (size follows the left spine: 3 leaves, size 2) | Claude, GPT, Grok | comments say perfect trees, d < 32, and how size is computed |
| `got`/`kept`/`got_size`/`kept_size` duplicate `Pair.snd`/`Pair.fst`, with wrong comments and mixed kinds | Claude, GPT, Grok | removed; laws use `Pair.fst`/`Pair.snd` |
| No extensionality | Claude, GPT | `view_inj` (same depth, same leaves; shapes matter: GPT's example) |
| No `Array.swap` laws | Claude | `swap_view`, `swap_old`, `swap_full` (for any element type) |
| No pair-shaped laws for rewriting destructured results | Claude | `get_pair`, `size_pair` (size is `shln(1, d)`, every d) |
| Slot bridge lemmas | Claude, GPT | `slot_lt`, `slot_small` (the `i >> 2` slot follows from lawful-words' `to_nat_shrn`) |
| Reading a new array | Claude, GPT | `get_new` (every depth, every index) |
| `get_set_same` has unneeded hypotheses | Claude, GPT | dropped: it holds for every tree |
| Spot coverage | Claude, GPT | 10 cases added: aliasing indexes 6 and 14 at depth 3, depth 0 writes, swap, size, clone, get_new (26 in all) |
| lawful-bytes: d = 30 lets the byte length reach 2^32 - 1 and wrap on push | GPT | lawful-bytes now requires d <= 29 |

Not taken:
- List lemmas (get after set, replicate, append) as laws (Claude, GPT). They belong to whoever
  needs them; the proofs will prove them as helpers, and a `lawful-lists` package can follow if
  several packages need the same ones.
- `view_to_list`: Base's `Array.to_list` is a template (`~T`) and cannot appear in a law; the
  comment on `view` says they are the same list.
- `new_lit` (`Array.new` equals the `[v : T^d]` literal): true by `{==}` for concrete types
  (Claude proved it for U32), but not statable for a type parameter.
- A `d <= 30 -> d < 32` helper: lawful-words' `nat_le_trans` covers it.

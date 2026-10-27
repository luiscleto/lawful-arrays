# lawful-arrays: a guide to the laws

`LAWS.bend` holds 21 laws about Base's `Array<T>`.

An array is logically a binary tree of leaves, which the runtime stores as one flat block.
- **`view(a)`:** the leaves read left to right. The laws describe arrays by their views.
- **`full(a, d)`:** a perfect tree, d levels deep, with 2^d leaves. `Array.new` makes perfect
  trees, and every operation keeps them perfect.
- **`slot(i, d)`:** the leaf index i reaches, which is i mod 2^d. Base wraps indexes this way.
- **Elements are `Data`,** as `Array.get` requires; `swap_full` also covers other element types.

| group | laws | in plain terms |
|---|---|---|
| Creating | `new_full`, `new_view`, `get_new` | `Array.new(d, v)` is a perfect tree of 2^d copies of v; reading it anywhere gives v, at any depth and any index |
| Size | `view_length`, `size_count`, `size_pair`, `size_kept` | a perfect tree has 2^d leaves; `Array.size` returns 2^d when d < 32 (`1 << d` in general) and hands back the same array |
| Reading | `get_view`, `get_kept`, `get_pair` | `get(a, i)` returns leaf `slot(i, d)` (d < 32) and hands back the same array; `get_pair` gives the result as a literal pair, so proofs about code that destructures it can rewrite |
| Writing | `set_view`, `set_full`, `get_set_same`, `get_set_other` | `set(a, i, v)` changes exactly leaf `slot(i, d)`; reading what was just written gives it back (for every tree and index); a write leaves every other leaf as it was |
| Swapping | `swap_view`, `swap_old`, `swap_full` | `swap` writes like `set` and returns the old value |
| Equality, indexes | `view_inj`, `slot_lt`, `slot_small` | two perfect trees of the same depth with the same leaves are equal; a slot is below 2^d, and equals i when i < 2^d |
| Cloning | `clone_pair` | `clone(a)` gives `(a, a)` |

## Where to look hardest

- **The `d < 32` bound.** From depth 32 up, Base's `Array.size` wraps to 0, and every access
  goes to the last leaf. The laws that involve an index require `d < 32`. lawful-bytes uses
  depth 29 at most.
- **`get_set_other` compares slots, not indexes.** At depth 3, indexes 6 and 14 reach the same
  leaf. `test/spot.bend` checks that case.

## Left out on purpose

- **Imperfect trees:** Base's own operations never make them.
- **Base's `Array.to_list` and the `[v : T^d]` literal:** both are templates, and cannot appear in
  a law about a type variable. The comments say they agree with `view` and `Array.new`.
- **List lemmas** (get after set, replicate, append): proven as helpers in `proof_base.bend`, not
  published as laws.

The twelve laws hold under the hypotheses written on them. The bound `d < 32` is the exact overflow line: depth 31 still fits in a `U32`, and depth 32 is where `Array.size` becomes 0. I re-ran `bend test/spot.bend` (16 true results) and `bend LAWS.bend --check-only` (12 open laws). Checked against Base's `Array` definitions and against the `Array.get` / `Array.set` / `Array.size` / `Array.new` calls in `lawful-bytes`.

1. **should fix.** `D.slot` (and the header of `LAWS.bend`). The comment says an access at `i` in an array of `2^d` leaves reaches leaf `i` modulo `2^d`. That is what `slot` computes, and it is what Base does for a perfect tree of depth below 32. From depth 32 up it is not what Base does. The laws that mention `slot` (`get_view`, `set_view`, `get_set_other`) already require `Nat.is_lt(d, 32n)`, so those statements stay true. `lawful-bytes` also stays inside the true region: `ok` requires `d <= 30`. The comment has no such bound, and `slot` is the helper a later proof will treat as the model of Base.

   Depth 31 is still a normal power of two. `Array.size` is `U32.shl` once per level above the leaf, and `U32.shl` is `Word.shl(32n, _)`, which shifts in a low 0 and drops the high bit. Thirty-one shifts of 1 leave `2^31`, which is a `U32`. The mask is `2^31 - 1`, the root split compares with `2^30`, and `Word.cmp` decides from the high bit, so `U32.is_lt` is unsigned. Including 31 is right.

   Depth 32, `Array.new(U32, 32n, 0)`, then `Array.set` at index 0 of the value 1:
   - The left spine is 32 nodes, so the size is `U32.shl` applied 32 times to 1, which is 0.
   - `Array.get.at` / `Array.swap.at` mask with `U32.sub(0, 1)`, so the masked index is unchanged, then test `U32.is_lt(i, U32.shr(0))`. Nothing is below 0, so the flag is false at every level.
   - The false branch always recurses into the right child (`h = 0`, `j = i - 0`). The leaf reached is the rightmost leaf, index `2^32 - 1`.
   - `slot(0, 32n)` is `Nat.mod(0, 2^32) = 0`. Leaf 0 is still 0. The value 1 is in the last leaf. `Array.get` at 0 returns 1.

   `set_full` does not need the depth bound. The same walk still replaces one leaf with a leaf, so a perfect tree stays perfect at depth 32 and above. `size_kept`, `get_kept`, and `clone_pair` likewise stay true there: they rebuild the same shape.

   Fix the `slot` comment and the header so they say this is Base's leaf only for a perfect tree of depth below 32. Leave the `d < 32` hypotheses as they are, and leave `set_full` unbounded.

2. **minor.** Comments on `got` and `kept` in `defs.bend`. Both say they are the value and the array returned by `Array.get` or `Array.size`. `got` and `kept` project `Array<T> & T`, which is `Array.get` (and `Array.swap`). `Array.size` returns `Array<T> & U32`, which is what `got_size` and `kept_size` project. For `T = U32`, the two pair types are the same type, and `lawful-bytes` is exactly that case, so `got(U32, Array.size(...))` and `got_size(U32, Array.get(...))` both typecheck and both return the second component. Point the comments at the operation each helper actually projects.

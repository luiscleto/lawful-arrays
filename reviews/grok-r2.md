ACCEPT

The twenty-one laws hold of Base's definitions, including the ones added in this round. `bend test/spot.bend` returns 26 true results, and `bend LAWS.bend --check-only` reports 21 open laws.

`get_set_same` with no hypotheses is true for every tree. `Array.set` is the array half of `Array.swap`, and `swap` and `get` mask with the same size and take the same branch at each node. `swap` replaces a leaf with a leaf, so the shape and the left-spine size are unchanged, and the following `get` at the same index reads that leaf. At depth 32 and above both walks go down the right spine, and the read is still the value just written.

`get_new` is true at every depth. `Array.new` fills every leaf with `v`, so whichever leaf the walk reaches, including the rightmost leaf once `Array.size` has wrapped to 0, the value is `v`.

`size_pair` is true for every depth of a perfect tree. `Array.size` is `U32.shl` once per level of the left spine, and `U32.shln(1, d)` is that same shift repeated `d` times. Both are `2^d` for `d < 32` and both are `0` from depth 32 up.

`slot_lt` and `slot_small` are properties of `Nat.mod` and `Nat.pow(2, d)` only. The modulus is at least 1, so the remainder is strictly below it, and a remainder of a smaller numerator is the numerator.

`swap_view` and `swap_old` match `set_view` and `get_view` on perfect trees of depth below 32, because `set` is the array half of `swap` and the old value is the leaf `get` would read. `swap_full` keeps the shape for any element type, including depth 32 and above.

`view_inj` holds because a perfect tree of depth `d` has only one shape, so the same leaves in order are the same array. `get_pair` is `get_kept` packaged as one pair.

`lawful-bytes` requires `d <= 29`, which is inside `d < 32`. The facts it uses are `new_full`, `get_new`, `get_view`, `get_pair`, `set_view`, `set_full`, `size_pair`, and `slot_small`, and those laws are present and true.

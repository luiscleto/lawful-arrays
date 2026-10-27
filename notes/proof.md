# Proof notes: lawful-arrays

## Status (2026-10-27, 21:25)

All 21 laws of `LAWS.bend` are proven. `./check.sh` runs both gate commands and both print
ALL PROOFS CHECK (`--check-only`, then `--verdict` with the BendTT kernel). Nothing in the import
graph uses `@unsafe` or foreign code. `bend test/spot.bend` is still all True (26 checks).

Files:
- `proof_base.bend`: Bool/Nat/List lemmas Base lacks: `subst`, and/or splitting, `lt_one`,
  `not_lt_le`, `lt_sub`, `pow_pos`, `pow_succ`, `pow_lt` (2^d < 2^e), List get/set over append
  (left and right parts), `replicate_add`, `get_set_ne`, cons and append injectivity.
- `proof_tree.bend`: the `Tree<T>` mirror (see below), the pair lemmas for `swap.lo`/`swap.hi`/
  `set.fin`, `size_eta`, `size_tree`, `view_length`, `new_full`, `new_view`, `get_new`,
  `clone_pair`, `get_pair`, `get_set_same` (any tree), `view_inj`.
- `proof_shape.bend`: `swap_full` and `set_full` for any element type (no mirror possible):
  witness lemmas `size_w` and `swap_w`.
- `proof_words.bend`: the ten U32/Nat facts used, forwarded to `../lawful-words`.
- `proof_index.bend`: the indexing laws. `gg`/`gso`/`gsv`: get, swap's old value and swap's leaves
  along the path in a perfect tree, by induction on the depth; the top level (`size_n`,
  `slot_n`: size 2^d, index `i & (2^d - 1)` = `D.slot(i, d)`); `get_set_other` through `tswap`,
  a tree that mirrors the written array.
- `PROOF.bend`: `def L.name` for every law; laws on a Data array go through the mirror.

## Dependency on lawful-words (read this before committing)

`proof_words.bend` imports `../lawful-words/proof_nat.bend` and `../lawful-words/proof_u32.bend`
directly, not `../lawful-words/PROOF.bend`. Reason: 13 lawful-words laws (the ones that mention
`D.two32()` or `D.wrap`, among them `to_nat_shln_fits`) cannot pass the checker as stated, see
`../lawful-words/notes/proof.md`, so their PROOF.bend cannot reach ALL PROOFS CHECK. Their proof
files restate every law with reusable variables, and the ones used here all check (both
`--check-only` and `--verdict`):
`to_nat_shr`, `is_lt_to_nat`, `is_le_to_nat`, `to_nat_sub_le`, `to_nat_and_mask`,
`to_nat_shln_fits_p` (the `_p` form, with `Nat.pow(2n, 32n)` in place of `D.two32()`), `mod_lt`,
`mod_small`, `div_mul_add`, `mul_comm`.

Risk: the lawful-words agent is still editing those files; a rename there breaks this gate.
`proof_words.bend` is the only place to fix. Once lawful-words is final (or published), point
the imports at its final form (or its hub hash).

## Where it got hard (research data)

- **Arrays are affine inside proofs.** `Array<T>` is a Type, and a lemma call is a live use, so
  a proof can mention a subtree only once: the induction hypothesis on `xs` and any other lemma
  about `xs` cannot both be called (error "consumed more than once"). Copies do not help: a
  `dup` built on `Array.clone` gives copies, but the recursive call on a copy fails termination
  (a copy is not a structural subterm). What worked: mirror the array as a `Tree<T>` (Data),
  with `mirror(a)` returning `t` and `{fromT(t) == a}`, and prove everything about `fromT(t)`,
  where `t` is reusable. Each law becomes one `mirror` call and a rewrite.
- **Elements that are not Data** (`swap_full`, and `set_full`, stated for `T: Type`): no mirror.
  The lemmas return the result array as a witness with its equations
  (`swap.go(a, ..) == (na, old)` and `full(na, d) == full(a, d)`), so each subtree is used once.
- **Sigma quantities.** `&t:A -> B` has affine fields (`(t, +e) = m` is refused); writing
  `Sigma<&2, &2, A, t => B>` makes the equation reusable, needed to transport the hypotheses.
- **No destructuring of a computed value** (`(b, c) = f(x)` is "a match on a computed value"):
  every witness is taken apart in a helper def that receives it as a parameter.
- **`+x = array` is refused** (a let marked reusable must be Data); array subterms are written
  out in full, which makes the motives long.
- **Rewrite direction**: almost every rewrite needed `Equal.sym` (lemmas are stated
  `complex == simple`, rewriting goes the other way). Writing each motive by "mark where the
  old term is in the current goal" avoided most errors; first-try success on most files.
- **Match order**: scrutinees must follow parameter order (`lt_sub` had to take `m` before `k`);
  constructors of an imported type need the module prefix (`P.TLeaf`).
- **2^32**: never unfolded. `pow_lt(d, 32n)` is proven symbolically, and `Nat.pow(2n, 32n)` only
  ever meets itself syntactically (in `size_n`). The kernel really does run out of fuel on
  `{Nat.is_lt(5n, Nat.pow(2n, 32n)) == True{}}` by `{==}`, which bend2 accepts, so this matters.
- **Nothing false found.** Every law held as stated; no hypothesis was unusable.

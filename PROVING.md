# Proving lawful-arrays: brief for the proof agent

## Goal

Prove every law in `LAWS.bend` (21 laws about Base's `Array`: new, size, get, set, swap, clone, on
the list of leaves `D.view`, for perfect trees `D.full`). Three reviewers from different model
families accepted the statements, so they are frozen: never edit `LAWS.bend` or `defs.bend`. If a
law looks false or unprovable as stated, stop and report it with the reason.

Proofs go in `PROOF.bend` (imports `LAWS.bend` and fills every law, as `def name(...) -> {...}:`
with the law's name) plus helper files `proof_*.bend`. Gate, in a `check.sh`:

```
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --check-only
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --verdict
```

Both must print ALL PROOFS CHECK, with no `@unsafe` and no foreign code anywhere in the import
graph. `bend test/spot.bend` must stay all True.

## Dependency on lawful-words

`Array.get`/`Array.swap` walk the tree with U32 arithmetic (`U32.shr`, `U32.and(i, n - 1)`,
`U32.is_lt`, `U32.sub`); `Array.size` is `U32.shl` per level. The facts you need about these are
laws of `../lawful-words` (`to_nat_shr`, `to_nat_and_mask`, `is_lt_to_nat`, `to_nat_sub_le`,
`to_nat_shln`, the Nat section...). Another agent is proving lawful-words right now (workspace
`prove-words`, notes in `../lawful-words/notes/proof.md`); an unproven law cannot be called.
So:
- Start with everything that needs no U32 facts: `D.full`/`D.view` structure, list lemmas
  (List.get/set/append/replicate/length, which Base lacks), `get_kept`, `size_kept`, `get_pair`,
  `clone_pair`, `swap_full`, `set_full`, `get_new`, `get_set_same`, `new_full`, `new_view`,
  `view_length`, `view_inj`, `size_pair` (structural: shln is one shl per level).
- For the indexing laws, state the U32 facts you need as hypotheses of your lemmas first, then
  discharge them by importing `../lawful-words/PROOF.bend` once its laws are proven (check its
  `check.sh`). If you need a U32 fact that lawful-words does not have, prove it yourself.

## Bend proof notes (from the framebender and minebender proofs)

- `%e : G` rewrites with `e : {new == old}`: `G` is the goal with `_` where `old` is; the rest of the
  def proves `G` with `new` there. Use `Equal.sym` to turn an equation around. `Equal.trans`,
  `Equal.cong` are in Base. Rewrite direction was the most frequent error in every earlier proof.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def
  that takes it as a parameter. Matches follow parameter order (`match a b:` for both). No match
  after a let.
- No mutual recursion, no forward references (define helpers first). Termination: the first argument
  that changes must shrink structurally; put it first. Eliminators take the induction hypothesis
  as a function argument.
- Unfilled laws are dead claims: a proof cannot call an open law. Prove in dependency order.
- A law's `for x` without `+` cannot be reused in its proof: restate with `+` where needed (same
  statement otherwise). Every equation used twice needs `+`. Function-typed hypotheses are affine.
- Refuting `{True{} == False{}}` or `{1n+n == 0n}`: rewrite through a `disc` motive that sends one
  constructor to `Empty` and the other to `Unit`, answer `Unit{}`.
- `Bool.pick`, `&&`, `||` evaluate both sides; to reason about them, case-split.
- Recursive defs do not unfold on variables: a lemma about `f(x)` for variable `x` needs a case
  split on `x` first.
- `?name` prints the goal at that point; `?TODO` leaves a hole. Errors print expected/observed terms.
- Every operator needs its type: `(a + b : U32)`. Bare constructors in a let need an annotation.
- `../framebender/proof_base.bend` and `../framebender/proof_machine_nat.bend` have proven Nat and
  Word facts you may copy (same author; MIT). `String.eq` soundness down to `Word.cmp` was proven
  there twice.

## Rules

- Use `nice -n 19` and a `timeout` for every check. No benchmarks.
- Never edit files in `../lawful-words` (read them only).
- No git commits; the lead commits.
- Keep `notes/proof.md`: what is proven, the plan for the rest, and short bullets on where the proofs
  got hard and why (research data: rewrite direction, affinity, a missing lemma...).
- Stop when every law is proven and both gate commands pass, or after about four hours, and report:
  - what is proven;
  - what is left, and why;
  - any law you believe is false or unusable as stated.

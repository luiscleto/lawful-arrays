You are reviewing a draft specification for `lawful-arrays`, a small Bend 2 package that will be
published on BendHub. Base's `Array<T>` is a binary tree (`ALeaf`, `ANode`) that the runtime stores
as one flat block, so `Array.get` and `Array.set` are one load or store. Base states no laws about
it. This package states, as laws, what `Array.new`, `Array.size`, `Array.get`, `Array.set` and
`Array.clone` do, in terms of the list of an array's leaves. The laws will be proven by a proof
checker and then used by `lawful-bytes` (bytes packed four to a `U32` in an `Array<U32>`). A wrong
law means a false proof downstream; a missing law means a downstream proof cannot be done.

Read these files in the current directory (read-only; do not modify anything):
- `LAWS.bend`: the 12 laws (the main object of review).
- `defs.bend`: the definitions the laws use (`full`, `view`, `got`, `kept`, `slot`, ...).
- Base, for how `Array` and its operations are defined: `bend base Array.get`, `bend base Array.set`,
  `bend base Array.size`, `bend base Array.new`, `bend base Array.swap`, `bend base Array.clone`, and
  `bend base` for the whole library. The Bend guide (`bend guide`, section on arrays) says how
  arrays are used.
- `test/spot.bend` evaluates both sides of several laws on small arrays (`bend test/spot.bend`; all
  16 pass). `bend LAWS.bend --check-only` reports 12 unproven laws, as expected.

Bend notes: `law name:` followed by `for x: T` lines is a claim for every x; `for -T: Data` is a type
parameter; `for h: {a == b : T}` is a hypothesis; `{a == b : T}` is equality. `Nat.sub` truncates;
`Nat.mod(a, 0) = a`. Indexes are `U32` and wrap modulo the array's size in Base.

For each definition and law, answer:
(a) Does the Bend mean exactly what its English comment says?
(b) Is it true of Base's definitions as written? If not, give a concrete counterexample worked from
    Base's definitions (array shape, index, value).
(c) Edge cases: depth 0 (one leaf), depth 31 and 32 (`Array.size` computes 2^d in a U32), indexes
    at or beyond the size, arrays that are not perfect trees.
(d) Missing laws that a packed-bytes library will need: it keeps a block of 2^d words, reads word
    `i >> 2`, writes words, allocates with `Array.new`, and states its own laws on the list of bytes
    the words hold.
(e) For a published package: are the names and shapes convenient to use in proofs?

Report a numbered list of findings. For each: the law or definition; severity (blocker / should fix
/ minor); the problem; a concrete example where possible; a suggested fix. Be concrete and brief. If
something is correct, you do not need to say so. End with the full report as your final message.

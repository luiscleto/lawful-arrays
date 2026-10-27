# lawful-arrays

What Bend's `Array` operations do, as laws that a proof checker verifies. Base's `Array<T>` is a
binary tree that the runtime stores as one flat block, so `Array.get` and `Array.set` are a single
load or store; Base states no laws about it. These laws describe `Array.new`, `Array.size`,
`Array.get`, `Array.set`, `Array.swap` and `Array.clone` on the list of an array's leaves, for
perfect trees (what `Array.new` makes and every operation keeps) of depth below 32.

Status: the laws (`LAWS.bend`, definitions in `defs.bend`) were reviewed in two rounds by Claude,
GPT and Grok (`reviews/`). Proofs are next.

`bend test/spot.bend` evaluates both sides of the laws on small arrays.

MIT (see `LICENSE`).

# lawful-arrays

What Bend's `Array` operations do, as laws that a proof checker verifies. Base's `Array<T>` is a
binary tree that the runtime stores as one flat block, so `Array.get` and `Array.set` are a single
load or store; Base states no laws about it. These laws describe `Array.new`, `Array.size`,
`Array.get`, `Array.set`, `Array.swap` and `Array.clone` on the list of an array's leaves, for
perfect trees (what `Array.new` makes and every operation keeps) of depth below 32.

Status: the laws (`LAWS.bend`, definitions in `defs.bend`) were reviewed in two rounds by Claude,
GPT and Grok (`reviews/`), and all 21 are proven (`PROOF.bend`): `./check.sh` checks them with
`bend` and with the Lean-proven kernel (`--verdict`).

`bend test/spot.bend` evaluates both sides of the laws on small arrays.

## Use

Published on [BendHub](https://hub.bend-lang.com/name/lawful-arrays) with its laws and proofs. Bend fetches
an import by name and checks it against the package's hash:

```python
import lawful-arrays@0.1.0.0/defs.bend as A   # the definitions the laws are about
import lawful-arrays@0.1.0.0/LAWS.bend as L   # the laws, to use in your own proofs
import lawful-arrays@0.1.0.0/PROOF.bend as P  # their proofs, which a proof using a law needs loaded
```

Versions below 1.0 have laws reviewed by three AI models but not yet by a human expert.

MIT (see `LICENSE`).

# lawful-arrays

Laws for Bend's built-in `Array`: what `new`, `size`, `get`, `set`, `swap` and `clone` do, stated
on the plain list of an array's elements and verified by Bend's proof checker. The array keeps its
speed (the runtime stores it as one flat block, so `get` and `set` are a single load or store), and
code built on it can be proven by reasoning about a list.

## Use

Bend fetches these imports from [BendHub](https://hub.bend-lang.com/name/lawful-arrays) by name:

```python
import lawful-arrays@0.1.0.0/defs.bend as A    # view, full, slot: what the laws talk about
import lawful-arrays@0.1.0.0/LAWS.bend as L    # the laws, to use in your own proofs
import lawful-arrays@0.1.0.0/PROOF.bend as P   # their proofs, needed whenever you use a law
```

Counting how often each value 0..7 occurs, in an array of 8 counters:

```python
import Base
import lawful-arrays@0.1.0.0/defs.bend as A

def bump.fin(+i: U32, an: Array<U32> & U32) -> Array<U32>:
  (a, n) = an
  Array.set(U32, a, i, (n + 1 : U32))

def bump(a: Array<U32>, +i: U32) -> Array<U32>:
  bump.fin(i, Array.get(U32, a, i))

def count(xs: List<U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case []:
      a
    case x <> rest:
      count(rest, bump(a, x))

def main() -> List<&2, U32>:
  A.view(U32, count([3, 1, 4, 1, 5, 2, 6, 5, 3, 5], Array.new(U32, 3n, 0)))
```

```
$ bend count.bend
[0, 2, 1, 2, 1, 3, 1, 0]
```

## What's in it

An array of depth `d` holds 2^d elements. Indexes wrap: index `i` reaches element `i mod 2^d`.

| operation | signature, in short | what it does |
|---|---|---|
| `Array.new` | `(T, d, v) -> Array<T>` | 2^d copies of `v` |
| `Array.size` | `(T, a) -> (a, n)` | the number of elements, 2^d, and the array back |
| `Array.get` | `(T, a, i) -> (a, x)` | element `i`, and the array back unchanged |
| `Array.set` | `(T, a, i, v) -> a` | replaces element `i` with `v`, nothing else |
| `Array.swap` | `(T, a, i, v) -> (a, old)` | writes like `set` and returns the value it replaced |
| `Array.clone` | `(T, a) -> (a, a)` | two copies of the array |
| `A.view` | `(T, a) -> List<T>` | the elements, left to right; the laws describe arrays by this list |
| `A.full` | `(T, a, d) -> Bool` | `a` has depth `d`, as every array from `Array.new` does and every operation keeps |
| `A.slot` | `(i, d) -> Nat` | the element index `i` reaches: `i mod 2^d` |

The array operations are Base's own; this package adds the laws about them. A law is a function
you call in a proof, with the law's variables as arguments. With `L` and `P` imported:

```python
# After writing v at index i, reading index i gives v.
def write_read(a: Array<U32>, i: U32, v: U32)
  -> {Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, a, i, v), i)) == v : U32}:
  L.get_set_same(U32, a, i, v)
```

The laws are proven. Below version 1.0 they have been reviewed by AI models but not yet by a human
expert. [docs/LAWS.md](docs/LAWS.md) lists them all in plain words.

## License

MIT (see `LICENSE`).

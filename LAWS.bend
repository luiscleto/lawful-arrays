import Base
import ./defs.bend as D

# lawful-arrays: what Base's Array operations do, stated on the list of an
# array's leaves (D.view). The laws are about perfect trees (D.full: depth d,
# 2^d leaves), which is what Array.new makes and every operation keeps. For
# d < 32, an index i reaches leaf i modulo 2^d (D.slot); from 32 up Base's
# Array.size wraps to 0, so the indexing laws require d < 32. Elements are Data
# (Array.get requires it, and so does D.view); only swap_full also covers
# other element types.

# ==========================================================================
# Creating
# ==========================================================================

law new_full:
  for -T: Data
  for d: Nat
  for v: T
  {D.full(T, Array.new(T, d, v), d) == True{} : Bool}

law new_view:
  for -T: Data
  for d: Nat
  for v: T
  {D.view(T, Array.new(T, d, v)) == List.replicate(T, Nat.pow(2n, d), v) : List<&2, T>}

# ==========================================================================
# Size
# ==========================================================================

law view_length:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for hf: {D.full(T, a, d) == True{} : Bool}
  {List.length(&2, T, D.view(T, a)) == Nat.pow(2n, d) : Nat}

# Array.size doubles 1 once per level of the left spine: for a perfect tree of
# depth d below 32 that is the number of leaves, 2^d.
law size_count:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.to_nat(Pair.snd(Array<T>, U32, Array.size(T, a))) == Nat.pow(2n, d) : Nat}

law size_kept:
  for -T: Data
  for a: Array<T>
  {Pair.fst(Array<T>, U32, Array.size(T, a)) == a : Array<T>}

# ==========================================================================
# Reading
# ==========================================================================

# Array.get reads leaf i (modulo the size).
law get_view:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {Some{Pair.snd(Array<T>, T, Array.get(T, a, i))} == List.get(&2, T, D.view(T, a), D.slot(i, d)) : Maybe<&2, T>}

# Array.get hands back the same array.
law get_kept:
  for -T: Data
  for a: Array<T>
  for i: U32
  {Pair.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}

# ==========================================================================
# Writing
# ==========================================================================

# Array.set replaces leaf i (modulo the size) and nothing else.
law set_view:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {D.view(T, Array.set(T, a, i, v)) == List.set(&2, T, D.view(T, a), D.slot(i, d), v) : List<&2, T>}

law set_full:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  {D.full(T, Array.set(T, a, i, v), d) == True{} : Bool}

# Reading what was just written gives it back.
# (This holds for every tree: set and get take the same path.)
law get_set_same:
  for -T: Data
  for a: Array<T>
  for i: U32
  for v: T
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}

# Writing leaf i does not change leaf j (j a different leaf modulo the size).
law get_set_other:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for j: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for hij: {Nat.is_eq(D.slot(i, d), D.slot(j, d)) == False{} : Bool}
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, a, j)) : T}

# ==========================================================================
# Swapping (Array.set is a swap that drops the old value; for elements that
# are not Data only swap_full applies)
# ==========================================================================

law swap_view:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {D.view(T, Pair.fst(Array<T>, T, Array.swap(T, a, i, v))) == List.set(&2, T, D.view(T, a), D.slot(i, d), v) : List<&2, T>}

law swap_old:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  for hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {Some{Pair.snd(Array<T>, T, Array.swap(T, a, i, v))} == List.get(&2, T, D.view(T, a), D.slot(i, d)) : Maybe<&2, T>}

law swap_full:
  for -T: Type
  for a: Array<T>
  for d: Nat
  for i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  {D.full(T, Pair.fst(Array<T>, T, Array.swap(T, a, i, v)), d) == True{} : Bool}

# ==========================================================================
# Shapes, equality and indexes
# ==========================================================================

# Two perfect trees of the same depth with the same leaves are the same array.
law view_inj:
  for -T: Data
  for a: Array<T>
  for b: Array<T>
  for d: Nat
  for ha: {D.full(T, a, d) == True{} : Bool}
  for hb: {D.full(T, b, d) == True{} : Bool}
  for h: {D.view(T, a) == D.view(T, b) : List<&2, T>}
  {a == b : Array<T>}

# Array.get as a literal pair (so code that destructures it can be rewritten).
law get_pair:
  for -T: Data
  for a: Array<T>
  for i: U32
  {Array.get(T, a, i) == (a, Pair.snd(Array<T>, T, Array.get(T, a, i))) : Array<T> & T}

law size_pair:
  for -T: Data
  for a: Array<T>
  for d: Nat
  for hf: {D.full(T, a, d) == True{} : Bool}
  {Array.size(T, a) == (a, U32.shln(1, d)) : Array<T> & U32}

# A new array reads as its initial value everywhere (every depth, every index).
law get_new:
  for -T: Data
  for d: Nat
  for v: T
  for i: U32
  {Pair.snd(Array<T>, T, Array.get(T, Array.new(T, d, v), i)) == v : T}

law slot_lt:
  for i: U32
  for d: Nat
  {Nat.is_lt(D.slot(i, d), Nat.pow(2n, d)) == True{} : Bool}

law slot_small:
  for i: U32
  for d: Nat
  for h: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  {D.slot(i, d) == U32.to_nat(i) : Nat}

# ==========================================================================
# Cloning
# ==========================================================================

# Array.clone gives two arrays equal to the original.
law clone_pair:
  for -T: Data
  for a: Array<T>
  {Array.clone(T, a) == (a, a) : Array<T> & Array<T>}

import Base
import ./defs.bend as D
import ./LAWS.bend as L
import ./proof_base.bend as B
import ./proof_tree.bend as P
import ./proof_shape.bend as S
import ./proof_index.bend as I

# Proofs of the laws: `def L.name` proves `law name` of LAWS.bend. Laws about
# an array of Data elements go through its mirror (P.mirror): a Tree<T> t with
# P.fromT(t) == a, about which the lemmas may say as much as they need (an
# array, a Type, can be used only once in a proof).

# Rewrites a fact about a into the same fact about the mirror.
def full_t(-T: Data, -a: Array<T>, -t: P.Tree<T>, +d: Nat, e: {P.fromT(T, t) == a : Array<T>},
  hf: {D.full(T, a, d) == True{} : Bool}) -> {D.full(T, P.fromT(T, t), d) == True{} : Bool}:
  B.subst(Array<T>, x => {D.full(T, x, d) == True{} : Bool}, a, P.fromT(T, t),
    Equal.sym(Array<T>, P.fromT(T, t), a, e), hf)

# Creating
# ========

def L.new_full(T, d, v):
  P.new_full(T, d, v)

def L.new_view(T, d, v):
  P.new_view(T, d, v)

# Size
# ====

def view_length.go(-T: Data, -a: Array<T>, +d: Nat, hf: {D.full(T, a, d) == True{} : Bool},
  m: P.Mirror(T, a)) -> {List.length(&2, T, D.view(T, a)) == Nat.pow(2n, d) : Nat}:
  (t, +e) = m
  %e : {List.length(&2, T, D.view(T, _)) == Nat.pow(2n, d) : Nat}
  P.view_length(T, d, t, full_t(T, a, t, d, e, hf))

def L.view_length(T, a, d, hf):
  view_length.go(T, a, d, hf, P.mirror(T, a))

def size_count.go(-T: Data, -a: Array<T>, +d: Nat, hf: {D.full(T, a, d) == True{} : Bool},
  +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, m: P.Mirror(T, a)) ->
  {U32.to_nat(Pair.snd(Array<T>, U32, Array.size(T, a))) == Nat.pow(2n, d) : Nat}:
  (t, +e) = m
  %e : {U32.to_nat(Pair.snd(Array<T>, U32, Array.size(T, _))) == Nat.pow(2n, d) : Nat}
  I.size_count_t(T, t, d, full_t(T, a, t, d, e, hf), hd)

def L.size_count(T, a, d, hf, hd):
  size_count.go(T, a, d, hf, hd, P.mirror(T, a))

def L.size_kept(T, a):
  %Equal.sym(Array<T> & U32, Array.size(T, a), (a, Pair.snd(Array<T>, U32, Array.size(T, a))), P.size_eta(T, a)) :
    {Pair.fst(Array<T>, U32, _) == a : Array<T>}
  {==}

def size_pair.go(-T: Data, -a: Array<T>, +d: Nat, hf: {D.full(T, a, d) == True{} : Bool},
  m: P.Mirror(T, a)) -> {Array.size(T, a) == (a, U32.shln(1, d)) : Array<T> & U32}:
  (t, +e) = m
  %e : {Array.size(T, _) == (_, U32.shln(1, d)) : Array<T> & U32}
  P.size_tree(T, d, t, full_t(T, a, t, d, e, hf))

def L.size_pair(T, a, d, hf):
  size_pair.go(T, a, d, hf, P.mirror(T, a))

# Reading
# =======

def get_view.go(-T: Data, -a: Array<T>, +d: Nat, +i: U32, hf: {D.full(T, a, d) == True{} : Bool},
  +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, m: P.Mirror(T, a)) ->
  {Some{Pair.snd(Array<T>, T, Array.get(T, a, i))} == List.get(&2, T, D.view(T, a), D.slot(i, d)) : Maybe<&2, T>}:
  (t, +e) = m
  %e : {Some{Pair.snd(Array<T>, T, Array.get(T, _, i))} == List.get(&2, T, D.view(T, _), D.slot(i, d)) : Maybe<&2, T>}
  I.get_view_t(T, t, d, i, full_t(T, a, t, d, e, hf), hd)

def L.get_view(T, a, d, i, hf, hd):
  get_view.go(T, a, d, i, hf, hd, P.mirror(T, a))

def get_pair.go(-T: Data, -a: Array<T>, +i: U32, m: P.Mirror(T, a)) ->
  {Array.get(T, a, i) == (a, Pair.snd(Array<T>, T, Array.get(T, a, i))) : Array<T> & T}:
  (t, e) = m
  %e : {Array.get(T, _, i) == (_, Pair.snd(Array<T>, T, Array.get(T, _, i))) : Array<T> & T}
  P.get_pair_t(T, t, i)

def L.get_pair(T, a, i):
  get_pair.go(T, a, i, P.mirror(T, a))

def get_kept.go(-T: Data, -a: Array<T>, +i: U32, m: P.Mirror(T, a)) ->
  {Pair.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}:
  (t, e) = m
  %e : {Pair.fst(Array<T>, T, Array.get(T, _, i)) == _ : Array<T>}
  Equal.cong(Array<T> & T, Array<T>, p => Pair.fst(Array<T>, T, p), Array.get(T, P.fromT(T, t), i),
    (P.fromT(T, t), Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), i))), P.get_pair_t(T, t, i))

def L.get_kept(T, a, i):
  get_kept.go(T, a, i, P.mirror(T, a))

def L.get_new(T, d, v, i):
  P.get_new_t(T, d, v, i)

# Writing
# =======

def set_view.go(-T: Data, -a: Array<T>, +d: Nat, +i: U32, +v: T, hf: {D.full(T, a, d) == True{} : Bool},
  +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, m: P.Mirror(T, a)) ->
  {D.view(T, Array.set(T, a, i, v)) == List.set(&2, T, D.view(T, a), D.slot(i, d), v) : List<&2, T>}:
  (t, +e) = m
  %e : {D.view(T, Array.set(T, _, i, v)) == List.set(&2, T, D.view(T, _), D.slot(i, d), v) : List<&2, T>}
  I.set_view_t(T, t, d, i, v, full_t(T, a, t, d, e, hf), hd)

def L.set_view(T, a, d, i, v, hf, hd):
  set_view.go(T, a, d, i, v, hf, hd, P.mirror(T, a))

def L.set_full(T, a, d, i, v, hf):
  S.set_full(T, a, d, i, v, hf)

def get_set_same.go(-T: Data, -a: Array<T>, +i: U32, +v: T, m: P.Mirror(T, a)) ->
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}:
  (t, e) = m
  %e : {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), i)) == v : T}
  P.get_set_same_t(T, t, i, v)

def L.get_set_same(T, a, i, v):
  get_set_same.go(T, a, i, v, P.mirror(T, a))

def get_set_other.go(-T: Data, -a: Array<T>, +d: Nat, +i: U32, +j: U32, +v: T,
  hf: {D.full(T, a, d) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
  +hij: {Nat.is_eq(D.slot(i, d), D.slot(j, d)) == False{} : Bool}, m: P.Mirror(T, a)) ->
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (t, +e) = m
  %e : {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, _, j)) : T}
  I.get_set_other_t(T, t, d, i, j, v, full_t(T, a, t, d, e, hf), hd, hij)

def L.get_set_other(T, a, d, i, j, v, hf, hd, hij):
  get_set_other.go(T, a, d, i, j, v, hf, hd, hij, P.mirror(T, a))

# Swapping
# ========

def swap_view.go(-T: Data, -a: Array<T>, +d: Nat, +i: U32, +v: T, hf: {D.full(T, a, d) == True{} : Bool},
  +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, m: P.Mirror(T, a)) ->
  {D.view(T, Pair.fst(Array<T>, T, Array.swap(T, a, i, v))) == List.set(&2, T, D.view(T, a), D.slot(i, d), v) : List<&2, T>}:
  (t, +e) = m
  %e : {D.view(T, Pair.fst(Array<T>, T, Array.swap(T, _, i, v))) == List.set(&2, T, D.view(T, _), D.slot(i, d), v) : List<&2, T>}
  I.swap_view_t(T, t, d, i, v, full_t(T, a, t, d, e, hf), hd)

def L.swap_view(T, a, d, i, v, hf, hd):
  swap_view.go(T, a, d, i, v, hf, hd, P.mirror(T, a))

def swap_old.go(-T: Data, -a: Array<T>, +d: Nat, +i: U32, +v: T, hf: {D.full(T, a, d) == True{} : Bool},
  +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, m: P.Mirror(T, a)) ->
  {Some{Pair.snd(Array<T>, T, Array.swap(T, a, i, v))} == List.get(&2, T, D.view(T, a), D.slot(i, d)) : Maybe<&2, T>}:
  (t, +e) = m
  %e : {Some{Pair.snd(Array<T>, T, Array.swap(T, _, i, v))} == List.get(&2, T, D.view(T, _), D.slot(i, d)) : Maybe<&2, T>}
  I.swap_old_t(T, t, d, i, v, full_t(T, a, t, d, e, hf), hd)

def L.swap_old(T, a, d, i, v, hf, hd):
  swap_old.go(T, a, d, i, v, hf, hd, P.mirror(T, a))

def L.swap_full(T, a, d, i, v, hf):
  S.swap_full(T, a, d, i, v, hf)

# Shapes, equality and indexes
# ============================

def view_inj.go(-T: Data, -a: Array<T>, -b: Array<T>, +d: Nat,
  ha: {D.full(T, a, d) == True{} : Bool}, hb: {D.full(T, b, d) == True{} : Bool},
  h: {D.view(T, a) == D.view(T, b) : List<&2, T>}, ma: P.Mirror(T, a), mb: P.Mirror(T, b)) ->
  {a == b : Array<T>}:
  (ta, +ea) = ma
  (tb, +eb) = mb
  %ea : {_ == b : Array<T>}
  %eb : {P.fromT(T, ta) == _ : Array<T>}
  +h1 = B.subst(Array<T>, x => {D.view(T, x) == D.view(T, b) : List<&2, T>}, a, P.fromT(T, ta),
    Equal.sym(Array<T>, P.fromT(T, ta), a, ea), h)
  +h2 = B.subst(Array<T>, x => {D.view(T, P.fromT(T, ta)) == D.view(T, x) : List<&2, T>}, b, P.fromT(T, tb),
    Equal.sym(Array<T>, P.fromT(T, tb), b, eb), h1)
  P.view_inj_t(T, d, ta, tb, full_t(T, a, ta, d, ea, ha), full_t(T, b, tb, d, eb, hb), h2)

def L.view_inj(T, a, b, d, ha, hb, h):
  view_inj.go(T, a, b, d, ha, hb, h, P.mirror(T, a), P.mirror(T, b))

def L.slot_lt(i, d):
  I.slot_lt_t(i, d)

def L.slot_small(i, d, h):
  I.slot_small_t(i, d, h)

# Cloning
# =======

def L.clone_pair(T, a):
  P.clone_pair(T, a)

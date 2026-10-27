import Base
import ./defs.bend as D
import ./proof_base.bend as B

# Structural lemmas about Base's Array: the shape-only laws, and the tools the
# index proofs use.
#
# An Array<T> is a Type, so a proof may use an array variable once: two lemmas
# about the same subtree (or a lemma and the induction hypothesis) cannot both
# take it. For Data elements, mirror(a) gives a Tree<T> (a Data copy of the
# shape and leaves) with fromT(t) == a; lemmas about fromT(t) may use t freely.

type Tree<-T: Data> is Data:
  TLeaf{x: T}
  TNode{l: Tree<T>, r: Tree<T>}

def fromT(-T: Data, t: Tree<T>) -> Array<T>:
  match t:
    case TLeaf{x}:
      ALeaf{x}
    case TNode{l, r}:
      ANode{fromT(T, l), fromT(T, r)}

def Mirror(-T: Data, -a: Array<T>) -> Data:
  Sigma<&2, &2, Tree<T>, t => {fromT(T, t) == a : Array<T>}>

law anode_eq:
  for -T: Type
  for -x1: Array<T>
  for -x2: Array<T>
  for -y1: Array<T>
  for -y2: Array<T>
  for e1: {x1 == y1 : Array<T>}
  for e2: {x2 == y2 : Array<T>}
  {ANode{x1, x2} == ANode{y1, y2} : Array<T>}

def anode_eq(T, x1, x2, y1, y2, e1, e2):
  %e1 : {ANode{x1, x2} == ANode{_, y2} : Array<T>}
  %e2 : {ANode{x1, x2} == ANode{x1, _} : Array<T>}
  {==}

def mirror.node(-T: Data, -xs: Array<T>, -ys: Array<T>, m1: Mirror(T, xs), m2: Mirror(T, ys))
  -> Mirror(T, ANode{xs, ys}):
  (t1, e1) = m1
  (t2, e2) = m2
  (TNode{t1, t2}, anode_eq(T, fromT(T, t1), fromT(T, t2), xs, ys, e1, e2))

def mirror(-T: Data, a: Array<T>) -> Mirror(T, a):
  match a:
    case ALeaf{x}:
      (TLeaf{x}, {==})
    case ANode{xs, ys}:
      mirror.node(T, xs, ys, mirror(T, xs), mirror(T, ys))

# Pairs returned by swap and get
# ==============================

law lo_fst:
  for -T: Type
  for -ys: Array<T>
  for r: Array<T> & T
  {Pair.fst(Array<T>, T, Array.swap.lo(T, ys, r)) == ANode{Pair.fst(Array<T>, T, r), ys} : Array<T>}

def lo_fst(T, ys, r):
  (a, x) = r
  {==}

law lo_snd:
  for -T: Type
  for -ys: Array<T>
  for r: Array<T> & T
  {Pair.snd(Array<T>, T, Array.swap.lo(T, ys, r)) == Pair.snd(Array<T>, T, r) : T}

def lo_snd(T, ys, r):
  (a, x) = r
  {==}

law hi_fst:
  for -T: Type
  for -xs: Array<T>
  for r: Array<T> & T
  {Pair.fst(Array<T>, T, Array.swap.hi(T, xs, r)) == ANode{xs, Pair.fst(Array<T>, T, r)} : Array<T>}

def hi_fst(T, xs, r):
  (a, x) = r
  {==}

law hi_snd:
  for -T: Type
  for -xs: Array<T>
  for r: Array<T> & T
  {Pair.snd(Array<T>, T, Array.swap.hi(T, xs, r)) == Pair.snd(Array<T>, T, r) : T}

def hi_snd(T, xs, r):
  (a, x) = r
  {==}

law fin_fst:
  for -T: Type
  for r: Array<T> & T
  {Array.set.fin(T, r) == Pair.fst(Array<T>, T, r) : Array<T>}

def fin_fst(T, r):
  (a, x) = r
  {==}

# Size
# ====

law size_eta:
  for -T: Type
  for a: Array<T>
  {Array.size(T, a) == (a, Pair.snd(Array<T>, U32, Array.size(T, a))) : Array<T> & U32}

def size_eta(T, a):
  match a:
    case ALeaf{x}:
      {==}
    case ANode{xs, ys}:
      %Equal.sym(Array<T> & U32, Array.size(T, xs), (xs, Pair.snd(Array<T>, U32, Array.size(T, xs))),
        size_eta(T, xs)) :
        {Array.size.node(T, ys, _) == (ANode{xs, ys}, Pair.snd(Array<T>, U32, Array.size.node(T, ys, _))) : Array<T> & U32}
      {==}

law size_tree:
  for -T: Data
  for +d: Nat
  for +t: Tree<T>
  for hf: {D.full(T, fromT(T, t), d) == True{} : Bool}
  {Array.size(T, fromT(T, t)) == (fromT(T, t), U32.shln(1, d)) : Array<T> & U32}

def size_tree(T, d, t, hf):
  match d t:
    case 0n TLeaf{x}:
      {==}
    case 0n TNode{l, r}:
      Empty.absurd({Array.size(T, fromT(T, TNode{l, r})) == (fromT(T, TNode{l, r}), 1) : Array<T> & U32},
        B.false_ne_true(hf))
    case 1n+p TLeaf{x}:
      Empty.absurd({Array.size(T, ALeaf{x}) == (ALeaf{x}, U32.shln(1, 1n+p)) : Array<T> & U32},
        B.false_ne_true(hf))
    case 1n+p TNode{l, r}:
      %Equal.sym(Array<T> & U32, Array.size(T, fromT(T, l)), (fromT(T, l), U32.shln(1, p)),
        size_tree(T, p, l, B.and_true_l(D.full(T, fromT(T, l), p), D.full(T, fromT(T, r), p), hf))) :
        {Array.size.node(T, fromT(T, r), _) == (ANode{fromT(T, l), fromT(T, r)}, U32.shln(1, 1n+p)) : Array<T> & U32}
      {==}

# Leaves
# ======

law view_length:
  for -T: Data
  for +d: Nat
  for +t: Tree<T>
  for +hf: {D.full(T, fromT(T, t), d) == True{} : Bool}
  {List.length(&2, T, D.view(T, fromT(T, t))) == Nat.pow(2n, d) : Nat}

def view_length(T, d, t, hf):
  match d t:
    case 0n TLeaf{x}:
      {==}
    case 0n TNode{l, r}:
      Empty.absurd({List.length(&2, T, D.view(T, fromT(T, TNode{l, r}))) == 1n : Nat}, B.false_ne_true(hf))
    case 1n+p TLeaf{x}:
      Empty.absurd({1n == Nat.pow(2n, 1n+p) : Nat}, B.false_ne_true(hf))
    case 1n+p TNode{l, r}:
      +VL = D.view(T, fromT(T, l))
      +VR = D.view(T, fromT(T, r))
      +P = Nat.pow(2n, p)
      %Equal.sym(Nat, List.length(&2, T, List.append(&2, T, VL, VR)),
        Nat.add(List.length(&2, T, VL), List.length(&2, T, VR)), B.length_append(T, VL, VR)) :
        {_ == Nat.pow(2n, 1n+p) : Nat}
      %Equal.sym(Nat, List.length(&2, T, VL), P,
        view_length(T, p, l, B.and_true_l(D.full(T, fromT(T, l), p), D.full(T, fromT(T, r), p), hf))) :
        {Nat.add(_, List.length(&2, T, VR)) == Nat.pow(2n, 1n+p) : Nat}
      %Equal.sym(Nat, List.length(&2, T, VR), P,
        view_length(T, p, r, B.and_true_r(D.full(T, fromT(T, l), p), D.full(T, fromT(T, r), p), hf))) :
        {Nat.add(P, _) == Nat.pow(2n, 1n+p) : Nat}
      Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.add(P, P), B.pow_succ(p))

# New arrays
# ==========

law new_full:
  for -T: Data
  for +d: Nat
  for +v: T
  {D.full(T, Array.new(T, d, v), d) == True{} : Bool}

def new_full(T, d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, D.full(T, Array.new(T, p, v), p), True{}, new_full(T, p, v)) :
        {Bool.and(_, _) == True{} : Bool}
      {==}

law new_view:
  for -T: Data
  for +d: Nat
  for +v: T
  {D.view(T, Array.new(T, d, v)) == List.replicate(T, Nat.pow(2n, d), v) : List<&2, T>}

def new_view(T, d, v):
  match d:
    case 0n:
      {==}
    case 1n+p:
      +V = D.view(T, Array.new(T, p, v))
      +P = Nat.pow(2n, p)
      %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.add(P, P), B.pow_succ(p)) :
        {List.append(&2, T, V, V) == List.replicate(T, _, v) : List<&2, T>}
      %Equal.sym(List<&2, T>, List.replicate(T, Nat.add(P, P), v),
        List.append(&2, T, List.replicate(T, P, v), List.replicate(T, P, v)), B.replicate_add(T, P, P, v)) :
        {List.append(&2, T, V, V) == _ : List<&2, T>}
      %new_view(T, p, v) :
        {List.append(&2, T, V, V) == List.append(&2, T, _, _) : List<&2, T>}
      {==}

law get_new_go:
  for -T: Data
  for +d: Nat
  for +v: T
  for +n: U32
  for +i: U32
  for +z: Bool
  {Pair.snd(Array<T>, T, Array.get.go(T, Array.new(T, d, v), n, i, z)) == v : T}

def get_new_go(T, d, v, n, i, z):
  match d z:
    case 0n _:
      {==}
    case 1n+p True{}:
      +h = U32.shr(n)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.lo(T, Array.new(T, p, v), Array.get.go(T, Array.new(T, p, v), h, i, U32.is_lt(i, U32.shr(h))))), Pair.snd(Array<T>, T, Array.get.go(T, Array.new(T, p, v), h, i, U32.is_lt(i, U32.shr(h)))),
        lo_snd(T, Array.new(T, p, v), Array.get.go(T, Array.new(T, p, v), h, i, U32.is_lt(i, U32.shr(h))))) : {_ == v : T}
      get_new_go(T, p, v, h, i, U32.is_lt(i, U32.shr(h)))
    case 1n+p False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.hi(T, Array.new(T, p, v), Array.get.go(T, Array.new(T, p, v), h, j, U32.is_lt(j, U32.shr(h))))), Pair.snd(Array<T>, T, Array.get.go(T, Array.new(T, p, v), h, j, U32.is_lt(j, U32.shr(h)))),
        hi_snd(T, Array.new(T, p, v), Array.get.go(T, Array.new(T, p, v), h, j, U32.is_lt(j, U32.shr(h))))) : {_ == v : T}
      get_new_go(T, p, v, h, j, U32.is_lt(j, U32.shr(h)))

# Cloning
# =======

law clone_pair:
  for -T: Data
  for a: Array<T>
  {Array.clone(T, a) == (a, a) : Array<T> & Array<T>}

def clone_pair(T, a):
  match a:
    case ALeaf{x}:
      {==}
    case ANode{xs, ys}:
      %Equal.sym(Array<T> & Array<T>, Array.clone(T, xs), (xs, xs), clone_pair(T, xs)) :
        {Array.clone.node(T, _, Array.clone(T, ys)) == (ANode{xs, ys}, ANode{xs, ys}) : Array<T> & Array<T>}
      %Equal.sym(Array<T> & Array<T>, Array.clone(T, ys), (ys, ys), clone_pair(T, ys)) :
        {Array.clone.node(T, (xs, xs), _) == (ANode{xs, ys}, ANode{xs, ys}) : Array<T> & Array<T>}
      {==}

# Reading hands the array back
# ============================

law get_go_eta:
  for -T: Data
  for a: Array<T>
  for +n: U32
  for +i: U32
  for +z: Bool
  {Array.get.go(T, a, n, i, z) == (a, Pair.snd(Array<T>, T, Array.get.go(T, a, n, i, z))) : Array<T> & T}

def get_go_eta(T, a, n, i, z):
  match a z:
    case ALeaf{x} _:
      {==}
    case ANode{xs, ys} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.get.go(T, xs, h, i, z2),
        (xs, Pair.snd(Array<T>, T, Array.get.go(T, xs, h, i, z2))), get_go_eta(T, xs, h, i, z2)) :
        {Array.swap.lo(T, ys, _) == (ANode{xs, ys}, Pair.snd(Array<T>, T, Array.swap.lo(T, ys, _))) : Array<T> & T}
      {==}
    case ANode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.get.go(T, ys, h, j, z2),
        (ys, Pair.snd(Array<T>, T, Array.get.go(T, ys, h, j, z2))), get_go_eta(T, ys, h, j, z2)) :
        {Array.swap.hi(T, xs, _) == (ANode{xs, ys}, Pair.snd(Array<T>, T, Array.swap.hi(T, xs, _))) : Array<T> & T}
      {==}

law get_pair_t:
  for -T: Data
  for +t: Tree<T>
  for +i: U32
  {Array.get(T, fromT(T, t), i) == (fromT(T, t), Pair.snd(Array<T>, T, Array.get(T, fromT(T, t), i))) : Array<T> & T}

def get_pair_t(T, t, i):
  %Equal.sym(Array<T> & U32, Array.size(T, fromT(T, t)), (fromT(T, t), Pair.snd(Array<T>, U32, Array.size(T, fromT(T, t)))), size_eta(T, fromT(T, t))) :
    {Array.get.at(T, i, _) == (fromT(T, t), Pair.snd(Array<T>, T, Array.get.at(T, i, _))) : Array<T> & T}
  +n = Pair.snd(Array<T>, U32, Array.size(T, fromT(T, t)))
  +j = U32.and(i, U32.sub(n, 1))
  get_go_eta(T, fromT(T, t), n, j, U32.is_lt(j, U32.shr(n)))

# Writing then reading the same index
# ===================================

# A swap keeps the left spine, so the size.
law sz_sw:
  for -T: Data
  for +t: Tree<T>
  for +n: U32
  for +i: U32
  for +v: T
  for +z: Bool
  {Array.size(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, i, v, z)))
    == (Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, i, v, z)),
        Pair.snd(Array<T>, U32, Array.size(T, fromT(T, t)))) : Array<T> & U32}

def sz_sw(T, t, n, i, v, z):
  match t z:
    case TLeaf{x} _:
      {==}
    case TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.lo(T, fromT(T, r), Array.swap.go(T, fromT(T, l), h, i, v, z2))),
        ANode{Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), fromT(T, r)},
        lo_fst(T, fromT(T, r), Array.swap.go(T, fromT(T, l), h, i, v, z2))) :
        {Array.size(T, _) == (_, Pair.snd(Array<T>, U32, Array.size(T, ANode{fromT(T, l), fromT(T, r)}))) : Array<T> & U32}
      %Equal.sym(Array<T> & U32, Array.size(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2))),
        (Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), Pair.snd(Array<T>, U32, Array.size(T, fromT(T, l)))),
        sz_sw(T, l, h, i, v, z2)) :
        {Array.size.node(T, fromT(T, r), _)
          == (ANode{Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), fromT(T, r)},
              Pair.snd(Array<T>, U32, Array.size.node(T, fromT(T, r), Array.size(T, fromT(T, l))))) : Array<T> & U32}
      %Equal.sym(Array<T> & U32, Array.size(T, fromT(T, l)), (fromT(T, l), Pair.snd(Array<T>, U32, Array.size(T, fromT(T, l)))),
        size_eta(T, fromT(T, l))) :
        {(ANode{Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), fromT(T, r)},
          U32.shl(Pair.snd(Array<T>, U32, Array.size(T, fromT(T, l)))))
          == (ANode{Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), fromT(T, r)},
              Pair.snd(Array<T>, U32, Array.size.node(T, fromT(T, r), _))) : Array<T> & U32}
      {==}
    case TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.hi(T, fromT(T, l), Array.swap.go(T, fromT(T, r), h, j, v, z2))),
        ANode{fromT(T, l), Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2))},
        hi_fst(T, fromT(T, l), Array.swap.go(T, fromT(T, r), h, j, v, z2))) :
        {Array.size(T, _) == (_, Pair.snd(Array<T>, U32, Array.size(T, ANode{fromT(T, l), fromT(T, r)}))) : Array<T> & U32}
      %Equal.sym(Array<T> & U32, Array.size(T, fromT(T, l)), (fromT(T, l), Pair.snd(Array<T>, U32, Array.size(T, fromT(T, l)))),
        size_eta(T, fromT(T, l))) :
        {Array.size.node(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2)), _)
          == (ANode{fromT(T, l), Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2))},
              Pair.snd(Array<T>, U32, Array.size.node(T, fromT(T, r), _))) : Array<T> & U32}
      {==}

# Reading where a swap wrote gives the written value (any tree).
law gss:
  for -T: Data
  for +t: Tree<T>
  for +n: U32
  for +i: U32
  for +v: T
  for +z: Bool
  {Pair.snd(Array<T>, T, Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, i, v, z)), n, i, z)) == v : T}

def gss(T, t, n, i, v, z):
  match t z:
    case TLeaf{x} _:
      {==}
    case TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.lo(T, fromT(T, r), Array.swap.go(T, fromT(T, l), h, i, v, z2))),
        ANode{Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), fromT(T, r)},
        lo_fst(T, fromT(T, r), Array.swap.go(T, fromT(T, l), h, i, v, z2))) :
        {Pair.snd(Array<T>, T, Array.get.go(T, _, n, i, True{})) == v : T}
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.lo(T, fromT(T, r),
          Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), h, i, z2))),
        Pair.snd(Array<T>, T, Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), h, i, z2)),
        lo_snd(T, fromT(T, r), Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, l), h, i, v, z2)), h, i, z2))) :
        {_ == v : T}
      gss(T, l, h, i, v, z2)
    case TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.hi(T, fromT(T, l), Array.swap.go(T, fromT(T, r), h, j, v, z2))),
        ANode{fromT(T, l), Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2))},
        hi_fst(T, fromT(T, l), Array.swap.go(T, fromT(T, r), h, j, v, z2))) :
        {Pair.snd(Array<T>, T, Array.get.go(T, _, n, i, False{})) == v : T}
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.hi(T, fromT(T, l),
          Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2)), h, j, z2))),
        Pair.snd(Array<T>, T, Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2)), h, j, z2)),
        hi_snd(T, fromT(T, l), Array.get.go(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, r), h, j, v, z2)), h, j, z2))) :
        {_ == v : T}
      gss(T, r, h, j, v, z2)

law get_set_same_t:
  for -T: Data
  for +t: Tree<T>
  for +i: U32
  for +v: T
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, fromT(T, t), i, v), i)) == v : T}

def get_set_same_t(T, t, i, v):
  +n = Pair.snd(Array<T>, U32, Array.size(T, fromT(T, t)))
  +j = U32.and(i, U32.sub(n, 1))
  +z = U32.is_lt(j, U32.shr(n))
  %Equal.sym(Array<T> & U32, Array.size(T, fromT(T, t)), (fromT(T, t), n), size_eta(T, fromT(T, t))) :
    {Pair.snd(Array<T>, T, Array.get(T, Array.set.fin(T, Array.swap.at(T, i, v, _)), i)) == v : T}
  %Equal.sym(Array<T>, Array.set.fin(T, Array.swap.go(T, fromT(T, t), n, j, v, z)),
    Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, j, v, z)),
    fin_fst(T, Array.swap.go(T, fromT(T, t), n, j, v, z))) :
    {Pair.snd(Array<T>, T, Array.get(T, _, i)) == v : T}
  %Equal.sym(Array<T> & U32, Array.size(T, Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, j, v, z))),
    (Pair.fst(Array<T>, T, Array.swap.go(T, fromT(T, t), n, j, v, z)), n), sz_sw(T, t, n, j, v, z)) :
    {Pair.snd(Array<T>, T, Array.get.at(T, i, _)) == v : T}
  gss(T, t, n, j, v, z)

# Perfect trees with the same leaves are equal
# ============================================

law view_inj_t:
  for -T: Data
  for +d: Nat
  for +ta: Tree<T>
  for +tb: Tree<T>
  for +ha: {D.full(T, fromT(T, ta), d) == True{} : Bool}
  for +hb: {D.full(T, fromT(T, tb), d) == True{} : Bool}
  for +he: {D.view(T, fromT(T, ta)) == D.view(T, fromT(T, tb)) : List<&2, T>}
  {fromT(T, ta) == fromT(T, tb) : Array<T>}

def view_inj_t(T, d, ta, tb, ha, hb, he):
  match d ta tb:
    case 0n TLeaf{x} TLeaf{y}:
      %B.cons_inj_h(T, x, y, Nil{}, Nil{}, he) : {ALeaf{x} == ALeaf{_} : Array<T>}
      {==}
    case 0n TLeaf{x} TNode{lb, rb}:
      Empty.absurd({ALeaf{x} == ANode{fromT(T, lb), fromT(T, rb)} : Array<T>}, B.false_ne_true(hb))
    case 0n TNode{la, ra} _:
      Empty.absurd({ANode{fromT(T, la), fromT(T, ra)} == fromT(T, tb) : Array<T>}, B.false_ne_true(ha))
    case 1n+p TLeaf{x} _:
      Empty.absurd({ALeaf{x} == fromT(T, tb) : Array<T>}, B.false_ne_true(ha))
    case 1n+p TNode{la, ra} TLeaf{y}:
      Empty.absurd({ANode{fromT(T, la), fromT(T, ra)} == ALeaf{y} : Array<T>}, B.false_ne_true(hb))
    case 1n+p TNode{la, ra} TNode{lb, rb}:
      +VLa = D.view(T, fromT(T, la))
      +VRa = D.view(T, fromT(T, ra))
      +VLb = D.view(T, fromT(T, lb))
      +VRb = D.view(T, fromT(T, rb))
      +hla = B.and_true_l(D.full(T, fromT(T, la), p), D.full(T, fromT(T, ra), p), ha)
      +hra = B.and_true_r(D.full(T, fromT(T, la), p), D.full(T, fromT(T, ra), p), ha)
      +hlb = B.and_true_l(D.full(T, fromT(T, lb), p), D.full(T, fromT(T, rb), p), hb)
      +hrb = B.and_true_r(D.full(T, fromT(T, lb), p), D.full(T, fromT(T, rb), p), hb)
      +hl = Equal.trans(Nat, List.length(&2, T, VLa), Nat.pow(2n, p), List.length(&2, T, VLb),
        view_length(T, p, la, hla), Equal.sym(Nat, List.length(&2, T, VLb), Nat.pow(2n, p), view_length(T, p, lb, hlb)))
      +ll = B.append_inj_l(T, VLa, VLb, VRa, VRb, hl, he)
      +he2 = B.subst(List<&2, T>, X => {List.append(&2, T, VLa, VRa) == List.append(&2, T, X, VRb) : List<&2, T>},
        VLb, VLa, Equal.sym(List<&2, T>, VLa, VLb, ll), he)
      +rr = B.append_cancel_l(T, VLa, VRa, VRb, he2)
      anode_eq(T, fromT(T, la), fromT(T, ra), fromT(T, lb), fromT(T, rb),
        view_inj_t(T, p, la, lb, hla, hlb, ll), view_inj_t(T, p, ra, rb, hra, hrb, rr))

law get_new_t:
  for -T: Data
  for +d: Nat
  for +v: T
  for +i: U32
  {Pair.snd(Array<T>, T, Array.get(T, Array.new(T, d, v), i)) == v : T}

def get_new_t(T, d, v, i):
  +n = Pair.snd(Array<T>, U32, Array.size(T, Array.new(T, d, v)))
  +j = U32.and(i, U32.sub(n, 1))
  %Equal.sym(Array<T> & U32, Array.size(T, Array.new(T, d, v)), (Array.new(T, d, v), n),
    size_eta(T, Array.new(T, d, v))) :
    {Pair.snd(Array<T>, T, Array.get.at(T, i, _)) == v : T}
  get_new_go(T, d, v, n, j, U32.is_lt(j, U32.shr(n)))

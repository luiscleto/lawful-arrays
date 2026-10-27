import Base
import ./defs.bend as D
import ./proof_base.bend as B
import ./proof_tree.bend as P
import ./proof_shape.bend as S
import ./proof_words.bend as W

# The indexing laws. At a node of a perfect tree of depth 1+p, Array.get.go
# holds n = 2^(1+p) and an index i below it; h = n >> 1 = 2^p, and z says
# i < h: then i goes left unchanged, else right as i - h. So the leaf reached
# is leaf i of the list of leaves, and the top level passes i & (n - 1), which
# is i modulo 2^d.

# One step down
# =============

law n_half:
  for +p: Nat
  {Nat.div(Nat.pow(2n, 1n+p), 2n) == Nat.pow(2n, p) : Nat}

def n_half(p):
  +P = Nat.pow(2n, p)
  %Equal.sym(Nat, Nat.mul(2n, P), Nat.mul(P, 2n), W.n_mul_comm(2n, P)) : {Nat.div(_, 2n) == P : Nat}
  %B.add_zero(Nat.mul(P, 2n)) : {Nat.div(_, 2n) == P : Nat}
  W.n_div_mul_add(P, 2n, 0n, {==})

law half:
  for +n: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  {U32.to_nat(U32.shr(n)) == Nat.pow(2n, p) : Nat}

def half(n, p, hn):
  %Equal.sym(Nat, U32.to_nat(U32.shr(n)), Nat.div(U32.to_nat(n), 2n), W.w_shr(n)) :
    {_ == Nat.pow(2n, p) : Nat}
  %Equal.sym(Nat, U32.to_nat(n), Nat.pow(2n, 1n+p), hn) :
    {Nat.div(_, 2n) == Nat.pow(2n, p) : Nat}
  n_half(p)

law lo_idx:
  for +n: U32
  for +i: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  for +hz: {U32.is_lt(i, U32.shr(n)) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, p)) == True{} : Bool}

def lo_idx(n, i, p, hn, hz):
  %half(n, p, hn) : {Nat.is_lt(U32.to_nat(i), _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), U32.to_nat(U32.shr(n))), U32.is_lt(i, U32.shr(n)), True{},
    Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), Nat.is_lt(U32.to_nat(i), U32.to_nat(U32.shr(n))), W.w_lt(i, U32.shr(n))), hz)

law hi_nlt:
  for +n: U32
  for +i: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  for +hz: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, p)) == False{} : Bool}

def hi_nlt(n, i, p, hn, hz):
  %half(n, p, hn) : {Nat.is_lt(U32.to_nat(i), _) == False{} : Bool}
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), U32.to_nat(U32.shr(n))), U32.is_lt(i, U32.shr(n)), False{},
    Equal.sym(Bool, U32.is_lt(i, U32.shr(n)), Nat.is_lt(U32.to_nat(i), U32.to_nat(U32.shr(n))), W.w_lt(i, U32.shr(n))), hz)

law le_shr:
  for +n: U32
  for +i: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  for +hz: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}
  {U32.is_le(U32.shr(n), i) == True{} : Bool}

def le_shr(n, i, p, hn, hz):
  %Equal.sym(Bool, U32.is_le(U32.shr(n), i), Nat.is_le(U32.to_nat(U32.shr(n)), U32.to_nat(i)), W.w_le(U32.shr(n), i)) :
    {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.shr(n)), Nat.pow(2n, p), half(n, p, hn)) :
    {Nat.is_le(_, U32.to_nat(i)) == True{} : Bool}
  B.not_lt_le(U32.to_nat(i), Nat.pow(2n, p), hi_nlt(n, i, p, hn, hz))

law hi_sub:
  for +n: U32
  for +i: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  for +hz: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}
  {U32.to_nat(U32.sub(i, U32.shr(n))) == Nat.sub(U32.to_nat(i), Nat.pow(2n, p)) : Nat}

def hi_sub(n, i, p, hn, hz):
  %Equal.sym(Nat, U32.to_nat(U32.sub(i, U32.shr(n))), Nat.sub(U32.to_nat(i), U32.to_nat(U32.shr(n))),
    W.w_sub_le(i, U32.shr(n), le_shr(n, i, p, hn, hz))) :
    {_ == Nat.sub(U32.to_nat(i), Nat.pow(2n, p)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.shr(n)), Nat.pow(2n, p), half(n, p, hn)) :
    {Nat.sub(U32.to_nat(i), _) == Nat.sub(U32.to_nat(i), Nat.pow(2n, p)) : Nat}
  {==}

law hi_idx:
  for +n: U32
  for +i: U32
  for +p: Nat
  for +hn: {U32.to_nat(n) == Nat.pow(2n, 1n+p) : Nat}
  for +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, 1n+p)) == True{} : Bool}
  for +hz: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}
  {Nat.is_lt(U32.to_nat(U32.sub(i, U32.shr(n))), Nat.pow(2n, p)) == True{} : Bool}

def hi_idx(n, i, p, hn, hi, hz):
  %Equal.sym(Nat, U32.to_nat(U32.sub(i, U32.shr(n))), Nat.sub(U32.to_nat(i), Nat.pow(2n, p)), hi_sub(n, i, p, hn, hz)) :
    {Nat.is_lt(_, Nat.pow(2n, p)) == True{} : Bool}
  B.lt_sub(Nat.pow(2n, p), U32.to_nat(i), Nat.pow(2n, p), hi_nlt(n, i, p, hn, hz),
    B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == True{} : Bool}, Nat.pow(2n, 1n+p),
      Nat.add(Nat.pow(2n, p), Nat.pow(2n, p)), B.pow_succ(p), hi))

# Down the tree
# =============

law gg:
  for -T: Data
  for +d: Nat
  for +t: P.Tree<T>
  for +n: U32
  for +i: U32
  for +z: Bool
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hn: {U32.to_nat(n) == Nat.pow(2n, d) : Nat}
  for +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  for +hz: {U32.is_lt(i, U32.shr(n)) == z : Bool}
  {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, t), n, i, z))}
    == List.get(&2, T, D.view(T, P.fromT(T, t)), U32.to_nat(i)) : Maybe<&2, T>}

def gg(T, d, t, n, i, z, hf, hn, hi, hz):
  match d t z:
    case 0n P.TLeaf{x} _:
      %Equal.sym(Nat, U32.to_nat(i), 0n, B.lt_one(U32.to_nat(i), hi)) :
        {Some{x} == List.get(&2, T, [x], _) : Maybe<&2, T>}
      {==}
    case 0n P.TNode{l, r} _:
      Empty.absurd({Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, P.TNode{l, r}), n, i, z))}
        == List.get(&2, T, D.view(T, P.fromT(T, P.TNode{l, r})), U32.to_nat(i)) : Maybe<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TLeaf{x} _:
      Empty.absurd({Some{x} == List.get(&2, T, [x], U32.to_nat(i)) : Maybe<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +lt = lo_idx(n, i, p, hn, hz)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.lo(T, P.fromT(T, r), Array.get.go(T, P.fromT(T, l), h, i, z2))),
        Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, l), h, i, z2)),
        P.lo_snd(T, P.fromT(T, r), Array.get.go(T, P.fromT(T, l), h, i, z2))) :
        {Some{_} == List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)) : Maybe<&2, T>}
      %Equal.sym(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)), List.get(&2, T, VL, U32.to_nat(i)),
        B.get_append_l(T, VL, VR, U32.to_nat(i),
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == True{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), lt))) :
        {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, l), h, i, z2))} == _ : Maybe<&2, T>}
      gg(T, p, l, h, i, z2, hfl, half(n, p, hn), lt, {==})
    case 1n+p P.TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +hfr = B.and_true_r(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.hi(T, P.fromT(T, l), Array.get.go(T, P.fromT(T, r), h, j, z2))),
        Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, r), h, j, z2)),
        P.hi_snd(T, P.fromT(T, l), Array.get.go(T, P.fromT(T, r), h, j, z2))) :
        {Some{_} == List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)) : Maybe<&2, T>}
      %Equal.sym(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)),
        List.get(&2, T, VR, Nat.sub(U32.to_nat(i), List.length(&2, T, VL))),
        B.get_append_r(T, VL, VR, U32.to_nat(i),
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == False{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), hi_nlt(n, i, p, hn, hz)))) :
        {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, r), h, j, z2))} == _ : Maybe<&2, T>}
      %Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)) :
        {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, r), h, j, z2))}
          == List.get(&2, T, VR, Nat.sub(U32.to_nat(i), _)) : Maybe<&2, T>}
      %hi_sub(n, i, p, hn, hz) :
        {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, r), h, j, z2))} == List.get(&2, T, VR, _) : Maybe<&2, T>}
      gg(T, p, r, h, j, z2, hfr, half(n, p, hn), hi_idx(n, i, p, hn, hi, hz), {==})

# What a swap hands back is the leaf it replaced.
law gso:
  for -T: Data
  for +d: Nat
  for +t: P.Tree<T>
  for +n: U32
  for +i: U32
  for +v: T
  for +z: Bool
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hn: {U32.to_nat(n) == Nat.pow(2n, d) : Nat}
  for +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  for +hz: {U32.is_lt(i, U32.shr(n)) == z : Bool}
  {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, t), n, i, v, z))}
    == List.get(&2, T, D.view(T, P.fromT(T, t)), U32.to_nat(i)) : Maybe<&2, T>}

def gso(T, d, t, n, i, v, z, hf, hn, hi, hz):
  match d t z:
    case 0n P.TLeaf{x} _:
      %Equal.sym(Nat, U32.to_nat(i), 0n, B.lt_one(U32.to_nat(i), hi)) :
        {Some{x} == List.get(&2, T, [x], _) : Maybe<&2, T>}
      {==}
    case 0n P.TNode{l, r} _:
      Empty.absurd({Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, P.TNode{l, r}), n, i, v, z))}
        == List.get(&2, T, D.view(T, P.fromT(T, P.TNode{l, r})), U32.to_nat(i)) : Maybe<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TLeaf{x} _:
      Empty.absurd({Some{x} == List.get(&2, T, [x], U32.to_nat(i)) : Maybe<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +lt = lo_idx(n, i, p, hn, hz)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.lo(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))),
        Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2)),
        P.lo_snd(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))) :
        {Some{_} == List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)) : Maybe<&2, T>}
      %Equal.sym(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)), List.get(&2, T, VL, U32.to_nat(i)),
        B.get_append_l(T, VL, VR, U32.to_nat(i),
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == True{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), lt))) :
        {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2))} == _ : Maybe<&2, T>}
      gso(T, p, l, h, i, v, z2, hfl, half(n, p, hn), lt, {==})
    case 1n+p P.TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +hfr = B.and_true_r(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      %Equal.sym(T, Pair.snd(Array<T>, T, Array.swap.hi(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))),
        Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2)),
        P.hi_snd(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))) :
        {Some{_} == List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)) : Maybe<&2, T>}
      %Equal.sym(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i)),
        List.get(&2, T, VR, Nat.sub(U32.to_nat(i), List.length(&2, T, VL))),
        B.get_append_r(T, VL, VR, U32.to_nat(i),
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == False{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), hi_nlt(n, i, p, hn, hz)))) :
        {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))} == _ : Maybe<&2, T>}
      %Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)) :
        {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))}
          == List.get(&2, T, VR, Nat.sub(U32.to_nat(i), _)) : Maybe<&2, T>}
      %hi_sub(n, i, p, hn, hz) :
        {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))} == List.get(&2, T, VR, _) : Maybe<&2, T>}
      gso(T, p, r, h, j, v, z2, hfr, half(n, p, hn), hi_idx(n, i, p, hn, hi, hz), {==})

# A swap writes leaf i of the list of leaves.
law gsv:
  for -T: Data
  for +d: Nat
  for +t: P.Tree<T>
  for +n: U32
  for +i: U32
  for +v: T
  for +z: Bool
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hn: {U32.to_nat(n) == Nat.pow(2n, d) : Nat}
  for +hi: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  for +hz: {U32.is_lt(i, U32.shr(n)) == z : Bool}
  {D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), n, i, v, z)))
    == List.set(&2, T, D.view(T, P.fromT(T, t)), U32.to_nat(i), v) : List<&2, T>}

def gsv(T, d, t, n, i, v, z, hf, hn, hi, hz):
  match d t z:
    case 0n P.TLeaf{x} _:
      %Equal.sym(Nat, U32.to_nat(i), 0n, B.lt_one(U32.to_nat(i), hi)) :
        {[v] == List.set(&2, T, [x], _, v) : List<&2, T>}
      {==}
    case 0n P.TNode{l, r} _:
      Empty.absurd({D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, P.TNode{l, r}), n, i, v, z)))
        == List.set(&2, T, D.view(T, P.fromT(T, P.TNode{l, r})), U32.to_nat(i), v) : List<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TLeaf{x} _:
      Empty.absurd({[v] == List.set(&2, T, [x], U32.to_nat(i), v) : List<&2, T>}, B.false_ne_true(hf))
    case 1n+p P.TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +lt = lo_idx(n, i, p, hn, hz)
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.lo(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))),
        ANode{Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2)), P.fromT(T, r)},
        P.lo_fst(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))) :
        {D.view(T, _) == List.set(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i), v) : List<&2, T>}
      %Equal.sym(List<&2, T>, List.set(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i), v),
        List.append(&2, T, List.set(&2, T, VL, U32.to_nat(i), v), VR),
        B.set_append_l(T, VL, VR, U32.to_nat(i), v,
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == True{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), lt))) :
        {List.append(&2, T, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2))), VR) == _ : List<&2, T>}
      %gsv(T, p, l, h, i, v, z2, hfl, half(n, p, hn), lt, {==}) :
        {List.append(&2, T, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2))), VR)
          == List.append(&2, T, _, VR) : List<&2, T>}
      {==}
    case 1n+p P.TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      +VL = D.view(T, P.fromT(T, l))
      +VR = D.view(T, P.fromT(T, r))
      +hfl = B.and_true_l(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      +hfr = B.and_true_r(D.full(T, P.fromT(T, l), p), D.full(T, P.fromT(T, r), p), hf)
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.hi(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))),
        ANode{P.fromT(T, l), Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))},
        P.hi_fst(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))) :
        {D.view(T, _) == List.set(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i), v) : List<&2, T>}
      %Equal.sym(List<&2, T>, List.set(&2, T, List.append(&2, T, VL, VR), U32.to_nat(i), v),
        List.append(&2, T, VL, List.set(&2, T, VR, Nat.sub(U32.to_nat(i), List.length(&2, T, VL)), v)),
        B.set_append_r(T, VL, VR, U32.to_nat(i), v,
          B.subst(Nat, X => {Nat.is_lt(U32.to_nat(i), X) == False{} : Bool}, Nat.pow(2n, p), List.length(&2, T, VL),
            Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)), hi_nlt(n, i, p, hn, hz)))) :
        {List.append(&2, T, VL, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2)))) == _ : List<&2, T>}
      %Equal.sym(Nat, List.length(&2, T, VL), Nat.pow(2n, p), P.view_length(T, p, l, hfl)) :
        {List.append(&2, T, VL, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))))
          == List.append(&2, T, VL, List.set(&2, T, VR, Nat.sub(U32.to_nat(i), _), v)) : List<&2, T>}
      %hi_sub(n, i, p, hn, hz) :
        {List.append(&2, T, VL, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))))
          == List.append(&2, T, VL, List.set(&2, T, VR, _, v)) : List<&2, T>}
      %gsv(T, p, r, h, j, v, z2, hfr, half(n, p, hn), hi_idx(n, i, p, hn, hi, hz), {==}) :
        {List.append(&2, T, VL, D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))))
          == List.append(&2, T, VL, _) : List<&2, T>}
      {==}

# The top level: size 2^d and index i & (2^d - 1)
# ===============================================

law one_mul:
  for +x: Nat
  {Nat.mul(U32.to_nat(1), x) == x : Nat}

def one_mul(x):
  B.add_zero(x)

law size_n:
  for +d: Nat
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.to_nat(U32.shln(1, d)) == Nat.pow(2n, d) : Nat}

def size_n(d, hd):
  +fits = B.subst(Nat, X => {Nat.is_lt(X, Nat.pow(2n, 32n)) == True{} : Bool},
    Nat.pow(2n, d), Nat.mul(U32.to_nat(1), Nat.pow(2n, d)),
    Equal.sym(Nat, Nat.mul(U32.to_nat(1), Nat.pow(2n, d)), Nat.pow(2n, d), one_mul(Nat.pow(2n, d))),
    B.pow_lt(d, 32n, hd))
  %Equal.sym(Nat, U32.to_nat(U32.shln(1, d)), Nat.mul(U32.to_nat(1), Nat.pow(2n, d)), W.w_shln_fits(1, d, fits)) :
    {_ == Nat.pow(2n, d) : Nat}
  one_mul(Nat.pow(2n, d))

law le0:
  for +y: Nat
  {Nat.is_le(0n, y) == True{} : Bool}

def le0(y):
  match y:
    case 0n:
      {==}
    case 1n+k:
      {==}

law le1_pow:
  for +d: Nat
  {Nat.is_le(1n, Nat.pow(2n, d)) == True{} : Bool}

def le1_pow.go(+x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_le(1n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, B.false_ne_true(h))
    case 1n+y:
      le0(y)

def le1_pow(d):
  le1_pow.go(Nat.pow(2n, d), B.pow_pos(d))

law le1:
  for +d: Nat
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.is_le(1, U32.shln(1, d)) == True{} : Bool}

def le1(d, hd):
  +S = U32.shln(1, d)
  %Equal.sym(Bool, U32.is_le(1, S), Nat.is_le(U32.to_nat(1), U32.to_nat(S)), W.w_le(1, S)) :
    {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(S), Nat.pow(2n, d), size_n(d, hd)) :
    {Nat.is_le(U32.to_nat(1), _) == True{} : Bool}
  le1_pow(d)

law mask_n:
  for +d: Nat
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.to_nat(U32.sub(U32.shln(1, d), 1)) == Nat.sub(Nat.pow(2n, d), 1n) : Nat}

def mask_n(d, hd):
  +S = U32.shln(1, d)
  %Equal.sym(Nat, U32.to_nat(U32.sub(S, 1)), Nat.sub(U32.to_nat(S), U32.to_nat(1)), W.w_sub_le(S, 1, le1(d, hd))) :
    {_ == Nat.sub(Nat.pow(2n, d), 1n) : Nat}
  %Equal.sym(Nat, U32.to_nat(S), Nat.pow(2n, d), size_n(d, hd)) :
    {Nat.sub(_, U32.to_nat(1)) == Nat.sub(Nat.pow(2n, d), 1n) : Nat}
  {==}

law slot_n:
  for +i: U32
  for +d: Nat
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1))) == D.slot(i, d) : Nat}

def slot_n(i, d, hd):
  W.w_and_mask(i, U32.sub(U32.shln(1, d), 1), d, mask_n(d, hd))

law slot_lt_t:
  for +i: U32
  for +d: Nat
  {Nat.is_lt(D.slot(i, d), Nat.pow(2n, d)) == True{} : Bool}

def slot_lt_t(i, d):
  W.n_mod_lt(U32.to_nat(i), Nat.pow(2n, d), B.pow_pos(d))

law slot_small_t:
  for +i: U32
  for +d: Nat
  for +h: {Nat.is_lt(U32.to_nat(i), Nat.pow(2n, d)) == True{} : Bool}
  {D.slot(i, d) == U32.to_nat(i) : Nat}

def slot_small_t(i, d, h):
  W.n_mod_small(U32.to_nat(i), Nat.pow(2n, d), h)

law jlt:
  for +i: U32
  for +d: Nat
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1))), Nat.pow(2n, d)) == True{} : Bool}

def jlt(i, d, hd):
  B.subst(Nat, X => {Nat.is_lt(X, Nat.pow(2n, d)) == True{} : Bool}, D.slot(i, d),
    U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1))),
    Equal.sym(Nat, U32.to_nat(U32.and(i, U32.sub(U32.shln(1, d), 1))), D.slot(i, d), slot_n(i, d, hd)),
    slot_lt_t(i, d))

# The laws, for a mirrored array
# ==============================

law size_count_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {U32.to_nat(Pair.snd(Array<T>, U32, Array.size(T, P.fromT(T, t)))) == Nat.pow(2n, d) : Nat}

def size_count_t(T, t, d, hf, hd):
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), U32.shln(1, d)), P.size_tree(T, d, t, hf)) :
    {U32.to_nat(Pair.snd(Array<T>, U32, _)) == Nat.pow(2n, d) : Nat}
  size_n(d, hd)

law get_view_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +i: U32
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), i))}
    == List.get(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d)) : Maybe<&2, T>}

def get_view_t(T, t, d, i, hf, hd):
  +S = U32.shln(1, d)
  +j = U32.and(i, U32.sub(S, 1))
  +z = U32.is_lt(j, U32.shr(S))
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), S), P.size_tree(T, d, t, hf)) :
    {Some{Pair.snd(Array<T>, T, Array.get.at(T, i, _))} == List.get(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d)) : Maybe<&2, T>}
  %slot_n(i, d, hd) :
    {Some{Pair.snd(Array<T>, T, Array.get.go(T, P.fromT(T, t), S, j, z))} == List.get(&2, T, D.view(T, P.fromT(T, t)), _) : Maybe<&2, T>}
  gg(T, d, t, S, j, z, hf, size_n(d, hd), jlt(i, d, hd), {==})

law swap_old_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +i: U32
  for +v: T
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {Some{Pair.snd(Array<T>, T, Array.swap(T, P.fromT(T, t), i, v))}
    == List.get(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d)) : Maybe<&2, T>}

def swap_old_t(T, t, d, i, v, hf, hd):
  +S = U32.shln(1, d)
  +j = U32.and(i, U32.sub(S, 1))
  +z = U32.is_lt(j, U32.shr(S))
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), S), P.size_tree(T, d, t, hf)) :
    {Some{Pair.snd(Array<T>, T, Array.swap.at(T, i, v, _))} == List.get(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d)) : Maybe<&2, T>}
  %slot_n(i, d, hd) :
    {Some{Pair.snd(Array<T>, T, Array.swap.go(T, P.fromT(T, t), S, j, v, z))} == List.get(&2, T, D.view(T, P.fromT(T, t)), _) : Maybe<&2, T>}
  gso(T, d, t, S, j, v, z, hf, size_n(d, hd), jlt(i, d, hd), {==})

law swap_view_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +i: U32
  for +v: T
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {D.view(T, Pair.fst(Array<T>, T, Array.swap(T, P.fromT(T, t), i, v)))
    == List.set(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d), v) : List<&2, T>}

def swap_view_t(T, t, d, i, v, hf, hd):
  +S = U32.shln(1, d)
  +j = U32.and(i, U32.sub(S, 1))
  +z = U32.is_lt(j, U32.shr(S))
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), S), P.size_tree(T, d, t, hf)) :
    {D.view(T, Pair.fst(Array<T>, T, Array.swap.at(T, i, v, _))) == List.set(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d), v) : List<&2, T>}
  %slot_n(i, d, hd) :
    {D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), S, j, v, z))) == List.set(&2, T, D.view(T, P.fromT(T, t)), _, v) : List<&2, T>}
  gsv(T, d, t, S, j, v, z, hf, size_n(d, hd), jlt(i, d, hd), {==})

law set_view_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +i: U32
  for +v: T
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  {D.view(T, Array.set(T, P.fromT(T, t), i, v))
    == List.set(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d), v) : List<&2, T>}

def set_view_t(T, t, d, i, v, hf, hd):
  +S = U32.shln(1, d)
  +j = U32.and(i, U32.sub(S, 1))
  +z = U32.is_lt(j, U32.shr(S))
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), S), P.size_tree(T, d, t, hf)) :
    {D.view(T, Array.set.fin(T, Array.swap.at(T, i, v, _))) == List.set(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d), v) : List<&2, T>}
  %Equal.sym(Array<T>, Array.set.fin(T, Array.swap.go(T, P.fromT(T, t), S, j, v, z)),
    Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), S, j, v, z)), P.fin_fst(T, Array.swap.go(T, P.fromT(T, t), S, j, v, z))) :
    {D.view(T, _) == List.set(&2, T, D.view(T, P.fromT(T, t)), D.slot(i, d), v) : List<&2, T>}
  %slot_n(i, d, hd) :
    {D.view(T, Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), S, j, v, z))) == List.set(&2, T, D.view(T, P.fromT(T, t)), _, v) : List<&2, T>}
  gsv(T, d, t, S, j, v, z, hf, size_n(d, hd), jlt(i, d, hd), {==})

# Writing one leaf, then reading another
# ======================================

# The tree a swap leaves, as a Tree (so the written array has a mirror too).
def tswap(-T: Data, t: P.Tree<T>, +n: U32, +i: U32, v: T, z: Bool) -> P.Tree<T>:
  match t z:
    case P.TLeaf{x} _:
      P.TLeaf{v}
    case P.TNode{l, r} True{}:
      +h = U32.shr(n)
      P.TNode{tswap(T, l, h, i, v, U32.is_lt(i, U32.shr(h))), r}
    case P.TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      P.TNode{l, tswap(T, r, h, j, v, U32.is_lt(j, U32.shr(h)))}

law tswap_eq:
  for -T: Data
  for +t: P.Tree<T>
  for +n: U32
  for +i: U32
  for +v: T
  for +z: Bool
  {P.fromT(T, tswap(T, t, n, i, v, z)) == Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), n, i, v, z)) : Array<T>}

def tswap_eq(T, t, n, i, v, z):
  match t z:
    case P.TLeaf{x} _:
      {==}
    case P.TNode{l, r} True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.lo(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))),
        ANode{Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, l), h, i, v, z2)), P.fromT(T, r)},
        P.lo_fst(T, P.fromT(T, r), Array.swap.go(T, P.fromT(T, l), h, i, v, z2))) :
        {ANode{P.fromT(T, tswap(T, l, h, i, v, z2)), P.fromT(T, r)} == _ : Array<T>}
      %tswap_eq(T, l, h, i, v, z2) :
        {ANode{P.fromT(T, tswap(T, l, h, i, v, z2)), P.fromT(T, r)} == ANode{_, P.fromT(T, r)} : Array<T>}
      {==}
    case P.TNode{l, r} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T>, Pair.fst(Array<T>, T, Array.swap.hi(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))),
        ANode{P.fromT(T, l), Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, r), h, j, v, z2))},
        P.hi_fst(T, P.fromT(T, l), Array.swap.go(T, P.fromT(T, r), h, j, v, z2))) :
        {ANode{P.fromT(T, l), P.fromT(T, tswap(T, r, h, j, v, z2))} == _ : Array<T>}
      %tswap_eq(T, r, h, j, v, z2) :
        {ANode{P.fromT(T, l), P.fromT(T, tswap(T, r, h, j, v, z2))} == ANode{P.fromT(T, l), _} : Array<T>}
      {==}

def set_tree(-T: Data, +t: P.Tree<T>, +i: U32, +v: T) -> P.Tree<T>:
  +n = Pair.snd(Array<T>, U32, Array.size(T, P.fromT(T, t)))
  +j = U32.and(i, U32.sub(n, 1))
  tswap(T, t, n, j, v, U32.is_lt(j, U32.shr(n)))

law set_tree_eq:
  for -T: Data
  for +t: P.Tree<T>
  for +i: U32
  for +v: T
  {Array.set(T, P.fromT(T, t), i, v) == P.fromT(T, set_tree(T, t, i, v)) : Array<T>}

def set_tree_eq(T, t, i, v):
  +n = Pair.snd(Array<T>, U32, Array.size(T, P.fromT(T, t)))
  +j = U32.and(i, U32.sub(n, 1))
  +z = U32.is_lt(j, U32.shr(n))
  %Equal.sym(Array<T> & U32, Array.size(T, P.fromT(T, t)), (P.fromT(T, t), n), P.size_eta(T, P.fromT(T, t))) :
    {Array.set.fin(T, Array.swap.at(T, i, v, _)) == P.fromT(T, set_tree(T, t, i, v)) : Array<T>}
  %Equal.sym(Array<T>, Array.set.fin(T, Array.swap.go(T, P.fromT(T, t), n, j, v, z)),
    Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), n, j, v, z)), P.fin_fst(T, Array.swap.go(T, P.fromT(T, t), n, j, v, z))) :
    {_ == P.fromT(T, set_tree(T, t, i, v)) : Array<T>}
  Equal.sym(Array<T>, P.fromT(T, tswap(T, t, n, j, v, z)), Pair.fst(Array<T>, T, Array.swap.go(T, P.fromT(T, t), n, j, v, z)),
    tswap_eq(T, t, n, j, v, z))

def unsome(-T: Data, +d: T, m: Maybe<&2, T>) -> T:
  match m:
    case None{}:
      d
    case Some{x}:
      x

law get_set_other_t:
  for -T: Data
  for +t: P.Tree<T>
  for +d: Nat
  for +i: U32
  for +j: U32
  for +v: T
  for +hf: {D.full(T, P.fromT(T, t), d) == True{} : Bool}
  for +hd: {Nat.is_lt(d, 32n) == True{} : Bool}
  for +hij: {Nat.is_eq(D.slot(i, d), D.slot(j, d)) == False{} : Bool}
  {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, P.fromT(T, t), i, v), j))
    == Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j)) : T}

def get_set_other_t(T, t, d, i, j, v, hf, hd, hij):
  +t2 = set_tree(T, t, i, v)
  +V = D.view(T, P.fromT(T, t))
  +se = set_tree_eq(T, t, i, v)
  +hf2 = B.subst(Array<T>, X => {D.full(T, X, d) == True{} : Bool}, Array.set(T, P.fromT(T, t), i, v), P.fromT(T, t2), se,
    S.set_full(T, P.fromT(T, t), d, i, v, hf))
  +c1 = get_view_t(T, t2, d, j, hf2, hd)
  +c2 = Equal.trans(List<&2, T>, D.view(T, P.fromT(T, t2)), D.view(T, Array.set(T, P.fromT(T, t), i, v)),
    List.set(&2, T, V, D.slot(i, d), v),
    Equal.cong(Array<T>, List<&2, T>, X => D.view(T, X), P.fromT(T, t2), Array.set(T, P.fromT(T, t), i, v),
      Equal.sym(Array<T>, Array.set(T, P.fromT(T, t), i, v), P.fromT(T, t2), se)),
    set_view_t(T, t, d, i, v, hf, hd))
  +c3 = B.get_set_ne(T, V, D.slot(i, d), D.slot(j, d), v, hij)
  +c4 = Equal.sym(Maybe<&2, T>, Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j))},
    List.get(&2, T, V, D.slot(j, d)), get_view_t(T, t, d, j, hf, hd))
  +ss = Equal.trans(Maybe<&2, T>, Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t2), j))},
    List.get(&2, T, D.view(T, P.fromT(T, t2)), D.slot(j, d)), Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j))},
    c1,
    Equal.trans(Maybe<&2, T>, List.get(&2, T, D.view(T, P.fromT(T, t2)), D.slot(j, d)),
      List.get(&2, T, List.set(&2, T, V, D.slot(i, d), v), D.slot(j, d)),
      Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j))},
      Equal.cong(List<&2, T>, Maybe<&2, T>, X => List.get(&2, T, X, D.slot(j, d)),
        D.view(T, P.fromT(T, t2)), List.set(&2, T, V, D.slot(i, d), v), c2),
      Equal.trans(Maybe<&2, T>, List.get(&2, T, List.set(&2, T, V, D.slot(i, d), v), D.slot(j, d)),
        List.get(&2, T, V, D.slot(j, d)), Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j))}, c3, c4)))
  %Equal.sym(Array<T>, Array.set(T, P.fromT(T, t), i, v), P.fromT(T, t2), se) :
    {Pair.snd(Array<T>, T, Array.get(T, _, j)) == Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j)) : T}
  Equal.cong(Maybe<&2, T>, T, m => unsome(T, v, m), Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t2), j))},
    Some{Pair.snd(Array<T>, T, Array.get(T, P.fromT(T, t), j))}, ss)

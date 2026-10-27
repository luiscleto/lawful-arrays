import Base

# Lemmas about Bool, Nat and List that Base lacks, used by the array proofs.
# Some are copied from ../framebender/proof_base.bend (same author, MIT).

# Equality
# ========

# Transport along an equation.
def subst(-A: Type, -P: A -> Type, -x: A, -y: A, e: {x == y : A}, p: P(x)) -> P(y):
  %e : P(_)
  p

# Bool
# ====

def Bool.disc_ft(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false_ne_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_ne_true(e):
  %e : Bool.disc_ft(_)
  Unit{}

law true_ne_false:
  for e: {True{} == False{} : Bool}
  Empty

def true_ne_false(e):
  false_ne_true(Equal.sym(Bool, True{}, False{}, e))

law and_true_l:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_true_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_ne_true(e))

law and_true_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_true_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_ne_true(e))

# Nat
# ===

def Nat.disc_z(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law succ_ne_zero:
  for -n: Nat
  for e: {1n+n == 0n : Nat}
  Empty

def succ_ne_zero(n, e):
  %e : Nat.disc_z(_)
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law succ_inj:
  for -a: Nat
  for -b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

law add_zero:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}

def add_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law sub_zero:
  for +i: Nat
  {Nat.sub(i, 0n) == i : Nat}

def sub_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

law lt_zero:
  for +i: Nat
  {Nat.is_lt(i, 0n) == False{} : Bool}

def lt_zero(i):
  match i:
    case 0n:
      {==}
    case 1n+k:
      {==}

law lt_zero_absurd:
  for +i: Nat
  for e: {Nat.is_lt(i, 0n) == True{} : Bool}
  Empty

def lt_zero_absurd(i, e):
  false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{},
    Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, lt_zero(i)), e))

# Below 1 is 0.
law lt_one:
  for +k: Nat
  for e: {Nat.is_lt(k, 1n) == True{} : Bool}
  {k == 0n : Nat}

def lt_one(k, e):
  match k:
    case 0n:
      {==}
    case 1n+j:
      Empty.absurd({1n+j == 0n : Nat}, lt_zero_absurd(j, e))

law not_lt_le:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_lt(a, b) == False{} : Bool}
  {Nat.is_le(b, a) == True{} : Bool}

def not_lt_le(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, true_ne_false(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_lt_le(p, q, e)

# k is at least m and below m + m2, so k - m is below m2.
law lt_sub:
  for +m: Nat
  for +k: Nat
  for +m2: Nat
  for h1: {Nat.is_lt(k, m) == False{} : Bool}
  for h2: {Nat.is_lt(k, Nat.add(m, m2)) == True{} : Bool}
  {Nat.is_lt(Nat.sub(k, m), m2) == True{} : Bool}

def lt_sub(m, k, m2, h1, h2):
  match m k:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, sub_zero(k)) : {Nat.is_lt(_, m2) == True{} : Bool}
      h2
    case 1n+q 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+q), m2) == True{} : Bool}, true_ne_false(h1))
    case 1n+q 1n+j:
      lt_sub(q, j, m2, h1, h2)

law lt0_add:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_lt(0n, a) == True{} : Bool}
  {Nat.is_lt(0n, Nat.add(a, b)) == True{} : Bool}

def lt0_add(a, b, e):
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, b) == True{} : Bool}, false_ne_true(e))
    case 1n+p:
      {==}

law pow_pos:
  for +d: Nat
  {Nat.is_lt(0n, Nat.pow(2n, d)) == True{} : Bool}

def pow_pos(d):
  match d:
    case 0n:
      {==}
    case 1n+p:
      lt0_add(Nat.pow(2n, p), Nat.add(Nat.pow(2n, p), 0n), pow_pos(p))

# 2^(1+p) unfolds to p' + (p' + 0); this is p' + p'.
law pow_succ:
  for +p: Nat
  {Nat.pow(2n, 1n+p) == Nat.add(Nat.pow(2n, p), Nat.pow(2n, p)) : Nat}

def pow_succ(p):
  %add_zero(Nat.pow(2n, p)) :
    {Nat.pow(2n, 1n+p) == Nat.add(Nat.pow(2n, p), _) : Nat}
  {==}

law lt_dbl:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(a, a), Nat.add(b, b)) == True{} : Bool}

def lt_dbl(a, b, e):
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.add(a, a), 0n) == True{} : Bool}, lt_zero_absurd(a, e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)) :
        {Nat.is_lt(_, Nat.add(q, 1n+q)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(q, 1n+q), 1n+Nat.add(q, q), add_succ(q, q)) :
        {Nat.is_lt(1n+Nat.add(p, p), _) == True{} : Bool}
      lt_dbl(p, q, e)

law lt_one_dbl:
  for +b: Nat
  for e: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(1n, Nat.add(b, b)) == True{} : Bool}

def lt_one_dbl(b, e):
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, false_ne_true(e))
    case 1n+q:
      %Equal.sym(Nat, Nat.add(q, 1n+q), 1n+Nat.add(q, q), add_succ(q, q)) :
        {Nat.is_lt(1n, 1n+_) == True{} : Bool}
      {==}

law pow_lt:
  for +d: Nat
  for +e: Nat
  for h: {Nat.is_lt(d, e) == True{} : Bool}
  {Nat.is_lt(Nat.pow(2n, d), Nat.pow(2n, e)) == True{} : Bool}

def pow_lt(d, e, h):
  match d e:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.pow(2n, d), 1n) == True{} : Bool}, lt_zero_absurd(d, h))
    case 0n 1n+q:
      %Equal.sym(Nat, Nat.pow(2n, 1n+q), Nat.add(Nat.pow(2n, q), Nat.pow(2n, q)), pow_succ(q)) :
        {Nat.is_lt(1n, _) == True{} : Bool}
      lt_one_dbl(Nat.pow(2n, q), pow_pos(q))
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.pow(2n, 1n+p), Nat.add(Nat.pow(2n, p), Nat.pow(2n, p)), pow_succ(p)) :
        {Nat.is_lt(_, Nat.pow(2n, 1n+q)) == True{} : Bool}
      %Equal.sym(Nat, Nat.pow(2n, 1n+q), Nat.add(Nat.pow(2n, q), Nat.pow(2n, q)), pow_succ(q)) :
        {Nat.is_lt(Nat.add(Nat.pow(2n, p), Nat.pow(2n, p)), _) == True{} : Bool}
      lt_dbl(Nat.pow(2n, p), Nat.pow(2n, q), pow_lt(p, q, h))

# List
# ====

law length_append:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  {List.length(&2, A, List.append(&2, A, xs, ys))
    == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}

def length_append(A, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %length_append(A, t, ys) :
        {1n+List.length(&2, A, List.append(&2, A, t, ys)) == 1n+_ : Nat}
      {==}

# Before index length(xs), xs ++ ys reads like xs.
law get_append_l:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +i: Nat
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.get(&2, A, List.append(&2, A, xs, ys), i) == List.get(&2, A, xs, i) : Maybe<&2, A>}

def get_append_l(A, xs, ys, i, e):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.get(&2, A, ys, i) == None{} : Maybe<&2, A>}, lt_zero_absurd(i, e))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      get_append_l(A, t, ys, k, e)

# From index length(xs) on, xs ++ ys reads like ys.
law get_append_r:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +i: Nat
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {List.get(&2, A, List.append(&2, A, xs, ys), i)
    == List.get(&2, A, ys, Nat.sub(i, List.length(&2, A, xs))) : Maybe<&2, A>}

def get_append_r(A, xs, ys, i, e):
  match xs i:
    case Nil{} _:
      %Equal.sym(Nat, Nat.sub(i, 0n), i, sub_zero(i)) : {List.get(&2, A, ys, i) == List.get(&2, A, ys, _) : Maybe<&2, A>}
      {==}
    case h <> t 0n:
      Empty.absurd({Some{h} == List.get(&2, A, ys, 0n) : Maybe<&2, A>}, true_ne_false(e))
    case h <> t 1n+k:
      get_append_r(A, t, ys, k, e)

law set_append_l:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +i: Nat
  for +v: A
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}
  {List.set(&2, A, List.append(&2, A, xs, ys), i, v)
    == List.append(&2, A, List.set(&2, A, xs, i, v), ys) : List<&2, A>}

def set_append_l(A, xs, ys, i, v, e):
  match xs i:
    case Nil{} _:
      Empty.absurd({List.set(&2, A, ys, i, v) == ys : List<&2, A>}, lt_zero_absurd(i, e))
    case h <> t 0n:
      {==}
    case h <> t 1n+k:
      %set_append_l(A, t, ys, k, v, e) :
        {h <> List.set(&2, A, List.append(&2, A, t, ys), k, v) == h <> _ : List<&2, A>}
      {==}

law set_append_r:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +i: Nat
  for +v: A
  for e: {Nat.is_lt(i, List.length(&2, A, xs)) == False{} : Bool}
  {List.set(&2, A, List.append(&2, A, xs, ys), i, v)
    == List.append(&2, A, xs, List.set(&2, A, ys, Nat.sub(i, List.length(&2, A, xs)), v)) : List<&2, A>}

def set_append_r(A, xs, ys, i, v, e):
  match xs i:
    case Nil{} _:
      %Equal.sym(Nat, Nat.sub(i, 0n), i, sub_zero(i)) : {List.set(&2, A, ys, i, v) == List.set(&2, A, ys, _, v) : List<&2, A>}
      {==}
    case h <> t 0n:
      Empty.absurd({v <> List.append(&2, A, t, ys)
        == h <> List.append(&2, A, t, List.set(&2, A, ys, 0n, v)) : List<&2, A>}, true_ne_false(e))
    case h <> t 1n+k:
      %set_append_r(A, t, ys, k, v, e) :
        {h <> List.set(&2, A, List.append(&2, A, t, ys), k, v) == h <> _ : List<&2, A>}
      {==}

law replicate_add:
  for -A: Data
  for +m: Nat
  for +n: Nat
  for +v: A
  {List.replicate(A, Nat.add(m, n), v)
    == List.append(&2, A, List.replicate(A, m, v), List.replicate(A, n, v)) : List<&2, A>}

def replicate_add(A, m, n, v):
  match m:
    case 0n:
      {==}
    case 1n+p:
      %replicate_add(A, p, n, v) :
        {v <> List.replicate(A, Nat.add(p, n), v) == v <> _ : List<&2, A>}
      {==}

# Writing index i does not change index j != i.
law get_set_ne:
  for -A: Data
  for +xs: List<&2, A>
  for +i: Nat
  for +j: Nat
  for +v: A
  for e: {Nat.is_eq(i, j) == False{} : Bool}
  {List.get(&2, A, List.set(&2, A, xs, i, v), j) == List.get(&2, A, xs, j) : Maybe<&2, A>}

def get_set_ne(A, xs, i, j, v, e):
  match xs i j:
    case Nil{} _ _:
      {==}
    case h <> t 0n 0n:
      Empty.absurd({Some{v} == Some{h} : Maybe<&2, A>}, true_ne_false(e))
    case h <> t 0n 1n+q:
      {==}
    case h <> t 1n+p 0n:
      {==}
    case h <> t 1n+p 1n+q:
      get_set_ne(A, t, p, q, v, e)

def head_or(-A: Data, +d: A, xs: List<&2, A>) -> A:
  match xs:
    case Nil{}:
      d
    case h <> t:
      h

def tail(-A: Data, xs: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

law cons_inj_h:
  for -A: Data
  for -x: A
  for -y: A
  for -xs: List<&2, A>
  for -ys: List<&2, A>
  for e: {x <> xs == y <> ys : List<&2, A>}
  {x == y : A}

def cons_inj_h(A, x, y, xs, ys, e):
  Equal.cong(List<&2, A>, A, l => head_or(A, x, l), x <> xs, y <> ys, e)

law cons_inj_t:
  for -A: Data
  for -x: A
  for -y: A
  for -xs: List<&2, A>
  for -ys: List<&2, A>
  for e: {x <> xs == y <> ys : List<&2, A>}
  {xs == ys : List<&2, A>}

def cons_inj_t(A, x, y, xs, ys, e):
  Equal.cong(List<&2, A>, List<&2, A>, l => tail(A, l), x <> xs, y <> ys, e)

# Two appends with equally long first parts: the first parts are equal...
law append_inj_l:
  for -A: Data
  for +x1: List<&2, A>
  for +x2: List<&2, A>
  for -y1: List<&2, A>
  for -y2: List<&2, A>
  for hl: {List.length(&2, A, x1) == List.length(&2, A, x2) : Nat}
  for +e: {List.append(&2, A, x1, y1) == List.append(&2, A, x2, y2) : List<&2, A>}
  {x1 == x2 : List<&2, A>}

def append_inj_l(A, x1, x2, y1, y2, hl, e):
  match x1 x2:
    case Nil{} Nil{}:
      {==}
    case Nil{} h2 <> t2:
      Empty.absurd({Nil{} == h2 <> t2 : List<&2, A>},
        succ_ne_zero(List.length(&2, A, t2), Equal.sym(Nat, 0n, 1n+List.length(&2, A, t2), hl)))
    case h1 <> t1 Nil{}:
      Empty.absurd({h1 <> t1 == Nil{} : List<&2, A>}, succ_ne_zero(List.length(&2, A, t1), hl))
    case h1 <> t1 h2 <> t2:
      %cons_inj_h(A, h1, h2, List.append(&2, A, t1, y1), List.append(&2, A, t2, y2), e) :
        {h1 <> t1 == _ <> t2 : List<&2, A>}
      %append_inj_l(A, t1, t2, y1, y2,
        succ_inj(List.length(&2, A, t1), List.length(&2, A, t2), hl),
        cons_inj_t(A, h1, h2, List.append(&2, A, t1, y1), List.append(&2, A, t2, y2), e)) :
        {h1 <> t1 == h1 <> _ : List<&2, A>}
      {==}

# ...and so are the second parts.
law append_cancel_l:
  for -A: Data
  for +xs: List<&2, A>
  for -y1: List<&2, A>
  for -y2: List<&2, A>
  for e: {List.append(&2, A, xs, y1) == List.append(&2, A, xs, y2) : List<&2, A>}
  {y1 == y2 : List<&2, A>}

def append_cancel_l(A, xs, y1, y2, e):
  match xs:
    case Nil{}:
      e
    case h <> t:
      append_cancel_l(A, t, y1, y2,
        cons_inj_t(A, h, h, List.append(&2, A, t, y1), List.append(&2, A, t, y2), e))

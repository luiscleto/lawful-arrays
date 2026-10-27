import Base
import ./defs.bend as D
import ./proof_base.bend as B
import ./proof_tree.bend as P

# Array.swap and Array.set keep a tree perfect, for any element type. Such
# elements cannot be copied, so no mirror: the lemmas return the new array as a
# witness beside the equations, and each subtree is used once.

# Array.size(a) is (b, n) with b == a.
def SizeW(-T: Type, -a: Array<T>) -> Type:
  &b:Array<T> -> &n:U32 -> {Array.size(T, a) == (b, n) : Array<T> & U32} & {b == a : Array<T>}

law size_node_eq:
  for -T: Type
  for -xs: Array<T>
  for -ys: Array<T>
  for -b: Array<T>
  for -n: U32
  for e: {Array.size(T, xs) == (b, n) : Array<T> & U32}
  {Array.size(T, ANode{xs, ys}) == (ANode{b, ys}, U32.shl(n)) : Array<T> & U32}

def size_node_eq(T, xs, ys, b, n, e):
  %Equal.sym(Array<T> & U32, Array.size(T, xs), (b, n), e) :
    {Array.size.node(T, ys, _) == (ANode{b, ys}, U32.shl(n)) : Array<T> & U32}
  {==}

def size_w.node(-T: Type, -xs: Array<T>, ys: Array<T>, w: SizeW(T, xs)) -> SizeW(T, ANode{xs, ys}):
  (b, n, e, q) = w
  (ANode{b, ys}, U32.shl(n), size_node_eq(T, xs, ys, b, n, e), P.anode_eq(T, b, ys, xs, ys, q, {==}))

def size_w(-T: Type, a: Array<T>) -> SizeW(T, a):
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1, {==}, {==})
    case ANode{xs, ys}:
      size_w.node(T, xs, ys, size_w(T, xs))

# Array.swap.go(a, ...) is (na, old) with na as perfect as a at every depth.
def SwapW(-T: Type, -a: Array<T>, -n: U32, -i: U32, -v: T, -z: Bool, -d: Nat) -> Type:
  &na:Array<T> -> &old:T -> {Array.swap.go(T, a, n, i, v, z) == (na, old) : Array<T> & T}
    & {D.full(T, na, d) == D.full(T, a, d) : Bool}

law lo_eq:
  for -T: Type
  for -ys: Array<T>
  for -r: Array<T> & T
  for -na: Array<T>
  for -old: T
  for e: {r == (na, old) : Array<T> & T}
  {Array.swap.lo(T, ys, r) == (ANode{na, ys}, old) : Array<T> & T}

def lo_eq(T, ys, r, na, old, e):
  %Equal.sym(Array<T> & T, r, (na, old), e) : {Array.swap.lo(T, ys, _) == (ANode{na, ys}, old) : Array<T> & T}
  {==}

law hi_eq:
  for -T: Type
  for -xs: Array<T>
  for -r: Array<T> & T
  for -na: Array<T>
  for -old: T
  for e: {r == (na, old) : Array<T> & T}
  {Array.swap.hi(T, xs, r) == (ANode{xs, na}, old) : Array<T> & T}

def hi_eq(T, xs, r, na, old, e):
  %Equal.sym(Array<T> & T, r, (na, old), e) : {Array.swap.hi(T, xs, _) == (ANode{xs, na}, old) : Array<T> & T}
  {==}

law and_eq_l:
  for -a: Bool
  for -c: Bool
  for -b: Bool
  for e: {a == c : Bool}
  {Bool.and(a, b) == Bool.and(c, b) : Bool}

def and_eq_l(a, c, b, e):
  %e : {Bool.and(a, b) == Bool.and(_, b) : Bool}
  {==}

law and_eq_r:
  for -b: Bool
  for -a: Bool
  for -c: Bool
  for e: {a == c : Bool}
  {Bool.and(b, a) == Bool.and(b, c) : Bool}

def and_eq_r(b, a, c, e):
  %e : {Bool.and(b, a) == Bool.and(b, _) : Bool}
  {==}

def swap_w.lo(-T: Type, -xs: Array<T>, ys: Array<T>, +n: U32, +i: U32, -v: T, +d: Nat,
  w: SwapW(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))), B.pred(d))) ->
  SwapW(T, ANode{xs, ys}, n, i, v, True{}, d):
  match d:
    case 0n:
      (na, old, e, q) = w
      (ANode{na, ys}, old,
        lo_eq(T, ys, Array.swap.go(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), na, old, e), {==})
    case 1n+p:
      (na, old, e, q) = w
      (ANode{na, ys}, old,
        lo_eq(T, ys, Array.swap.go(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), na, old, e),
        and_eq_l(D.full(T, na, p), D.full(T, xs, p), D.full(T, ys, p), q))

def swap_w.hi(-T: Type, xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, -v: T, +d: Nat,
  w: SwapW(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), B.pred(d))) ->
  SwapW(T, ANode{xs, ys}, n, i, v, False{}, d):
  match d:
    case 0n:
      (na, old, e, q) = w
      (ANode{xs, na}, old,
        hi_eq(T, xs, Array.swap.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), na, old, e), {==})
    case 1n+p:
      (na, old, e, q) = w
      (ANode{xs, na}, old,
        hi_eq(T, xs, Array.swap.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v,
          U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), na, old, e),
        and_eq_r(D.full(T, xs, p), D.full(T, na, p), D.full(T, ys, p), q))

def swap_w(-T: Type, a: Array<T>, +n: U32, +i: U32, v: T, +z: Bool, +d: Nat) -> SwapW(T, a, n, i, v, z, d):
  match a z d:
    case ALeaf{x} _ 0n:
      (ALeaf{v}, x, {==}, {==})
    case ALeaf{x} _ 1n+p:
      (ALeaf{v}, x, {==}, {==})
    case ANode{xs, ys} True{} _:
      +h = U32.shr(n)
      swap_w.lo(T, xs, ys, n, i, v, d, swap_w(T, xs, h, i, v, U32.is_lt(i, U32.shr(h)), B.pred(d)))
    case ANode{xs, ys} False{} _:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      swap_w.hi(T, xs, ys, n, i, v, d, swap_w(T, ys, h, j, v, U32.is_lt(j, U32.shr(h)), B.pred(d)))

# The array a swap leaves is perfect: the steps after Array.size.
def swap_full.fin(-T: Type, -a: Array<T>, -b: Array<T>, +n: U32, +i: U32, -v: T, +d: Nat,
  hf: {D.full(T, a, d) == True{} : Bool}, q: {b == a : Array<T>},
  w: SwapW(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)), d)) ->
  {D.full(T, Pair.fst(Array<T>, T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v,
    U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))), d) == True{} : Bool}:
  (na, old, e, f) = w
  %Equal.sym(Array<T> & T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v,
    U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), (na, old), e) :
    {D.full(T, Pair.fst(Array<T>, T, _), d) == True{} : Bool}
  Equal.trans(Bool, D.full(T, na, d), D.full(T, b, d), True{}, f,
    Equal.trans(Bool, D.full(T, b, d), D.full(T, a, d), True{},
      Equal.cong(Array<T>, Bool, x => D.full(T, x, d), b, a, q), hf))

def swap_full.go(-T: Type, -a: Array<T>, +d: Nat, +i: U32, v: T, hf: {D.full(T, a, d) == True{} : Bool},
  w: SizeW(T, a)) -> {D.full(T, Pair.fst(Array<T>, T, Array.swap(T, a, i, v)), d) == True{} : Bool}:
  (b, +n, e, q) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), e) :
    {D.full(T, Pair.fst(Array<T>, T, Array.swap.at(T, i, v, _)), d) == True{} : Bool}
  +j = U32.and(i, U32.sub(n, 1))
  swap_full.fin(T, a, b, n, i, v, d, hf, q, swap_w(T, b, n, j, v, U32.is_lt(j, U32.shr(n)), d))

law swap_full:
  for -T: Type
  for a: Array<T>
  for +d: Nat
  for +i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  {D.full(T, Pair.fst(Array<T>, T, Array.swap(T, a, i, v)), d) == True{} : Bool}

def swap_full(T, a, d, i, v, hf):
  swap_full.go(T, a, d, i, v, hf, size_w(T, a))

def set_full.fin(-T: Type, -a: Array<T>, -b: Array<T>, +n: U32, +i: U32, -v: T, +d: Nat,
  hf: {D.full(T, a, d) == True{} : Bool}, q: {b == a : Array<T>},
  w: SwapW(T, b, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)), d)) ->
  {D.full(T, Array.set.fin(T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v,
    U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))), d) == True{} : Bool}:
  (na, old, e, f) = w
  %Equal.sym(Array<T> & T, Array.swap.go(T, b, n, U32.and(i, U32.sub(n, 1)), v,
    U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), (na, old), e) :
    {D.full(T, Array.set.fin(T, _), d) == True{} : Bool}
  Equal.trans(Bool, D.full(T, na, d), D.full(T, b, d), True{}, f,
    Equal.trans(Bool, D.full(T, b, d), D.full(T, a, d), True{},
      Equal.cong(Array<T>, Bool, x => D.full(T, x, d), b, a, q), hf))

def set_full.go(-T: Type, -a: Array<T>, +d: Nat, +i: U32, v: T, hf: {D.full(T, a, d) == True{} : Bool},
  w: SizeW(T, a)) -> {D.full(T, Array.set(T, a, i, v), d) == True{} : Bool}:
  (b, +n, e, q) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), e) :
    {D.full(T, Array.set.fin(T, Array.swap.at(T, i, v, _)), d) == True{} : Bool}
  +j = U32.and(i, U32.sub(n, 1))
  set_full.fin(T, a, b, n, i, v, d, hf, q, swap_w(T, b, n, j, v, U32.is_lt(j, U32.shr(n)), d))

law set_full:
  for -T: Type
  for a: Array<T>
  for +d: Nat
  for +i: U32
  for v: T
  for hf: {D.full(T, a, d) == True{} : Bool}
  {D.full(T, Array.set(T, a, i, v), d) == True{} : Bool}

def set_full(T, a, d, i, v, hf):
  set_full.go(T, a, d, i, v, hf, size_w(T, a))

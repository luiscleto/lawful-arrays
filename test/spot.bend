import Base
import ../defs.bend as D

# Spot checks: both sides of laws on small arrays of U32.

def a3() -> Array<U32>:
  Array.set(U32, Array.set(U32, Array.new(U32, 3n, 7), 2, 20), 5, 50)

def eqm(x: Maybe<&2, U32>, y: Maybe<&2, U32>) -> Bool:
  match x y:
    case Some{a} Some{b}:
      U32.is_eq(a, b)
    case None{} None{}:
      True{}
    case Some{a} None{}:
      False{}
    case None{} Some{b}:
      False{}

def eql(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      U32.is_eq(x, y) && eql(xt, yt)
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}

def main() -> List<Bool>:
  [ D.full(U32, Array.new(U32, 3n, 7), 3n)
  , Bool.not(D.full(U32, Array.new(U32, 3n, 7), 2n))
  , eql(D.view(U32, Array.new(U32, 2n, 7)), [7, 7, 7, 7])
  , Nat.is_eq(List.length(&2, U32, D.view(U32, a3())), 8n)
  , Nat.is_eq(U32.to_nat(Pair.snd(Array<U32>, U32, Array.size(U32, a3()))), 8n)
  , eql(D.view(U32, a3()), [7, 7, 20, 7, 7, 50, 7, 7])
  , eqm(Some{Pair.snd(Array<U32>, U32, Array.get(U32, a3(), 5))}, List.get(&2, U32, D.view(U32, a3()), D.slot(5, 3n)))
  , eqm(Some{Pair.snd(Array<U32>, U32, Array.get(U32, a3(), 13))}, List.get(&2, U32, D.view(U32, a3()), D.slot(13, 3n)))
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, a3(), 13)), 50)
  , eql(D.view(U32, Array.set(U32, a3(), 10, 99)), List.set(&2, U32, D.view(U32, a3()), D.slot(10, 3n), 99))
  , D.full(U32, Array.set(U32, a3(), 10, 99), 3n)
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, a3(), 6, 66), 6)), 66)
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, a3(), 6, 66), 5)), Pair.snd(Array<U32>, U32, Array.get(U32, a3(), 5)))
  , eql(D.view(U32, Pair.fst(Array<U32>, U32, Array.get(U32, a3(), 4))), D.view(U32, a3()))
  , eql(D.view(U32, Array.new(U32, 0n, 3)), [3])
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.new(U32, 0n, 3), 9)), 3)
    , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, a3(), 6, 66), 14)), 66)
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.set(U32, Array.new(U32, 0n, 1), 5, 9), 0)), 9)
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.get(U32, Array.new(U32, 4n, 42), 1000)), 42)
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.swap(U32, a3(), 5, 1)), 50)
  , eql(D.view(U32, Pair.fst(Array<U32>, U32, Array.swap(U32, a3(), 5, 1))), List.set(&2, U32, D.view(U32, a3()), 5n, 1))
  , U32.is_eq(Pair.snd(Array<U32>, U32, Array.size(U32, a3())), U32.shln(1, 3n))
  , Nat.is_eq(D.slot(13, 3n), 5n)
  , Nat.is_eq(D.slot(5, 3n), 5n)
  , eql(D.view(U32, Pair.fst(Array<U32>, U32, Array.size(U32, a3()))), D.view(U32, a3()))
  , eql(D.view(U32, Pair.fst(Array<U32>, Array<U32>, Array.clone(U32, a3()))), D.view(U32, a3()))
  ]

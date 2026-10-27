import Base

# lawful-arrays definitions. The laws are in LAWS.bend.
#
# Base's Array<T> is a binary tree (ALeaf, ANode) that the runtime stores as one
# flat block; Array.get and Array.set are one load or store there. The laws
# describe an array by the list of its leaves, left to right.

# a is a perfect tree of depth d: 2^d leaves, every one at depth d. Arrays
# made by Array.new are; Array.set and Array.get keep it so.
def full(-T: Type, a: Array<T>, +d: Nat) -> Bool:
  match a d:
    case ALeaf{x} 0n:
      True{}
    case ALeaf{x} 1n+p:
      False{}
    case ANode{xs, ys} 0n:
      False{}
    case ANode{xs, ys} 1n+p:
      full(T, xs, p) && full(T, ys, p)

# The leaves of a, left to right (the same list as Base's Array.to_list, which
# is a template and cannot appear in a law). Elements must be Data.
def view(-T: Data, a: Array<T>) -> List<&2, T>:
  match a:
    case ALeaf{x}:
      [x]
    case ANode{xs, ys}:
      List.append(&2, T, view(T, xs), view(T, ys))

# The leaf an access at index i reaches in a perfect tree of depth d < 32:
# i modulo 2^d. (From depth 32 up, Base's Array.size wraps to 0 and every
# access reaches the last leaf; the laws exclude that.)
def slot(i: U32, d: Nat) -> Nat:
  Nat.mod(U32.to_nat(i), Nat.pow(2n, d))

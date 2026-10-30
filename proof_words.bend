import Base
import lawful-words@0.1.0.0/proof_nat.bend as WN
import lawful-words@0.1.0.0/proof_u32.bend as WU

# The U32 and Nat facts the index proofs need, from lawful-words (BendHub), where
# they are laws (proof_u32.bend and proof_nat.bend restate them with every
# variable reusable). w_shln_fits is to_nat_shln_fits with 2^32 written as
# Nat.pow(2n, 32n): the law's D.two32() cannot be checked (lawful-words
# notes/proof.md).

law w_shr:
  for +a: U32
  {U32.to_nat(U32.shr(a)) == Nat.div(U32.to_nat(a), 2n) : Nat}

def w_shr(a):
  WU.to_nat_shr(a)

law w_lt:
  for +a: U32
  for +b: U32
  {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}

def w_lt(a, b):
  WU.is_lt_to_nat(a, b)

law w_le:
  for +a: U32
  for +b: U32
  {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}

def w_le(a, b):
  WU.is_le_to_nat(a, b)

law w_sub_le:
  for +a: U32
  for +b: U32
  for +h: {U32.is_le(b, a) == True{} : Bool}
  {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}

def w_sub_le(a, b, h):
  WU.to_nat_sub_le(a, b, h)

law w_and_mask:
  for +a: U32
  for +m: U32
  for +k: Nat
  for +h: {U32.to_nat(m) == Nat.sub(Nat.pow(2n, k), 1n) : Nat}
  {U32.to_nat(U32.and(a, m)) == Nat.mod(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

def w_and_mask(a, m, k, h):
  WU.to_nat_and_mask(a, m, k, h)

law w_shln_fits:
  for +a: U32
  for +k: Nat
  for +h: {Nat.is_lt(Nat.mul(U32.to_nat(a), Nat.pow(2n, k)), Nat.pow(2n, 32n)) == True{} : Bool}
  {U32.to_nat(U32.shln(a, k)) == Nat.mul(U32.to_nat(a), Nat.pow(2n, k)) : Nat}

def w_shln_fits(a, k, h):
  WU.to_nat_shln_fits_p(a, k, h)

law n_mod_lt:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

def n_mod_lt(a, b, h):
  WN.mod_lt(a, b, h)

law n_mod_small:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.mod(a, b) == a : Nat}

def n_mod_small(a, b, h):
  WN.mod_small(a, b, h)

law n_div_mul_add:
  for +q: Nat
  for +b: Nat
  for +r: Nat
  for +h: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}

def n_div_mul_add(q, b, r, h):
  WN.div_mul_add(q, b, r, h)

law n_mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def n_mul_comm(a, b):
  WN.mul_comm(a, b)

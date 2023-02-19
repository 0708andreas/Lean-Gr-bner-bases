import data.finsupp.basic
import data.nat.choose
import algebra.monoid_algebra
import data.list
import order.zorn
import data.polynomial data.mv_polynomial

open set
open ring
open polynomial
universes u 
section

-- A monomial on several veriables is a multiset
-- over a ordered set of variables σ

-- Example: {x, x, y, z, z, z} corresponds to
-- the monomial x^2yz^3


-- A linear order is a total, decidable order
variables {σ : Type*} [linear_order σ]

-- The lex order, in terms of multisets
-- A proof of lex m1 m2 is a proof that m1 ≤ m2 in the lex order

def multiset.lex (m1 m2 : multiset σ) : Prop :=
  m1.sort (≥) ≤ m2.sort (≥)

-- Monomials are linearly ordered using the lex order
instance [linear_order σ] : linear_order (multiset σ) :=
  {
    le := multiset.lex,
    lt := (fun (m1 m2 : multiset σ), m1.lex m2 ∧ m1 ≠ m2),
    le_refl := (sorry),
    le_trans := sorry,
    lt_iff_le_not_le := sorry,
    le_antisymm := sorry,
    le_total := sorry,
    decidable_le := sorry,
  }



end
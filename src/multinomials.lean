import data.nat.basic
import data.vector.zip
import dickson
import monomial_order
import algebra.monoid_algebra.basic

noncomputable theory

open vector set finset finsupp

universe u
variables {R : Type u} [field R] {n : ℕ} [monomial_order n]

section multinomial

def multinomial (n : ℕ) (R : Type u) [field R] : Type u :=
  add_monoid_algebra R (vector ℕ n)

instance : comm_ring (multinomial n R) := add_monoid_algebra.comm_ring

def C (n : ℕ) (c : R) : multinomial n R := single 0 c
def X (n : ℕ) (c : R) : multinomial n.succ R := single (1 ::ᵥ 0) c
def mono {n : ℕ} (v : vector ℕ n) (c : R) : multinomial n R := single v n

def coeff {n : ℕ} (v : vector ℕ n) (m : multinomial n R) : R := @coe_fn _ _ (monoid_algebra.has_coe_to_fun _ _) m v

def dvd (d m : multinomial n R) : Prop :=
  ∃ q : multinomial n R, m = d * q

def init [r : monomial_order n] (m : multinomial n R) : vector ℕ n :=
  @dite _ (m = 0) (classical.prop_decidable (m=0))
  (λ h, (0 : vector ℕ n))
  (λ h, finset.max' m.support begin
    rw nonempty_iff_ne_empty,
    by_contradiction h2,
    rw ←ne.def at h,admit,
  end)

-- def init [r : monomial_order n] (m : multinomial n R) (h : m ≠ 0) : vector ℕ n := begin
--   have m_supp_ne_empty : m.support ≠ ∅ := begin
--     by_contradiction h2,
--     rw finsupp.support_eq_empty at h2,
--     exact h h2,
--   end,
--   rw ←nonempty_iff_ne_empty at m_supp_ne_empty,
--   exact finset.max' m.support m_supp_ne_empty,
-- end

lemma init_mult_eq_mult_init (f g : multinomial n R) (h : f ≠ 0 ∧ g ≠ 0) : init (f*g) = (init f) + (init g) := begin

end

lemma dvd_iff_le_init [monomial_order n] (f g : multinomial n R) : dvd f g ↔ init f ≤ init g := begin
  split, {
    assume h,
    cases h with w hq,

  }, {}
end


def lt (m : multinomial n R) [r : monomial_order n] : multinomial n R := begin
  let S := m.support,
  by_cases S.nonempty, {
    let v := finset.max' S h,
    exact (mono v (coeff v m)),
  }, {
    exact 0,
  }
end


end multinomial

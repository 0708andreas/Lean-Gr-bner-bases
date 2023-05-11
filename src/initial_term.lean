import data.nat.basic
import init.algebra.order
import set_theory.cardinal.finite
import data.vector.zip
import data.finsupp.basic
import data.finite.defs
import data.finset.basic
import data.finset.lattice
import data.finsupp.defs
import data.mv_polynomial.basic
import ring_theory.polynomial.basic
import monomial_order

universe u 
variables {σ : Type u } {R : Type*} [field R] [finite σ] [decidable_eq σ] [decidable_eq R]

open mv_polynomial

noncomputable def IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_term σ) :=
  if h : (f = 0) then
    0
  else 
    finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h)
noncomputable def IN' {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : with_bot (mv_term σ) :=
  if h : f = 0 then
    ⊥
  else
    ↑(IN f)
lemma IN'_eq_IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN' f = ↑(IN f) := begin
    rw [IN', dite_right h],
    exact ⊥,
  end
lemma IN'_eq_bot {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f = 0) :
  IN' f = ⊥ := begin
    rw [IN', dite_left h],
    exact IN f,
  end
noncomputable def LT {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_polynomial σ R) :=
  mv_polynomial.monomial (IN f) (f.coeff (IN f))

lemma IN_of_non_zero_eq {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN f = finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h):= begin
    rw IN,
    simp *,
  end
lemma coeff_IN_nonzero [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  coeff (IN f) f ≠ 0 := begin
    rw ←mv_polynomial.mem_support_iff,
    rw IN_of_non_zero_eq _ h,
    exact finset.max'_mem _ _,
  end
lemma IN_mem_support [term_order σ] (f : mv_polynomial σ R) (hf : f ≠ 0) :
IN f ∈ f.support := begin
  rw IN,
  rw dite_right hf,
  exact finset.max'_mem _ _,
  exact IN f,
end
@[simp]
lemma IN_neg [term_order σ] (f : mv_polynomial σ R) : IN (-f) = IN f := begin
  rw [IN, IN],
  by_cases f = 0, {
    have h' : -f = 0 := by simp *,
    simp *,
  }, {
    have h' : ¬(-f = 0) := by simp *,
    simp *, 
  }
end
lemma IN_add_le_max [term_order σ] (f g : mv_polynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
IN (f+g) ≤ max (IN f) (IN g) := begin
  simp,
  by_cases h : f+g = 0, {
    rw h,
    left,
    exact term_order.zero_le _,
  }, {
    have IN_fg : IN (f+g) ∈ (f+g).support := IN_mem_support _ (h),
    have IN_fug := finset.mem_of_subset mv_polynomial.support_add IN_fg,
    rw finset.mem_union at IN_fug,
    cases IN_fug, {
      left,
      conv in (IN f) {rw IN,},
      rw dite_right hf,
      exact finset.le_max' _ _ IN_fug,
      exact IN f,
    }, {
      right,
      conv in (IN g) {rw IN,},
      rw dite_right hg,
      exact finset.le_max' _ _ IN_fug,
      exact IN g,
    }
  }
end
@[simp]
lemma IN_zero [term_order σ] : IN (0 : mv_polynomial σ R) = 0 := begin
  rw IN,
  simp *,
end
@[simp]
lemma LT_zero [term_order σ] : LT (0 : mv_polynomial σ R) = 0 := begin
  rw LT,
  simp *,
end
@[simp]
lemma IN_monomial [term_order σ] (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) : IN (monomial s c) = s := begin
  rw IN,
  simp *,
  conv in (((monomial s) c).support) {rw support_monomial},
  simp *,
end
@[simp]
lemma IN_mul [term_order σ] (f : mv_polynomial σ R) (hf : f ≠ 0) (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) :
IN ((monomial s c)*f) = IN (monomial s c) + IN f := begin
  rw [IN_monomial _ _ hc, IN],
  have H : monomial s c * f ≠ 0 := begin
    intro hX,
    rw ←zero_mul f at hX,
    have hX' := is_domain.mul_right_cancel_of_ne_zero hf hX,
    rw monomial_eq_zero at hX',
    exact hc hX',
  end,
  rw dite_right H, swap, exact 0,
  conv in (monomial s c * f) {rw mv_polynomial.mul_def},
  simp *,
  apply eq_of_le_of_not_lt, {
    refine finset.max'_le _ _ _ _,
    intros y hy,
    have hy' := finset.mem_of_subset (finsupp.support_sum) hy,
    rw finset.mem_bUnion at hy',
    rcases hy' with ⟨i, hi, hy'⟩,
    have hy'' := finset.mem_of_subset (support_monomial_subset) hy',
    rw finset.mem_singleton at hy'',
    rw [IN, hy''],
    simp *,
    apply term_order.additive,
    exact finset.le_max' _ _ hi,
  }, {
    intro hX,
    rw finset.max'_lt_iff at hX,
    specialize hX (s + IN f),
    apply @eq.not_lt _ _ (s + IN f : mv_term σ) (s + IN f : mv_term σ) rfl,
    apply hX,
    rw [mv_polynomial.mem_support_iff, sum_def, coeff_sum],
    simp *,
    exact coeff_IN_nonzero f hf,
  }
end
lemma nonzero_of_LT_nonzero [term_order σ] (f : mv_polynomial σ R) (h : LT f ≠ 0) : f ≠ 0 := begin
  intro hX,
  rw hX at h,
  rw LT_zero at h,
  exact h rfl,
end
lemma eq_zero_of_LT_eq_zero [term_order σ] (f : mv_polynomial σ R) (h : LT f = 0) : f = 0 := begin
  by_contra hX,
  rw [LT, monomial_eq_zero] at h,
  exact coeff_IN_nonzero f hX (h),
end
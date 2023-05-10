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
import dickson
import dickson_add_monoid
import utils

open vector set finset finsupp mv_polynomial classical

universe u 
variables {σ : Type u } {R : Type*} [field R] [finite σ] [decidable_eq σ] [decidable_eq R]

 


@[derive [add_comm_monoid, has_zero, has_sub, add_semigroup]]
def mv_term (σ : Type u) : Type u := (σ →₀ ℕ)
lemma mv_term.sub_add_cancel (v₁ v₂ : σ →₀ ℕ) (h : v₂ ≤ v₁) : v₁ - v₂ + v₂ = v₁ := begin
  ext,
  simp,
  exact nat.sub_add_cancel (h a),
end
lemma mv_term.sub_sub_self (a b : σ →₀ ℕ) (h : b ≤ a) : a - (a - b) = b := begin
  ext,
  simp,
  exact nat.sub_sub_self (h a_1),
end
class term_order (σ : Type u) [finite σ] extends linear_order (mv_term σ) :=
  (additive : ∀ v v₁ v₂ : mv_term σ, v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le : ∀ v : mv_term σ, 0 ≤ v)

lemma weaken_le [t : term_order σ] (v v1 v2 : mv_term σ) :
v ≤ v1 → v ≤ (v1 + v2) := begin
  assume h,
  have v1_le_sum := term_order.additive v1 0 v2 (term_order.zero_le v2),
  rw add_monoid.add_zero _ at v1_le_sum,
  exact le_trans h v1_le_sum,
end

lemma mv_polynomial.empty_support_iff_eq_zero (f : mv_polynomial σ R) :
  (f = 0) ↔ f.support = ∅ := begin
    split, {
      intro h,
      rw h,
      exact mv_polynomial.support_zero,
    }, {
      intro h,
      rw eq_zero_iff,
      intro d,
      rw ←mv_polynomial.not_mem_support_iff,
      rw h,
      exact set.not_mem_empty d,
    }
  end

lemma mv_polynomial.non_empty_support_of_ne_zero (f : mv_polynomial σ R)
  (h : f ≠ 0) : f.support.nonempty := begin
    rw ne.def at h,
    rw mv_polynomial.empty_support_iff_eq_zero at h,
    rw ←finset.not_nonempty_iff_eq_empty at h,
    rw not_not at h,
    exact h,
  end

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


lemma term_order_is_well_order' [t : term_order σ] (S : set (mv_polynomial σ R)) (h : S.nonempty) :
  (∃ f₀ ∈ S, ∀ f ∈ S, (IN(f₀)) ≤ (IN(f)) ) := begin
    have d := mv_dickson (IN '' S),
    cases d with v hv,
    have v_nonempty : v.nonempty := begin
      have some_in_S := set.nonempty.some_mem h,
      have IN_some_in_IN_S := mem_image_of_mem IN some_in_S,
      have some_in_upper := mem_of_subset_of_mem hv.right IN_some_in_IN_S,
      rw mv_upper_set at some_in_upper,
      cases some_in_upper,
      cases some_in_upper_h with s0,
      cases some_in_upper_h_h with hs0,
      exact ⟨ s0, hs0 ⟩,
    end,
    let s₀ := @min' _ (t.to_linear_order) v v_nonempty,
    have s0_in_v : s₀ ∈ v := finset.min'_mem v _,
    rw ←mem_coe at s0_in_v,
    have s0_in_IN_S : s₀ ∈ IN '' S := mem_of_subset_of_mem hv.left s0_in_v,
    rw mem_image_iff_bex at s0_in_IN_S,
    rcases s0_in_IN_S with ⟨ x, ⟨ hx, IN_x_eq_s0 ⟩ ⟩,
    existsi x,
    existsi hx,
    intros f hf,
    rw IN_x_eq_s0,
    have IN_f_in_IN_S := mem_image_of_mem IN hf,
    have IN_f_in_upper := mem_of_subset_of_mem hv.right IN_f_in_IN_S,
    rcases IN_f_in_upper with ⟨ w, ⟨ s, ⟨ hs, IN_f_eq ⟩  ⟩ ⟩,
    rw IN_f_eq,
    rw add_comm w s,
    apply weaken_le,
    exact @min'_le _ t.to_linear_order v s hs,
  end
#check @term_order_is_well_order'

lemma term_order_is_well_order [t : term_order σ] (S : set (mv_term σ)) (h : S.nonempty) :
  (∃ t₀ ∈ S, ∀ t ∈ S, ¬ t < t₀) := begin
    have d := mv_dickson S,
    cases d with v hv,
    have v_nonempty : v.nonempty := begin
      have some_in_S := set.nonempty.some_mem h,
      have some_in_upper := mem_of_subset_of_mem hv.right some_in_S,
      rcases some_in_upper with ⟨ x, s0, hs0, _ ⟩,
      exact ⟨ s0, hs0 ⟩
    end,
    let s₀ := @min' _ t.to_linear_order v v_nonempty,
    have s0_in_v : s₀ ∈ v := finset.min'_mem v _,
    rw ←mem_coe at s0_in_v,
    have s0_in_S := mem_of_subset_of_mem hv.left s0_in_v,
    existsi s₀,
    existsi s0_in_S,
    intros s hs,
    have s_in_upper := mem_of_subset_of_mem hv.right hs,
    rcases s_in_upper with ⟨ w, ⟨ r, ⟨ hr, s_eq ⟩ ⟩ ⟩,
    rw s_eq,
    rw add_comm w r,
    apply not_lt_of_le,
    apply weaken_le,
    exact @min'_le _ t.to_linear_order v r hr,
  end

instance [term_order σ] : has_well_founded (mv_term σ) := {
  r := (<),
  wf := begin
    rw well_founded.well_founded_iff_has_min,
    intros s hs,
    exact term_order_is_well_order s hs,
  end,
}
instance [term_order σ] : has_well_founded (with_bot (mv_term σ)) := {
  r := linear_order.lt,
  wf := with_bot.well_founded_lt (has_well_founded.wf),
}
#check term_order_is_well_order



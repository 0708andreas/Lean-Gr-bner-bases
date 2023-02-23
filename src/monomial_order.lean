import data.nat.basic
import set_theory.cardinal.finite
import data.vector.zip
import data.finsupp.basic
import data.finite.defs
import data.finset.basic
import data.finsupp.defs
import data.mv_polynomial.basic
import dickson

open vector set finset finsupp mv_polynomial classical

universe u 
variables {σ : Type u } {R : Type*} [field R] [finite σ] [decidable_eq σ] [decidable_eq R]

instance : has_dvd (σ →₀ ℕ) := {
  dvd := λ v w : σ →₀ ℕ, ∃ c : σ →₀ ℕ, w = v + c
}

class term_order (σ : Type u) [finite σ] extends linear_order (σ →₀ ℕ) :=
  (additive : ∀ v v₁ v₂ : σ →₀ ℕ, v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le_v : ∀ v : σ →₀ ℕ, 0 ≤ v)

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

lemma mv_polynomial.non_empty_support_of_ne_zero (f : mv_polynomial σ R) (h : f ≠ 0) :
  f.support.nonempty := begin
    rw ne.def at h,
    rw mv_polynomial.empty_support_iff_eq_zero at h,
    rw ←finset.not_nonempty_iff_eq_empty at h,
    rw not_not at h,
    exact h,
  end

noncomputable def IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (σ →₀ ℕ) :=
  dite (f = 0)
    (λ h, 0)
    (λ h, finset.max' f.support begin
      cases finset.eq_empty_or_nonempty f.support, {
      exfalso,
      rw ←mv_polynomial.empty_support_iff_eq_zero at h_1,
      contradiction,
      }, {
        exact h_1,
      }
    end)

lemma IN_of_non_zero_eq {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN f = finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h):= begin
    rw IN,
    rw dite_eq_iff,
    right,
    rw ne.def at h,
    existsi h,
    refl,
  end

noncomputable def LT [term_order σ] (f : mv_polynomial σ R) : R :=
  coeff (IN f) f

class monomial_order (n : ℕ) extends linear_order (vector ℕ n) :=
  (additive : ∀ v v₁ v₂ : vector ℕ n, v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le_v : ∀ v : vector ℕ n, 0 ≤ v)

lemma monomial_order_is_well_order {n : ℕ} [m : monomial_order n] (S : set (vector ℕ n)) [h : S.nonempty] :
  (∃ s₀ ∈ S, ∀ s ∈ S, s₀ ≤ s) := begin
    have d := dickson n S,
    cases d,
    have d_nonempty : d_w.nonempty := begin
      have some_in_S := set.nonempty.some_mem h,
      have some_in_upper := mem_of_subset_of_mem d_h.right some_in_S,
      rw upper_set at some_in_upper,
      cases some_in_upper,
      cases some_in_upper_h with s₀,
      cases some_in_upper_h_h with hs₀,
      exact ⟨ s₀, hs₀ ⟩,
    end,
    let s₀ := min' d_w d_nonempty,
    apply exists.intro s₀,
    have s0_in_d := min'_mem d_w d_nonempty,
    rw ←mem_coe at s0_in_d,
    have s0_in_S := mem_of_subset_of_mem d_h.left s0_in_d,
    apply exists.intro s0_in_S,
    intros s hs,
    have s_in_upperset := mem_of_subset_of_mem d_h.right hs,
    rw upper_set at s_in_upperset,
    cases s_in_upperset with v hv,
    cases hv with v1,
    cases hv_h with v1_in_d s_eq_v_v1,
    have zero_le_v : 0 ≤ v := m.zero_le_v v,
    have v1_le_v1_v : v1 + 0 ≤ v1 + v := m.additive v1 0 v zero_le_v,
    rw vector.add_zero v1 at v1_le_v1_v,
    rw vector.add_comm at v1_le_v1_v,
    rw add_eq_zip_add at v1_le_v1_v,
    rw ←s_eq_v_v1 at v1_le_v1_v,
    have s0_le_v1 : s₀ ≤ v1 := finset.min'_le d_w v1 v1_in_d,
    exact le_trans s0_le_v1 v1_le_v1_v,
  end


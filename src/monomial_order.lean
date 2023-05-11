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
class term_order (σ : Type u) [finite σ] extends linear_order (mv_term σ) :=
  (additive : ∀ v v₁ v₂ : mv_term σ, v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le : ∀ v : mv_term σ, 0 ≤ v)

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



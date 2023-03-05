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
import dickson
import dickson_add_monoid

open vector set finset finsupp mv_polynomial classical

universe u 
variables {σ : Type u } {R : Type*} [field R] [finite σ] [decidable_eq σ] [decidable_eq R]

instance : has_dvd (σ →₀ ℕ) := {
  dvd := λ v w : σ →₀ ℕ, ∃ c : σ →₀ ℕ, w = v + c
}

inductive mv_term (σ : Type u) : Type u
| intro (s : σ →₀  ℕ) : mv_term
def mv_term.elim : (mv_term σ) → (σ →₀ ℕ)
| (mv_term.intro s) := s 

 

class term_order (σ : Type u) [finite σ] extends linear_order (σ →₀ ℕ) :=
  (additive : ∀ v v₁ v₂ : σ →₀ ℕ, v₁ ≤ v₂ → v + v₁ ≤ v + v₂)
  (zero_le_v : ∀ v : σ →₀ ℕ, 0 ≤ v)

class term_order' (σ : Type u) [finite σ] :=
  (lt : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop)
  (trans : ∀ a b c : (σ →₀ ℕ), (lt a b) → (lt b c) → (lt a c))
  (total : ∀ a b : (σ →₀ ℕ), (a ≠ b) → (lt a b) ∨ (lt b a))
  (additive : ∀ a b c : (σ →₀ ℕ), (lt a b) → lt (c + a) (c + b))
  (zero_lt : ∀ a : (σ →₀ ℕ), (a ≠ 0) → lt 0 a)

infix ` ≺ `:50 := term_order'.lt 

lemma weaken_le [t : term_order σ] (v v1 v2 : σ →₀ ℕ) : v ≤ v1 → v ≤ (v1 + v2) := begin
  assume h,
  have v1_le_sum := term_order.additive v1 0 v2 (term_order.zero_le_v v2),
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
noncomputable def LT {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_polynomial σ R) :=
  mv_polynomial.monomial (IN f) (f.coeff (IN f))

lemma IN_of_non_zero_eq {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  IN f = finset.max' f.support (mv_polynomial.non_empty_support_of_ne_zero f h):= begin
    rw IN,
    rw dite_eq_iff,
    right,
    rw ne.def at h,
    existsi h,
    refl,
  end

theorem min'_le' {α : Type*} [linear_order α] (x : α) (s : finset α) (H : s.nonempty) (H2 : x ∈ s) : s.min' H ≤ x :=
min_le_of_eq H2 (with_top.coe_untop _ _).symm

lemma term_order_is_well_order [t : term_order σ] (S : set (mv_polynomial σ R)) [h : S.nonempty] :
  (∃ f₀ ∈ S, ∀ f ∈ S, t.le (IN(f₀)) (IN(f)) ) := begin
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
    let s₀ := min' v v_nonempty,
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
    have s0_eq : v.min' _ = s₀ := rfl,
    have c := min'_le' s v v_nonempty hs,
    rw s0_eq at c,
    apply weaken_le,
    exact c,
  end


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


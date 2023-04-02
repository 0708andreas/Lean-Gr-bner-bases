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

instance : has_dvd (mv_term σ) := ⟨λ v₁ v₂, ∃ v, v₁ = v₂ + v⟩
lemma mv_term.dvd_intro (a b c : mv_term σ) (h : a = b + c) : a ∣ b := ⟨c, h⟩
lemma mv_term_dvd_trans {a b c : mv_term σ} : a ∣ b → b ∣ c → a ∣ c
| h1 h2 := begin cases h1, cases h2,
           apply mv_term.dvd_intro a c (h2_w + h1_w),
           rw h1_h, rw h2_h,
           rw add_assoc c _ _,
           end

lemma weaken_le [t : term_order σ] (v v1 v2 : mv_term σ) : v ≤ v1 → v ≤ (v1 + v2) := begin
  assume h,
  have v1_le_sum := term_order.additive v1 0 v2 (term_order.zero_le v2),
  rw add_monoid.add_zero _ at v1_le_sum,
  exact le_trans h v1_le_sum,
end
lemma not_le_zero [t : term_order σ] (s : mv_term σ) (h : s ≠ 0) : ¬s ≤ 0 :=
  begin
    intro s,
    refine h _,
    exact linear_order.le_antisymm _ _ s (term_order.zero_le _),
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

noncomputable def IN {σ : Type u} [decidable_eq σ] [finite σ] [term_order σ] (f : mv_polynomial σ R) : (mv_term σ) :=
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
lemma coeff_IN_nonzero [term_order σ] (f : mv_polynomial σ R) (h : f ≠ 0) :
  coeff (IN f) f ≠ 0 := begin
    rw ←mv_polynomial.mem_support_iff,
    rw IN_of_non_zero_eq _ h,
    exact finset.max'_mem _ _,
  end
lemma IN_mult [term_order σ] (f g : mv_polynomial σ R) (hf : f ≠ 0) (hg : g ≠ 0) :
  IN(f * g) = IN(f) + IN(g) := begin
    rw IN,
    by_cases h : f * g = 0, {
      exfalso,
      have hx : f = 0 ∨ g = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h,
      cases hx, exact hf hx, exact hg hx,
    }, {
      rw dite_right h,
      rw IN,
      rw dite_right hf,
      rw IN,
      rw dite_right hg,
      conv in (f * g) { rw mv_polynomial.mul_def, },
      
      have sup_fg : (f*g).support = f.support.bUnion (λa, g.support.bUnion $ λb, {a+b}) := begin

      end,
      admit,
    }
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
      cases some_in_upper,
      cases some_in_upper_h with s0,
      cases some_in_upper_h_h with hs0,
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
#check term_order_is_well_order


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


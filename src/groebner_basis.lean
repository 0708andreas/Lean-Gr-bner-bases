import data.nat.basic
import data.vector.zip
import data.finset.basic
import algebra.monoid_algebra.basic
import ring_theory.ideal.basic
import dickson
import data.mv_polynomial.basic
import monomial_order
import dickson_add_monoid
import dickson

noncomputable theory

open vector set finset finsupp mv_polynomial

universe u
variables {σ : Type*} [finite σ] [decidable_eq σ]
variables {R : Type u} [field R] {n : ℕ} [decidable_eq R]


def finset_grobner_basis [term_order σ] (F : finset (mv_polynomial σ R)) (I : ideal (mv_polynomial σ R)) : Prop :=
  ((↑F : (set (mv_polynomial σ R))) ⊆ I) ∧
  (∀f : mv_polynomial σ R, f ∈ F → f ≠ 0 ) ∧
  (∀ f ∈ I, f ≠ 0 → ∃ f' : mv_polynomial σ R, (f' ∈ F) ∧ ((IN f') ∣ (IN f))) 

theorem exists_finset_grobner_basis [term_order σ] (I : ideal (mv_polynomial σ R)) :
  ∃ F : finset (mv_polynomial σ R), finset_grobner_basis F I := begin
    let SI := {f : mv_polynomial σ R | f ∈ I ∧ f ≠ 0 },
    let S := IN '' SI,
    have exi_V := mv_dickson S,
    cases exi_V with V hV,
    cases hV with V_sub_S S_sub_upper,
    let Vf := single_preimage SI V IN V_sub_S,
    choose Vf H using Vf,
    existsi Vf,
    split, {
      intros f hf,
      have f_in_SI := mem_of_subset_of_mem H.left hf,
      rw set_like.mem_coe,
      exact f_in_SI.left,
    },
    split, {
      intros f hf,
      rw ←mem_coe at hf,
      have f_in_SI := mem_of_subset_of_mem H.left hf,
      exact f_in_SI.right,
    }, {
      intros f hf f_ne_0,
      have f_in_SI : f ∈ SI := ⟨ hf, f_ne_0⟩,
      have in_f_in_S : IN(f) ∈ S := mem_image_of_mem IN f_in_SI,
      have in_f_in_upper := mem_of_subset_of_mem S_sub_upper in_f_in_S,
      cases in_f_in_upper with x hx,
      rcases hx with ⟨ s, ⟨ hs, f_eq⟩  ⟩, 
      rw ←H.right at hs,
      rw finset.mem_image at hs,
      rcases hs with ⟨ f', ⟨ hf', f'_eq ⟩⟩,
      existsi f',
      split, {
        exact hf',
      }, {
        simp *,
        existsi x,
        rw add_comm_monoid.add_comm x s,
      },
    }
  end

def grobner_basis {n : ℕ} [term_order σ] (F : fin n → (mv_polynomial σ R)) (I : ideal (mv_polynomial σ R)) : Prop :=
  (∀ m : fin n, F m ∈ I ∧ F m ≠ 0) ∧
  (∀ f ∈ I, f ≠ 0 → ∃ m : fin n, (IN (F m)) ∣ (IN f))

theorem exists_grobner_basis [term_order σ] (I : ideal (mv_polynomial σ R)) :
  ∃ (n : ℕ) (F : fin n → (mv_polynomial σ R)), grobner_basis F I := begin
    let SI := {f : mv_polynomial σ R | f ∈ I ∧ f ≠ 0 },
    let S := IN '' SI,
    have exi_V := mv_dickson S,
    cases exi_V with V hV,
    cases hV with V_sub_S S_sub_upper,
    let Vf := single_preimage SI V IN V_sub_S,
    choose Vf H using Vf,
    let L := Vf.to_list,
    let n := L.length,
    have hn : ∀ m : fin n, ↑m < L.length := λm, fin.is_lt m,
    let F := λ m : fin n, L.nth_le m (hn m),
    existsi n,
    existsi F,
    split, {
      intro m,
      have Fm_in_L := list.nth_le_mem L m (hn m),
      rw finset.mem_to_list at Fm_in_L,
      rw ←mem_coe at Fm_in_L,
      have Fm_in_SI := mem_of_subset_of_mem H.left Fm_in_L,
      exact Fm_in_SI,
    }, {
      intros f hf f_ne_0,
      have f_in_SI : f ∈ SI := ⟨ hf, f_ne_0 ⟩,
      have in_f_in_S : IN(f) ∈ S := mem_image_of_mem IN f_in_SI,
      have in_f_in_upper := mem_of_subset_of_mem S_sub_upper in_f_in_S,
      cases in_f_in_upper with x hx,
      rcases hx with ⟨ s, ⟨ hs, f_eq⟩  ⟩, 
      rw ←H.right at hs,
      rw finset.mem_image at hs,
      rcases hs with ⟨ f', ⟨ hf', f'_eq ⟩⟩,
      rw ←finset.mem_to_list at hf',
      rw list.mem_iff_nth_le at hf',
      rcases hf' with ⟨ m, ⟨ hm, H ⟩ ⟩,
      existsi (⟨ m, hm ⟩ : fin n),
      have F_eq : F ⟨ m, hm ⟩  = Vf.to_list.nth_le m hm := rfl,
      rw F_eq,
      rw H,
      rw f_eq,
      rw f'_eq,
      existsi x,
      rw add_comm_monoid.add_comm,     
    },
  end
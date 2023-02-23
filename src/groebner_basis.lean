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


def grobner_basis [term_order σ] (F : finset (mv_polynomial σ R)) (I : ideal (mv_polynomial σ R)) : Prop :=
  ((↑F : (set (mv_polynomial σ R))) ⊆ I) ∧
  (∀ f ∈ I, ∃ f' : mv_polynomial σ R, (f' ∈ F) ∧ ((IN f') ∣ (IN f))) 

theorem exists_grobner_basis [term_order σ] (I : ideal (mv_polynomial σ R)) :
  ∃ F : finset (mv_polynomial σ R), grobner_basis F I := begin
    -- let S := {v : σ →₀ ℕ | ∃ f : mv_polynomial σ R, f ∈ I ∧ IN(f) = v},
    let SI := {f : mv_polynomial σ R | f ∈ I},
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
      exact f_in_SI,
    }, {
      intros f hf,
      have f_in_SI : f ∈ SI := hf,
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

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
import mv_division

noncomputable theory

open vector set finset finsupp mv_polynomial

universe u
variables {σ : Type*} [finite σ] [decidable_eq σ] [finite σ] [term_order σ]
variables {R : Type u} [field R] {n : ℕ} [decidable_eq R]


def finset_grobner_basis [term_order σ] (F : finset (mv_polynomial σ R)) (I : ideal (mv_polynomial σ R)) : Prop :=
  ((↑F : (set (mv_polynomial σ R))) ⊆ I) ∧
  (∀f : mv_polynomial σ R, f ∈ F → f ≠ 0 ) ∧
  (∀ f ∈ I, f ≠ 0 → ∃ f' : mv_polynomial σ R, (f' ∈ F) ∧ ((LT f') ∣ (LT f))) 

theorem finset_exists_grobner_basis [term_order σ] (I : ideal (mv_polynomial σ R)) :
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
        have f'_in_SI : f' ∈ SI := mem_of_subset_of_mem H.left hf',
        have f'_ne_zero : f' ≠ 0 := f'_in_SI.right,
        rw LT,
        rw LT,
        existsi (monomial x ((coeff (IN f) f)/(coeff (IN f') f'))),
        rw monomial_mul,
        
        rw field.div_eq_mul_inv,
        rw mul_comm,
        rw mul_assoc,
        rw ←single_eq_monomial,
        rw ←single_eq_monomial,
        conv {
          to_rhs,
          congr,
          skip,
          congr,
          skip,
          rw mul_comm,
        },
        rw mul_inv_cancel _,
        simp *,
        conv {
          to_rhs,
          congr,
          rw add_comm_monoid.add_comm,
        },
        exact coeff_IN_nonzero _ f'_ne_zero,
      }
    },
  end

def grobner_basis {n : ℕ} [term_order σ] (F : fin n → (mv_polynomial σ R)) (I : ideal (mv_polynomial σ R)) : Prop :=
  (∀ m : fin n, F m ∈ I ∧ F m ≠ 0) ∧
  (∀ f ∈ I, f ≠ 0 → ∃ m : fin n, (LT (F m)) ∣ (LT f))

def span_ideal {n : ℕ} (G : fin n → mv_polynomial σ R) : ideal (mv_polynomial σ R) := ideal.span ( λf, ∃i, f = (G i) )
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
      rcases hf' with ⟨ m, ⟨ hm, hf' ⟩ ⟩,
      existsi (⟨ m, hm ⟩ : fin n),
      have F_eq : F ⟨ m, hm ⟩  = Vf.to_list.nth_le m hm := rfl,
      rw F_eq,
      rw hf',
      existsi (monomial x ((coeff (IN f) f)/(coeff (IN f') f'))),
      
      have f'_in_Vf := list.nth_le_mem Vf.to_list m hm,
      rw hf' at f'_in_Vf,
      rw finset.mem_to_list at f'_in_Vf,
      have f'_in_SI : f' ∈ SI := mem_of_subset_of_mem H.left f'_in_Vf,
      have f'_ne_zero : f' ≠ 0 := f'_in_SI.right,
      rw LT,
      rw LT,
      rw monomial_mul,
        
      rw field.div_eq_mul_inv,
      rw mul_comm,
      rw mul_assoc,
      rw ←single_eq_monomial,
      rw ←single_eq_monomial,
      conv {
        to_rhs,
        congr,
        skip,
        congr,
        skip,
        rw mul_comm,
      },
      rw mul_inv_cancel _,
      simp *,
      conv {
        to_rhs,
        congr,
        rw add_comm_monoid.add_comm,
      },
      exact coeff_IN_nonzero _ f'_ne_zero,
    },
  end

lemma span_ideal_basis (G : fin n → mv_polynomial σ R) : basis (fin n) R (span_ideal G) := begin
  basis.mk
end
theorem div_zero_iff_member {n : ℕ} (f : mv_polynomial σ R) (G : fin n → mv_polynomial σ R) (H : grobner_basis G (span_ideal G)) :
  mv_div_r f G = 0 ↔ f ∈ span_ideal G := begin
    split, {
      intro h,
      rw span_ideal,
      rw ideal.mem_span,
    }, {}
  end
import data.nat.basic
import data.vector.zip
import algebra.monoid_algebra.basic
import ring_theory.ideal.basic
import dickson
import multinomials

noncomputable theory

open vector set finset finsupp multinomial

universe u
variables {R : Type u} [field R] {n : ℕ} [decidable_eq (multinomial n R)]


def groebner_basis (F : finset (multinomial n R)) (I : ideal (multinomial n R)) : Prop :=
  ((↑F : (set (multinomial n R))) ⊆ ↑I)
  ∧ ∀ f ∈ I, ∃ f' : multinomial n R, f' ∈ F ∧ dvd f' f
class is_groebner_basis (F : finset (multinomial n R)) (I : ideal (multinomial n R)) :=
  (groebner : ∀ f ∈ I, ∃ f' : multinomial n R, f' ∈ F ∧ dvd f' f)

theorem exists_groebner_basis [r : monomial_order n] (I : ideal (multinomial n R)) :
  ∃ (F : finset (multinomial n R)), groebner_basis F I := begin
    -- let S := {v : vector ℕ n | ∃ f ∈ I, v = (init f)},
    let S : set (vector ℕ n) := init '' (↑I : set (multinomial n R)),
    have v := dickson n S,
    cases v with v hv,
    have F := single_preimage (↑I : set (multinomial n R)) v init hv.left,
    cases F with F hF,
    apply exists.intro F,
    rw groebner_basis,
    split, {
      exact hF.left,
    }, {
      intros f hf,
      
    },
    have fi := λ s ∈ v, begin
      rw ←finset.mem_coe at H,
      have s_in_S := set.mem_of_mem_of_subset H hv.left,
      choose f hf using s_in_S,
    end,
    apply exists.intro,
    

  end
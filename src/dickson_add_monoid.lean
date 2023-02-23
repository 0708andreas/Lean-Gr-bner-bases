import tactic.choose
import data.finset.basic
import data.vector
import data.vector.zip
import data.set.basic
import vector_add_monoid
import data.finsupp.basic
import data.finsupp.defs
import linear_algebra.basic
import logic.equiv.defs
import set_theory.cardinal.finite
import vector_add_monoid
import dickson

noncomputable theory

open classical finset set vector finsupp

lemma vector_equiv_to_fun_eq_nth {n : ℕ} : (equiv.vector_equiv_fin ℕ n).to_fun = vector.nth := rfl

theorem vector_N_equiv_fin_to_N (n : ℕ) :
  add_equiv (vector ℕ n) (fin n → ℕ) :=
  add_equiv.mk' (equiv.vector_equiv_fin ℕ n) (begin
    intros x y,
    unfold_coes,
    rw vector_equiv_to_fun_eq_nth,
    rw add_eq_zip_add,
    refine funext _,
    intro m,
    rw vector.zip_with_nth has_add.add x y,
    simp *,
  end)

def linear_equiv_fun_on_finite {α M : Type*} [fintype α] [add_comm_monoid M] :
  (α →₀ M) ≃+ (α → M) :=
{ to_fun := coe_fn,
  map_add' := λ f g, rfl,
  .. finsupp.equiv_fun_on_finite }

theorem fin_to_N_equiv_fin_finto_N (n : ℕ) :
  add_equiv  (fin n → ℕ) (fin n →₀ ℕ) := add_equiv.symm linear_equiv_fun_on_finite

-- Vi kan bruge finsupp.dom_congr til at få fin n →₀ ℕ ≃+ σ →₀ ℕ for σ ≃ fin n
theorem vector_N_equiv_fin_fto_N (n : ℕ) :
  (vector ℕ n) ≃+ (fin n →₀ ℕ) :=
    add_equiv.trans (vector_N_equiv_fin_to_N n) (fin_to_N_equiv_fin_finto_N n)

theorem vector_N_equiv_finite_fto_N {σ : Type*} [f : finite σ] :
  (vector ℕ (nat.card σ)) ≃+ (σ →₀ ℕ) := begin
    rw finite_iff_exists_equiv_fin at f,
    choose n hn using f,
    have e := (inhabited_of_nonempty hn).default,
    rw (nat.card_eq_of_equiv_fin e),
    have requiv := (e.symm),
    have r := @finsupp.dom_congr (fin n) σ ℕ _ requiv ,
    exact add_equiv.trans (vector_N_equiv_fin_fto_N n) r,
  end

def mv_upper_set {σ : Type*} [finite σ] (n : ℕ) (v : finset (σ →₀ ℕ)) : (set (σ →₀ ℕ)) :=
  {x : σ →₀ ℕ | ∃ (x' s : σ →₀ ℕ) (H : s ∈ v), x = x' + s}

theorem mv_dickson {σ : Type*} [decidable_eq σ] [finite σ] (S : set (σ →₀ ℕ)) :
  ∃ v : finset (σ →₀ ℕ), ↑v ⊆ S ∧ S ⊆ mv_upper_set (nat.card σ) v := begin
    let n := nat.card σ,
    let e := @vector_N_equiv_finite_fto_N σ _,
    let S' : set (vector ℕ (nat.card σ)) := image (e.symm) S,
    have v' := dickson n S',
    cases v' with v' hv',
    let v : finset (σ →₀ ℕ) := finset.image (e) v',
    cases hv' with v'_sub_S' S'_sub_upper,
    existsi v,
    split, {
      intros x hx,
      rw finset.mem_coe at hx,
      rw finset.mem_image at hx,
      rcases hx with ⟨ a, ⟨ ha, h⟩ ⟩,
      rw ←h,
      rw ←finset.mem_coe at ha,
      have hha := mem_of_mem_of_subset ha v'_sub_S',
      rw mem_image _ _ _ at hha,
      rcases hha with ⟨ b, ⟨ hb, h ⟩⟩,
      rw ←h,
      rw add_equiv.apply_symm_apply _ _,
      exact hb,
    }, {
      intros s hs,
      let a := e.symm s,
      have ha : a ∈ S' := set.mem_image_of_mem _ hs,
      have a_in_upper : a ∈ upper_set n v' := mem_of_mem_of_subset ha S'_sub_upper,
      cases a_in_upper with x hx,
      cases hx with x' h,
      cases h with x'_in_v' h,
      have e_h := congr (rfl : ⇑e= ⇑e) h,
      rw ←add_eq_zip_add at e_h,
      rw ←add_equiv.to_fun_eq_coe at e_h,
      rw e.map_add' _ _ at e_h,
      existsi (e.to_fun x),
      existsi (e.to_fun x'),
      existsi (finset.mem_image_of_mem (e.to_fun) x'_in_v'),
      have s_eq := add_equiv.apply_symm_apply e s,
      rw ←add_equiv.to_fun_eq_coe at s_eq,
      rw s_eq at e_h,
      exact e_h,
    },
  end
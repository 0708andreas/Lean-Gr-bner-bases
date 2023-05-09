import data.finsupp.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.mv_polynomial.division
import ring_theory.ideal.basic
import algebra.big_operators.basic
import logic.function.basic
import logic.basic
import monomial_order
import utils

noncomputable theory

open_locale big_operators
open mv_polynomial classical

universe u 
variables {σ : Type*} [finite σ] [decidable_eq σ] [term_order σ]
variables {R : Type*} [field R] [decidable_eq R]



-- Assuming (LT f) ∣ (LT g) returns (LT g)/(LT f).
def monomial_div (g f: mv_polynomial σ R) (h : (LT f) ∣ (LT g)) : mv_polynomial σ R :=
  monomial ((IN g) - (IN f)) ((g.coeff (IN g))/(f.coeff (IN f)))
def term (f : mv_polynomial σ R) (c : σ →₀ ℕ) : (mv_polynomial σ R) := monomial c (coeff c f)
lemma non_zero_of_non_constant (s : mv_polynomial σ R) (h : s.degrees ≠ 0) : s ≠ 0 :=
begin
  by_contradiction hs,
  refine h _,
  rw hs,
  exact degrees_zero,
end

@[simp]
lemma IN_zero : IN (0 : mv_polynomial σ R) = 0 := begin
  rw IN,
  simp *,
end
@[simp]
lemma IN_monomial (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) : IN (monomial s c) = s := begin
  rw IN,
  simp *,
  conv in (((monomial s) c).support) {rw support_monomial},
  simp *,
end
lemma IN_mul (f : mv_polynomial σ R) (hf : f ≠ 0) (s : σ →₀ ℕ) (c : R) (hc : c ≠ 0) :
IN ((monomial s c)*f) = IN (monomial s c) + IN f := begin
  rw IN_monomial _ _ hc,
  rw IN,
  have H : monomial s c * f ≠ 0 := sorry,
  rw dite_right H, swap, exact 0,
  conv in (monomial s c * f) {rw mul_def},
  simp *,

  apply eq_of_le_of_not_lt, {
    refine finset.max'_le _ _ _ _,
    intros y hy,
    have hy' := finset.mem_of_subset (finsupp.support_sum) hy,
    rw finset.mem_bUnion at hy',
    rcases hy' with ⟨i, hi, hy'⟩,
    conv at hy' {
      congr,
      skip,
      rw @support_monomial _ _ (c * f i) (s+i) _ _,
    },


    admit,
  }, {admit,}
end
lemma erase_IN (s f : mv_polynomial σ R) (h : (LT f) ∣ (LT s)) (hs : s ≠ 0) (hs' : s - (monomial_div s f h)*f ≠ 0) : IN (s - (monomial_div s f h)*f) < IN s:=
begin
  admit,
end


noncomputable def fin_find' {n : ℕ} (p : fin n → Prop) (h : ∃ i, p i) : fin n :=
  @option.get (fin n) (@fin.find _ (λ i, p i) (dec_pred _)) ((@fin.is_some_find_iff _ _ (dec_pred _)).mpr h)
noncomputable lemma fin_find'_p {n : ℕ} (p : fin n → Prop) (h : ∃ i, p i) : p (fin_find' p h) := begin
  refine @fin.find_spec _ p (dec_pred _) _ _,
  exact option.get_mem _,
end

def mv_div_step {n : ℕ} (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
                        (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                        (s : mv_polynomial σ R) : 
  (fin n → mv_polynomial σ R) × mv_polynomial σ R × mv_polynomial σ R :=
--         a                        r                  s 
  @dite _ (∃ i:fin n, (LT (F i)) ∣ (LT s)) (prop_decidable _) 
    (λ h, let i := fin_find' (λi, (LT (F i)) ∣ (LT s)) h in
      (function.update a i ((a i) + monomial_div s (F i) (fin_find'_p _ h)), r, s - (monomial_div s (F i) (fin_find'_p _ h))*(F i)))
    (λ h, (a, r + (LT s), s - (LT s)))

lemma mv_div_step_inv1 {n : ℕ}
                    (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
                    (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                    (s : mv_polynomial σ R)
                    (h : f = (∑ i, (a i)*(F i)) + r + s) :
                    (f = ∑ i, ((mv_div_step f F a r s).fst i)*(F i) +
                         (mv_div_step f F a r s).snd.fst +
                         (mv_div_step f F a r s).snd.snd ) := 
  begin
    by_cases he : (∃i, (LT (F i)) ∣ (LT s)), {
      rw h,
      conv {
        congr,
        rw add_assoc,
        skip,
        rw add_assoc,
        rw mv_div_step,
        simp *,
        congr,
        skip,
        rw sub_eq_add_neg,
      },
      conv {
        to_rhs,
        conv {
          congr,
          skip,
          rw add_comm,
          rw add_assoc,
          rw add_comm,
          rw add_assoc,
        },
        rw ←add_assoc,
      },
      rw add_left_inj (r+s),
      let i := fin_find' (λ i, (LT (F i)) ∣ (LT s)) he,
      have i_in_fin_univ : i ∈ @finset.univ (fin n) _ := finset.mem_univ i,
      
      conv { -- Fjern function.update i summen
        to_rhs,
        congr,
        congr,
        skip,
        funext,
        rw function.update_apply a _ _ _,
        rw ite_mul _ _ _ _,
      },
      conv { -- Split det led, vi fjerner ud
        to_rhs,
        congr,
        rw ←finset.add_sum_erase _ _ i_in_fin_univ,
        congr,
        simp*,
      },
      conv {
        to_rhs,
        conv {
          congr,
          rw add_comm,
          rw right_distrib,
        },
        rw ←add_assoc,
      },
      rw @finset.sum_ite_of_false _ (fin n) (finset.univ.erase i) _ (λ x, x = i) _ _ _ begin
        intros x hx,
        simp,
        exact finset.ne_of_mem_erase hx,
      end,
      simp *,
    }, {
      rw mv_div_step,
      simp *,
      rw ←add_assoc,
      simp *,
    }
  end

lemma coeff_monomial_ne_zero (c m : σ →₀ ℕ) (r : R) (h : ¬(coeff c (monomial m r) = 0)) : m = c := begin
  rw coeff_monomial at h,
  by_cases hc : m = c, {
    exact hc,
  }, {
    simp [hc] at h,
    contradiction,
  }
end
lemma mv_div_step_inv2 {n : ℕ}
                          (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R) 
                          (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                          (s : mv_polynomial σ R)
                          (h1 : f = (∑i, (a i) * (F i)) + r + s)
                          (h2 : r = 0 ∨ ∀(m : fin n) (c ∈ r.support), ¬ LT (F m) ∣ monomial c 1) :
                          ((mv_div_step f F a r s).snd.fst = 0 ∨ ∀(m : fin n)(c ∈ (mv_div_step f F a r s).snd.fst.support), ¬ LT (F m) ∣ monomial c 1) :=
begin
  rw mv_div_step,
  by_cases h : (∃ (i : fin n), LT (F i) ∣ LT s), {
    simp *,
    simp at h2,
    exact h2,
  }, {
    simp *,
    cases h2, {
      right,
      intros m c hc,
      rw h2 at hc,
      simp at hc,
      intro hx,
      rw not_exists at h,
      specialize h m,
      rw LT at hc,
      have hs : IN s = c := coeff_monomial_ne_zero _ _ _ hc,
      have c_dvd_s : monomial c 1 ∣ LT s := begin
        rw LT,
        rw hs,
        rw monomial_dvd_monomial,
        simp,
      end,
      have X : LT (F m) ∣ LT s := dvd_trans hx c_dvd_s,
      contradiction,
    }, {
      right,
      intros m c hc,
      specialize h2 m c,
      by_cases hc' : c ∈ r.support, {
        exact h2 hc',
      }, {
        rw mem_support_iff at hc',
        rw not_ne_iff at hc',
        rw hc' at hc,
        rw zero_add at hc,
        rw not_exists at h,
        specialize h m,
        have hs : IN s = c := coeff_monomial_ne_zero _ _ _ hc,
        have c_dvd_s : monomial c 1 ∣ LT s := begin
          rw LT,
          rw hs,
          rw monomial_dvd_monomial,
          simp,
        end,
        intro hx,
        have X : LT (F m) ∣ LT s := dvd_trans hx c_dvd_s,
        contradiction,
      }
    }
  }
end

variables {n : ℕ} (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
lemma mv_div_step_decreases : Π(a : fin n → mv_polynomial σ R)
        (r : mv_polynomial σ R) (s : mv_polynomial σ R)
        (hs : s ≠ 0),
        (IN' (mv_div_step f F a r s).snd.snd < IN' s)
| a r s hs := begin
  by_cases hs' : (mv_div_step f F a r s).snd.snd = 0, {
    rw [hs', IN'_eq_IN _ hs, IN'_eq_bot 0 _],
    exact with_bot.bot_lt_coe _,
    refl,
  },
  suffices H : IN (mv_div_step f F a r s).snd.snd < IN s, {
    rw [IN'_eq_IN _ hs', IN'_eq_IN _ hs, with_bot.coe_lt_coe],
    exact H,
  },
  rw mv_div_step,
  rw mv_div_step at hs',
  by_cases hi : (∃ (i : fin n), LT (F i) ∣ LT s), {
  simp * at *,
  exact erase_IN _ _ _ hs hs',
  }, {
    simp * at *,
    rw IN_of_non_zero_eq _ hs',
    conv {
      to_lhs,
      congr,
      conv {
        congr,
        rw LT,
        rw ←single_eq_monomial,
        rw coeff,
        rw ←finsupp.erase_eq_sub_single _ _,
      },
      rw support,
      rw finsupp.support_erase,
      rw IN_of_non_zero_eq _ hs,
    },
    conv {
      to_rhs,
      rw IN_of_non_zero_eq _ hs,
    },
    refine finset.lt_max'_of_mem_erase_max' _ _ _,
    exact finset.max'_mem _ _,
  }
end

noncomputable def mv_div_aux {n : ℕ} (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R) :
                       (fin n → mv_polynomial σ R) ×
                       (mv_polynomial σ R) × (mv_polynomial σ R) →
                       (fin n → mv_polynomial σ R) × (mv_polynomial σ R) × (mv_polynomial σ R)
| ⟨ a, r, s ⟩  := 
  if hs : s = 0 then
    (a, r, s)
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
          from mv_div_step_decreases f F a r s hs,
    (mv_div_aux (mv_div_step f F a r s))

  using_well_founded {
    rel_tac := λ _ _, `[exact {
      r := λ N M, IN' N.snd.snd < IN' M.snd.snd,
      wf := (inv_image.is_well_founded _ _).wf
    }],
    dec_tac := `[exact this],
  }
lemma mv_div_aux_s_eq_zero : ΠN:(fin n → mv_polynomial σ R) × 
                             (mv_polynomial σ R) × (mv_polynomial σ R), (mv_div_aux f F N).snd.snd = 0
| ⟨ a, r, s ⟩ := 
  if hs : s = 0 then
    begin rw mv_div_aux, simp *, end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
          from mv_div_step_decreases f F a r s hs,
    begin rw mv_div_aux, simp *, end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.snd.snd < IN' M.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this],
    }

lemma mv_div_aux_spec1 : Π (N:(fin n → mv_polynomial σ R) × 
                             (mv_polynomial σ R) × (mv_polynomial σ R))
                             (h : f = (∑i, (N.fst i) * (F i)) + N.snd.fst + N.snd.snd ),
                         f = (∑i, (mv_div_aux f F N).fst i * F i) + (mv_div_aux f F N).snd.fst + (mv_div_aux f F N).snd.snd
| ⟨ a, r, s ⟩ h :=
  if hs : s = 0 then
    begin
      rw [mv_div_aux],
      simp *,
    end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
      from mv_div_step_decreases f F a r s hs,
    begin
      rw [mv_div_aux],
      simp *,
      simp at h,
      rw ←h,
      refine mv_div_aux_spec1 (mv_div_step f F a r s) _,
      refine mv_div_step_inv1 f F a r s h,
    end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.fst.snd.snd < IN' M.fst.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this],
    }

lemma coeff_eq_of_nonzero (c : σ →₀ ℕ) (s : mv_polynomial σ R) (H : ¬coeff c (LT s) = 0) : c = IN s := begin
  rw LT at H,
  rw coeff_monomial at H,
  simp at H,
  exact H.1.symm,
end
lemma field_dvd (a b : R) (H : a ≠ 0) : a ∣ b := begin
  existsi a⁻¹ * b,
  rw ←mul_assoc,
  rw mul_inv_cancel H,
  rw one_mul,
end

lemma mv_div_aux_spec2 : Π(N:(fin n → mv_polynomial σ R) × 
                             (mv_polynomial σ R) × (mv_polynomial σ R))
                          (h1 : f = (∑i, (N.fst i) * (F i)) + N.snd.fst + N.snd.snd)
                          (h2 : N.snd.fst = 0 ∨ ∀(m : fin n) (c ∈ N.snd.fst.support), ¬ LT (F m) ∣ monomial c 1),
                          ((mv_div_aux f F N).snd.fst = 0 ∨ ∀(m : fin n)(c ∈ (mv_div_aux f F N).snd.fst.support), ¬ LT (F m) ∣ monomial c 1)
| ⟨ a, r, s ⟩ h1 h2 := 
  if hs : s = 0 then
    begin
      rw mv_div_aux,
      simp at h2,
      simp *,
    end
  else
    have (IN' (mv_div_step f F a r s).snd.snd) < (IN' s),
      from mv_div_step_decreases f F a r s hs,
    begin
      rw mv_div_aux,
      simp at h1,
      simp *,
      rw ←h1,
      conv in (¬coeff _ (mv_div_aux f F (mv_div_step f F a r s)).snd.fst = 0) {
        rw ←ne.def,
        rw ←mem_support_iff,
      },
      refine mv_div_aux_spec2 (mv_div_step f F a r s) _ _,
      exact mv_div_step_inv1 f F a r s h1,
      apply mv_div_step_inv2 f F a r s h1,
      conv at h2 in ((a, r, s).snd.fst = 0) {simp,},
      exact h2,
    end
    using_well_founded {
      rel_tac := λ _ _, `[exact {
        r := λN M, IN' N.fst.snd.snd < IN' M.fst.snd.snd,
        wf := (inv_image.is_well_founded _ _).wf,
      }],
      dec_tac := `[exact this]
    }

def mv_div {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (fin n → (mv_polynomial σ R)) × (mv_polynomial σ R) :=
  ((mv_div_aux f F (λ_, 0, 0, f)).fst, (mv_div_aux f F (λ_, 0, 0, f)).snd.fst)
def mv_div_a {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (fin n → mv_polynomial σ R) := (mv_div f F).fst
def mv_div_r {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) : 
  (mv_polynomial σ R) := (mv_div f F).snd

theorem mv_div_spec1 {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  f = (∑ m : fin n, ((mv_div_a f F) m * (F m))) + (mv_div_r f F) :=
  begin
    rw [mv_div_a, mv_div_r, mv_div],
    simp,
    have C := (mv_div_aux_spec1 f F (λ (_x : fin n), 0, 0, f) begin simp *, end),
    have s_eq_0 := (mv_div_aux_s_eq_zero f F (λ (_x : fin n), 0, 0, f)),
    rw [s_eq_0, add_zero] at C,
    exact C,
  end
theorem mv_div_spec2 {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (mv_div_r f F) = 0 ∨ ∀ (m : fin n) (c ∈ (mv_div_r f F).support), ¬ LT (F m) ∣ monomial c 1 :=
  begin
    rw [mv_div_r, mv_div],
    have C := (mv_div_aux_spec2 f F (λ (_x : fin n), 0, 0, f) begin simp *, end),
    simp at C,
    simp,
    exact C,
  end



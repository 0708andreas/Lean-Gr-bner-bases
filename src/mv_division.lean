import data.finsupp.basic
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import ring_theory.ideal.basic
import algebra.big_operators.basic
import logic.function.basic
import logic.basic
import monomial_order
import groebner_basis

noncomputable theory

open_locale big_operators
open mv_polynomial classical

universe u 
variables {σ : Type*} [finite σ] [decidable_eq σ] [term_order σ]
variables {R : Type*} [field R] [decidable_eq R]

inductive N : Type
| z : N 
| s : N → N
open N
inductive N_lt : N → N → Prop
| z_lt : Π(n : N), N_lt z (s n)
| s_lt : Π(n m : N), N_lt n m → N_lt (s n) (s m)
def N_add : N → N → N
| z     := id
| (s n) := λ m, s (N_add n m)
def N_add' : N → N → N
| z     n := n
| (s m) n := s (N_add m n)
#check N.rec

lemma N_add_zero : ∀n:N, N_add z n = N_add n z := begin
  apply N.rec,
  refl,
  intros n h,
  rw N_add,
  rw function.comp_app,
  rw ←h,
  rw N_add,
  refl,
end

def N_add_zero' : ∀n:N, N_add z n = N_add n z
| z     := rfl
| (s n) := congr_arg _ (congr_arg _ (N_add_zero n))

def N_succ_add : ∀n m:N, N_add m n.s = (N_add m n).s
| z m := N_add_zero' m

lemma add_eq_add' : N_add = N_add' := begin
  refine funext _,
  intro n,
  refine funext _,
  intro m,
  cases n with n ih, {
    refl,
  }, {
    refl,
  }
end

instance : linear_order (mv_polynomial σ R) := {
  le := sorry,
  le_refl := sorry,
  le_trans := sorry,
  le_antisymm := sorry,
  le_total := sorry,
  decidable_le := sorry,
}

def ex1 : ℕ → ℕ
| 0       := 1
| (n + 1) := have (n+1)/3 < n+1, from nat.div_lt_self' n 1,
       n * ex1((n+1)/3)

example : ex1 0 = 1 := by {rw ex1}

example : well_founded nat.lt := ⟨ 
  nat.rec 
    (acc.intro 0 (λ n h, absurd h (nat.not_lt_zero n)))
    (λ n ih, acc.intro (nat.succ n) (λ m h,
      or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h))
        (λ e, eq.substr e ih) (acc.inv ih)))
 ⟩

theorem well_founded_iff_has_min {α : Type*} {r : α → α → Prop} : (well_founded r) ↔
  ∀ (s : set α), s.nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬ r x m :=
begin
  refine ⟨λ h, h.has_min, λ h, ⟨λ x, _⟩⟩,
  by_contra hx,
  obtain ⟨m, hm, hm'⟩ := h _ ⟨x, hx⟩,
  refine hm ⟨_, λ y hy, _⟩,
  by_contra hy',
  exact hm' y hy' hy,
end

theorem well_order_is_well_founded {α : Type*} (r : α → α → Prop) [is_linear_order α r]
  (h : ∀ (S : set α), S.nonempty → ∃ (s₀ ∈ S), ∀ (s ∈ S), ¬ r s s₀) :
  well_founded r :=
  ⟨ begin
    intro x,
    by_contra hx,
    let S : set α := λ y, ¬(acc r y),
    have H := h S ⟨ x, hx ⟩,
    obtain ⟨ m, hm, hm' ⟩ := H,
    apply hm,
    apply acc.intro,
    intros y hy,
    -- refine hm ⟨m, λ y hy, _ ⟩,
    by_contra hy',
    exact hm' y hy' hy,
  end ⟩

example : well_founded nat.lt := ⟨ begin
  apply nat.rec, {
    apply acc.intro 0,
    intros n h,
    exact absurd h (nat.not_lt_zero n),
  }, {
    intros n ih,
    apply acc.intro (n.succ),
    intros m h,
    have m_le_n := (nat.le_of_succ_le_succ h),
    cases nat.eq_or_lt_of_le m_le_n, {
      rw h_1,
      exact ih,
    }, {
      exact acc.inv ih h_1,
    }
  }
end ⟩ 



-- Assuming (LT f) ∣ (LT g) returns (LT g)/(LT f).
def monomial_div (g f: mv_polynomial σ R) (h : (LT f) ∣ (LT g)) : mv_polynomial σ R :=
  monomial ((IN g) - (IN f)) ((g.coeff (IN g))/(f.coeff (IN f)))

def fin_find' {n : ℕ} (p : fin n → Prop) [decidable_pred p] (h : ∃ i, p i) : fin n :=
  @option.get (fin n) (fin.find (λ i, p i)) (fin.is_some_find_iff.mpr h)
lemma fin_find'_p {n : ℕ} (p : fin n → Prop) [decidable_pred p] (h : ∃ i, p i) : p (fin_find' p h) := begin
  refine fin.find_spec p _,
  -- rw fin_find',
  exact option.get_mem _,
end


def mv_div_step {n : ℕ} (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
                        (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                        (s : mv_polynomial σ R) : 
  (fin n → mv_polynomial σ R) × mv_polynomial σ R × mv_polynomial σ R :=

  @dite _ (∃ i:fin n, (LT (F i)) ∣ (LT s)) (prop_decidable _)
    (λ h, let i := @fin_find' _ (λi, (LT (F i)) ∣ (LT s)) (dec_pred _) h in
      (function.update a i ((a i) + monomial_div s (F i) sorry), r, s - (monomial_div s (F i) sorry)*(F i)))
    (λ n, (a, r + (LT s), s - (LT s)))

lemma mv_div_step_inv {n : ℕ}
                    (f : mv_polynomial σ R) (F : fin n → mv_polynomial σ R)
                    (a : fin n → mv_polynomial σ R) (r : mv_polynomial σ R)
                    (s : mv_polynomial σ R)
                    (h : f = r + s + ∑ i, (a i)*(F i)) :
                    (f = (mv_div_step f F a r s).snd.fst +
                         (mv_div_step f F a r s).snd.snd +
                          ∑ i, ((mv_div_step f F a r s).fst i)*(F i)) := 
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
        rw add_assoc,
      },
      -- rw mv_div_step,
      simp *,
      let i := @fin_find' _ (λ i, (LT (F i)) ∣ (LT s)) (dec_pred _) he,
      have i_in_fin_univ : i ∈ @finset.univ (fin n) _ := finset.mem_univ i,
      -- have hi : i = @fin_find' _ (λ i, (LT (F i)) ∣ (LT s)) (dec_pred _) h := rfl,
      -- rw monomial_div,
      
      conv {
        to_rhs,
        congr,
        skip,
        congr,
        skip,
        funext,
        rw function.update_apply a _ _ _,
        rw ite_mul _ _ _ _,
      },
      conv {
        to_rhs,
        congr,
        skip,
        rw ←finset.add_sum_erase _ _ i_in_fin_univ,
        congr,
        simp*,
      },
      rw ←add_assoc,
      conv {
        to_rhs,
        congr,
        conv {
          congr,
          skip,
          rw add_comm,
          rw right_distrib,
        },
        rw ←add_assoc,
        congr,
      },
      rw neg_add_self,
      rw zero_add,
      rw @finset.sum_ite_of_false _ (fin n) (finset.univ.erase i) _ (λ x, x = i) _ _ _ begin
        intros x hx,
        simp,
        exact finset.ne_of_mem_erase hx,
      end,
      simp *,
    }, {
      rw mv_div_step,
      simp *,
    }
  end

noncomputable def mv_div_aux {n : ℕ} : (mv_polynomial σ R) → (fin n → mv_polynomial σ R) →
                       (fin n → mv_polynomial σ R) →
                       (mv_polynomial σ R) →
    (mv_polynomial σ R) → (fin n → mv_polynomial σ R) × (mv_polynomial σ R) × (mv_polynomial σ R)
| f F a r s := 
  if s = 0 then
    (a, r, s)
  else
    let ⟨ a', r', s' ⟩ := mv_div_step f F a r s in 
    (mv_div_aux f F a' r') s'
    using_well_founded {
      rel_tac := λ _ _, `[exact show (IN (mv_div_step f F a r s).snd.snd.fst) < IN(s), by admit],
    }

def mv_div {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  (fin n → mv_polynomial σ R) × (mv_polynomial σ R) :=


def mv_div {n : ℕ} (f : mv_polynomial σ R) (F : fin n → (mv_polynomial σ R)) :
  ∃ (a : fin n → (mv_polynomial σ R)) (r : mv_polynomial σ R),
    (f = r + ∑ m : fin n, F m * a m) ∧ 
    (r = 0 ∨ ∀ (m : fin n) (c ∈ r.support), ¬ IN(F m) ∣ c) :=
  begin
    
  end

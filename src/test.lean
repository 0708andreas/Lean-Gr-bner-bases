import data.nat.basic
import data.nat.order.basic
import data.nat.parity
import tactic.linarith
import tactic.norm_num


def lg : ℕ → ℕ
| 0 := 0
| (x+1) := have (x+1) / 2 < (x+1), from nat.div_lt_self' x 0,
           1 + lg ((x+1)/2)

def lg_ineq (n : ℕ) : Prop := n+1 < 2^lg (n+1)

lemma two_mul_succ_div_two {m : ℕ} : (2 * m + 1) / 2 = m :=
begin
  rw [nat.succ_div, if_neg], norm_num,
  rintros ⟨k, h⟩, exact nat.two_mul_ne_two_mul_add_one h.symm,
end

lemma two_mul_succ_succ {m : ℕ} : 2 * m + 1 + 1 = 2 * (m + 1) := by linarith

lemma lg_zero : lg 0 = 0 := by {rw lg}
lemma lg_one : lg 1 = 1 := by {erw [lg, lg_zero]}


lemma lg_lemma2'' : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1)
| 0 := by { rw lg_one, norm_num, }
| (x + 1) :=
begin
  cases (nat.even_or_odd x),
  { rcases h with ⟨m, hm⟩, specialize lg_lemma2'' m,
    rw [hm, lg, pow_add],
    rw two_mul_succ_succ, norm_num, exact lg_lemma2'', },
  { rcases h with ⟨m, hm⟩,
    specialize lg_lemma2'' m, rw [hm, lg, pow_add],
    rw [two_mul_succ_succ, two_mul_succ_div_two], linarith }
end
using_well_founded
{ dec_tac := `[exact show m < x + 1, by linarith] }

lemma lg_lemma2'' : ∀(x:ℕ), x+1 < 2^lg (x+1)
| 0 := begin
  rw lg_one,
  linarith,
  end
| (x+1) := begin
  cases (nat.even_or_odd x), {
    rcases h with ⟨ m, hm ⟩,
    have lem := lg_lemma2'' m,
    rw [hm, lg, pow_add],
    rw two_mul_succ_succ,
  }, {}
end
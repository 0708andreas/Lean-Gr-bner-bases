import data.fintype.basic
import data.set.basic
import data.set.finite

open_locale classical 

theorem test {σ : Type*} (S : set σ) [fin_σ : fintype σ] : set.finite S := begin
  unfreezingI {
    induction fin_σ with fin_σ_s,
    induction fin_σ_s using finset.induction_on,
    {
      admit,
    },
    {
      apply fin_σ_s_ᾰ_1,
      
    }
  }
end

inductive XY : Type
| x : XY
| y : XY
open XY
lemma XY.x_ne_y : x = y → false .
instance : decidable_eq XY
| x x := is_true rfl
| x y := is_false XY.x_ne_y
| y x := is_false (ne.symm XY.x_ne_y)
| y y := is_true rfl


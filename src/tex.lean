import tactic.hint
import tactic.suggest

inductive N : Type
| z : N 
| s : N → N 
open N

def N_add : N → N → N
| z     := id
| (s n) := s ∘ (N_add n)

def N_add_zero : ∀ n:N, N_add z n = N_add n z
| z     := rfl
| (s n) := congr_arg id (congr_arg s (N_add_zero n))

def N_add_succ : ∀ n m:N, N_add n m.s = N_add n.s m
| z     m := rfl
| (s n) m := congr_arg s (N_add_succ n m)  

def N_add_comm : ∀ n m:N, N_add n m = N_add m n
| z     m := N_add_zero m 
| (s n) m := eq.subst (eq.symm (N_add_succ m n))
                      (congr_arg s (N_add_comm n m)) 
--  begin
--    rw N_add_succ m n,
--   apply congr_arg s (N_add_comm n m),
--  end

def N_add_comm' : ∀ n m:N, N_add n m = N_add m n 
| z     m := N_add_zero m
| (s n) m := begin
  rw N_add_succ m n,
  refine congr_arg s _,
  exact N_add_comm n m,
end

class group (G : Type) :=
  (mul : G → G → G)
  (mul_assoc : ∀g₁ g₂ g₃ : G, mul (mul g₁ g₂) g₃ = mul g₁ (mul g₂ g₃))
  (one : G)
  (inv : G → G)
  (one_mul : ∀ g : G, mul one g = g)
  (mul_one : ∀ g : G, mul g one = g)
  (mul_inv : ∀ g : G, mul (inv g) g = one)

open group

example (A B : Prop) : (¬ A) → (A ∨ B) → B := begin
  intro na,
  intro h,
  cases h, {
    cases (na h),
  }, {
    exact h,
  }
end

#check eq.subst


inductive even : N → Prop 
| z_even : even z 
| ss_even : Π(n:N) (h : even n), even (s (s n))
open even

def is_even : N → Prop 
| z         := true
| (s z)     := false
| (s (s n)) := is_even n 

#check even.rec 

def ext : Πn:N, even n → is_even n 
| n h := even.rec (trivial : is_even z) (λ n h' t, t) h

def is_even_eq_empty : Πn:N, ¬(even n) → is_even n = false 
| n h := begin
  apply eq_false_of_not_eq_true,
end

def even_dec : Πn:N, even n ∨ ¬ even n 
| z := or.inl z_even
| (s z) := or.inr (λ h, ext (s z) h)
| (s (s n)) := begin
  cases even_dec n, {
    exact or.inl (ss_even n h),
  }, {
    right,
    intro hx,
    have t : is_even n.s.s := ext n.s.s hx,
    have t' : is_even n := t,
    
  }
end
-- import tactic.hint
-- import tactic.suggest
-- import tactic.linarith
import tactic.nth_rewrite
import data.set.basic
import data.prod.lex
import data.nat.basic
import data.int.basic
import algebra.order.ring.lemmas

section N
inductive N : Sort 1
| z : N
| s : N → N
open N
#check N.rec

def N_add : N → N → N
| z     := id
| (s n) := s ∘ (N_add n)

def N_add_zero : ∀ n:N, N_add z n = N_add n z
| z     := rfl
| (s n) := congr_arg id (congr_arg s (N_add_zero n))

universes i j u v
inductive my_prod {A : Sort i} {B : Sort j} : A → B → Sort (max i j)
| intro (a : A) (b : B) : my_prod a b

inductive P_dec (P : Prop) : Type 
| is_false : ¬P → P_dec 
| is_true  :  P → P_dec  
#check P_dec.rec
#check decidable.rec
#check Exists.rec
#check @eq.rec
#check @my_prod.rec
inductive T {L : Sort i} : L → Sort (max i 1)
| leaf : Π l : L, T l 
| node {l1 l2 : L} : ℤ → T l1 → T l2 → T l1

inductive or_int {A : Sort i} : A → Sort (max i 1) 
| left (a : A) : or_int a 
| right (a : A) (x : ℤ) : or_int a 

inductive my_eq {α : Sort 1} (a : α) : α → Prop
| refl : my_eq a

#check @my_eq.rec
#check @eq.rec

-- def add2 : ℕ → ℕ → ℕ
-- | n m := if h : n = 0 then m else add2 (n-1) m
-- using_well_founded {
--   dec_tac := `[exact nat.sub_lt (nat.pos_of_ne_zero h) nat.zero_lt_one ]
-- }
  -- using_well_founded {
  --   dec_tac := `[simp]
  -- }

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

inductive even : N → Prop 
| z_even : even z 
| ss_even : Π(n:N) (h : even n), even (s (s n))
open even

def is_even : N → Prop 
| z         := true
| (s z)     := false
| (s (s n)) := is_even n 

-- #check even.rec 

def ext : Πn:N, even n → is_even n 
| n h := even.rec (trivial : is_even z) (λ n h' t, t) h

-- def is_even_eq_empty : Πn:N, ¬(even n) → is_even n = false 
-- | n h := begin
--   apply eq_false_of_not_eq_true,
-- end

-- def even_dec : Πn:N, even n ∨ ¬ even n 
-- | z := or.inl z_even
-- | (s z) := or.inr (λ h, ext (s z) h)
-- | (s (s n)) := begin
--   cases even_dec n, {
--     exact or.inl (ss_even n h),
--   }, {
--     right,
--     intro hx,
--     have t : is_even n.s.s := ext n.s.s hx,
--     have t' : is_even n := t,
    
--   }
-- end

end N

@[class]
structure group' (G : Type) :=
  (mul : G → G → G)
  (mul_assoc : ∀g₁ g₂ g₃ : G, mul (mul g₁ g₂) g₃ = mul g₁ (mul g₂ g₃))
  (one : G)
  (inv : G → G)
  (one_mul : ∀ g : G, mul one g = g)
  (mul_one : ∀ g : G, mul g one = g)
  (mul_inv : ∀ g : G, mul (inv g) g = one)

open group

@[derive [has_add, has_one]]
def Z_alt := ℤ
def to_Z_alt : ℤ → Z_alt := id 
def of_Z_alt : Z_alt → ℤ := id 

instance : group' Z_alt := {
  mul := λ m n, m + 1 + n, 
  mul_assoc := λ m n k, begin
    rw int.add_assoc,
    rw int.add_assoc,
    conv in (n + (1 + k)) {rw ←int.add_assoc,},
  end,
  one := to_Z_alt (-1),
  inv := λ m, to_Z_alt ((-1) + (-of_Z_alt m) + (-1)),
  one_mul := λ m, begin
    exact int.zero_add m,
  end,
  mul_one := λ m, begin
    rw int.add_assoc,
    nth_rewrite 1 int.add_comm,
    exact int.add_zero m,
  end,
  mul_inv := λ m, begin
    rw [to_Z_alt, of_Z_alt, id.def, id.def, id.def, int.add_assoc, int.add_assoc],
    conv in ((-1:ℤ) + (1 + m)) {rw ←int.add_assoc,},
    simp,
  end,
}

instance (G S : Type*) [gs : group' G] : group' (S → G) := {
  mul := λf g, λs, gs.mul (f s) (g s),
  mul_assoc := λf g h, begin apply funext, intro s, rw gs.mul_assoc, end,
  one := λ_, gs.one,
  inv := λf, λs, gs.inv (f s),
  one_mul := λg, begin apply funext, intro s, rw gs.one_mul,end,
  mul_one := λg, begin apply funext, intro s, rw gs.mul_one, end ,
  mul_inv := λg, begin apply funext, intro s, rw gs.mul_inv, end,
}

inductive my_acc {S : Type*} (r : S → S → Prop) : S → Prop 
| intro : ∀ (s : S), (∀ (t : S), r t s → my_acc t) → my_acc s

lemma my_acc_has_min {S : Type*} (r : S → S → Prop) (wf : ∀s:S, my_acc r s)
  (A : set S) (h : A.nonempty) : ∃s₀ ∈ A, ∀ x ∈ A, ¬ r x s₀ := begin
    -- unfreezingI {
      rcases h with ⟨ a, ha ⟩,
      refine (my_acc.rec _ (wf a)) ha,
      intros x acc_x H hx,
      let A' := {s' ∈ A | r s' x},
      cases set.eq_empty_or_nonempty A', {
        existsi x,
        existsi hx,
        intros x' hx' nax',
        have x'_in_A' : x' ∈ A' := ⟨ hx', nax' ⟩, 
        rw h at x'_in_A',
        exact set.not_mem_empty x' x'_in_A',
      }, {
        rcases h with ⟨ t, ht ⟩,
        have rtx : r t x := ht.2,
        have t_in_A : t ∈ A := set.mem_of_subset_of_mem (set.sep_subset _ _) ht,
        exact H t rtx t_in_A,
      }
    -- }
  end


#check my_acc.rec_on
#check my_acc.rec

def AC {A B : Type*} {r : A → B → Prop} (H : ∀a:A, psigma (λb, r a b)) : psigma (λf:A→B, ∀a:A, r a (f a)) := ⟨ λa, (H a).fst, λa, (H a).snd ⟩

def fix {S : Type*} {C : S → Type*} {r : S → S → Prop} (F : Πx, (Πy, r y x → C y) → C x) (s : S) (h : acc r s) : C s :=
  acc.rec (λx' _ ih, F x' ih) h

theorem my_acc.inv {S : Type*} {r : S → S → Prop} {x y : S} (h1 : my_acc r x) (h2 : r y x) : my_acc r y :=
my_acc.rec_on h1 (λ x1 ac1 ih h2, ac1 y h2) h2

lemma fix_F_eq {S : Type*} {C : S → Type*} {r : S → S → Prop} (x : S) (acx : acc r x)
  (F : Πx, (Πy, r y x → C y) → C x) :
  fix F x acx = F x (λ (y : S) (p : r y x), fix F y (acc.inv acx p)) :=
    acc.drec (λ x r ih, rfl) acx

lemma l1 (m : ℕ) : to_lex (m, 1) < to_lex (m + 1, 0) := begin 
  rw prod.lex.lt_iff,
  left,
  simp,
  exact nat.lt_succ_self m,
end
lemma l2 (m n : ℕ) : to_lex (m + 1, n) < to_lex (m + 1, n + 1) := begin 
  rw prod.lex.lt_iff,
  right,
  split, {
    simp,
  }, {
    simp,
    exact nat.lt_succ_self n,
  }
end
lemma l3 (m n x: ℕ) : to_lex (m, x) < to_lex (m + 1, n + 1) := begin 
  rw prod.lex.lt_iff,
  left,
  simp,
  exact nat.lt_succ_self m,
end
def ack_aux : Π (p1 : ℕ ×ₗ ℕ) (h : Π (p2 : ℕ ×ₗ ℕ), p2 < p1 → ℕ), ℕ
| ⟨ 0, n ⟩ _ := n+1
| ⟨ m+1, 0 ⟩ h := h (m, 1) (l1 m)
| ⟨ m+1, n+1 ⟩ h := h (m, (h (m+1, n) (l2 m n))) (l3 m n _)

def ack (p : ℕ × ℕ) : ℕ := fix ack_aux p ((prod.lex_wf nat.lt_wf nat.lt_wf).apply p)

def ack2 : ℕ → ℕ → ℕ
| 0 n := n+1
| (m+1) 0 := ack2 m 1 
| (m+1) (n+1) := ack2 m (ack2 (m+1) n)

def add : ℕ → ℕ → ℕ
| 0     n := n 
| (m+1) n := (add m n) + 1

example (A B : Prop) : (¬ A) → (A ∨ B) → B := begin
  intro na,
  intro h,
  cases h, {
    cases (na h),
  }, {
    exact h,
  }
end





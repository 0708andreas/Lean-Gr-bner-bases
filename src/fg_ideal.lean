import ring_theory.finiteness

noncomputable theory

open classical

universe u
variables {σ : Type*} [finite σ] [decidable_eq σ] [finite σ]
variables {R : Type u} [semiring R] {n : ℕ} [decidable_eq R]

def find_basis (I : ideal R) : (I.fg) → Σ n:ℕ, basis (fin n) R I
| h := if H : linear_independent R (some (h : ∃ (S : finset R), ideal.span ↑S = I )) then
() else ()

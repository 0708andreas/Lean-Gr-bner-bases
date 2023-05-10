import ring_theory.finiteness

noncomputable theory

open classical

universe u
variables {σ : Type*} [finite σ] [decidable_eq σ] [finite σ]
variables {R : Type u} [semiring R] {n : ℕ} [decidable_eq R]


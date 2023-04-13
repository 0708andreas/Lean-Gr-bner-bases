import data.nat.basic
import data.vector
import data.vector.zip


namespace vector
open vector

instance (n : ℕ) : has_add (vector ℕ n) :=
  ⟨ λ v1 v2, zip_with (+) v1 v2 ⟩
instance (n : ℕ) : has_zero (vector ℕ n) :=
  ⟨ repeat 0 n ⟩

lemma add_eq_zip_add {n : ℕ} (v1 v2 : vector ℕ n) :
  v1 + v2 = zip_with (+) v1 v2 := rfl

@[simp]
lemma zip_with_head {α β γ : Type*} {n : ℕ} (f : α → β → γ)
  (x : vector α n.succ) (y : vector β n.succ) :
  (zip_with f x y).head = f (x.head) (y.head) := begin
    repeat {rw ←nth_zero},
    exact (zip_with_nth f x y 0),
  end

@[simp]
lemma add_head {n : ℕ} (v1 v2 : vector ℕ n.succ) :
  (v1 + v2).head = v1.head + v2.head := begin
    rw add_eq_zip_add,
    simp *,
  end

@[simp]
lemma add_tail {n : ℕ} (v1 v2 : vector ℕ n.succ) :
  (v1 + v2).tail = v1.tail + v2.tail := begin
    repeat {rw add_eq_zip_add},
    simp *,
  end

lemma add_zero {n : ℕ} (v : vector ℕ n) : v + 0 = v := begin
  induction n, {
    rw vector.eq_nil v,
    simp,
  }, {
    rcases exists_eq_cons v with ⟨ head, tail, h⟩,
    rw h,
    rw vector.eq_cons_iff,
    split, {
      simp *,
      refl,
    }, {
      simp *,
      exact n_ih tail,
    }
  }
end
lemma cons_add_eq_add_cons {n : ℕ} (v1 v2 : vector ℕ n) (a b : ℕ) :
  (a ::ᵥ v1) + (b ::ᵥ v2) = (a + b) ::ᵥ (v1 + v2) := begin
    rw [add_eq_zip_add, eq_cons_iff],
    split, {
      rw [zip_with_head, cons_head, cons_head],
    },{
      rw [zip_with_tail, cons_tail, cons_tail],
      refl,
    }
  end

lemma add_comm {n : ℕ} (v1 v2 : vector ℕ n) : v1 + v2 = v2 + v1 := begin
  induction n with n n_ih, {
    simp *,
  }, {
    rcases exists_eq_cons v1 with ⟨ x, xs, hx ⟩,
    rcases exists_eq_cons v2 with ⟨ y, ys, hy ⟩,
    rw [hx, hy],
    repeat {rw cons_add_eq_add_cons},
    rw [n_ih, nat.add_comm],
  }
end

lemma vector.zero_add {n : ℕ} (v : vector ℕ n) : 0 + v = v := begin
  rw vector.add_comm,
  rw vector.add_zero,
end

lemma vector.add_assoc {n : ℕ} (v1 v2 v3 : vector ℕ n) :
  (v1 + v2) + v3 = v1 + (v2 + v3) := begin
    induction n with n n_ih, {
      simp *,
    }, {
      rcases exists_eq_cons v1 with ⟨ x, xs, hx ⟩,
      rcases exists_eq_cons v2 with ⟨ y, ys, hy ⟩,
      rcases exists_eq_cons v3 with ⟨ z, zs, hz ⟩,
      rw [hx, hy, hz],
      repeat {rw cons_add_eq_add_cons},
      rw nat.add_assoc,
      rw n_ih,
    }
  end

instance (n : ℕ) : add_comm_monoid (vector ℕ n) := { 
  add := has_add.add,
  add_assoc := vector.add_assoc,
  zero := 0,
  zero_add := vector.zero_add,
  add_zero := vector.add_zero,
  add_comm := vector.add_comm,
}

end vector
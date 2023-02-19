
import data.nat.basic
import data.vector.zip

open vector

instance (n : ℕ) : has_add (vector ℕ n) :=
  ⟨ λ v1 v2, zip_with (+) v1 v2 ⟩
instance (n : ℕ) : has_zero (vector ℕ n) :=
  ⟨ repeat 0 n ⟩

lemma add_eq_zip_add {n : ℕ} (v1 v2 : vector ℕ n) : v1 + v2 = zip_with (+) v1 v2 :=
  rfl

lemma zip_with_head {α β γ : Type*} {n : ℕ} (f : α → β → γ) (x : vector α n.succ) (y : vector β n.succ) :
  (vector.zip_with f x y).head = f (x.head) (y.head) := begin
    rw ←nth_zero,
    rw ←nth_zero,
    rw ←nth_zero,
    exact (zip_with_nth f x y 0),
  end

lemma vector.add_zero {n : ℕ} (v : vector ℕ n) : v + 0 = v := begin
  induction n, {
    have eq_nil : v = nil := vector.eq_nil v,
    rw eq_nil,
    refl,
  }, {
    have hv := vector.exists_eq_cons v,
    cases hv with head,
    cases hv_h with tail h,
    rw h,
    rw vector.eq_cons_iff,
    split, {
      rw ←h,
      rw add_eq_zip_add,
      rw zip_with_head (+) (v) 0,
      have zero_head_eq_zero : (0 : vector ℕ n_n.succ).head = 0 := rfl,
      rw zero_head_eq_zero,
      rw add_zero,
      rw h,
      rw cons_head,
    }, {
      rw ←h,
      rw add_eq_zip_add,
      rw vector.zip_with_tail _ _ _,
      rw ←add_eq_zip_add,
      have zero_tail_eq_zero : (0 : vector ℕ n_n.succ).tail = 0 := rfl,
      rw zero_tail_eq_zero,
      rw n_ih v.tail,
      rw h,
      rw cons_tail,
    }
  }
end
lemma vector.cons_add_eq_add_cons {n : ℕ} (v1 v2 : vector ℕ n) (a b : ℕ) :
  (a ::ᵥ v1) + (b ::ᵥ v2) = (a + b) ::ᵥ (v1 + v2) := begin
    rw add_eq_zip_add,
    rw eq_cons_iff,
    split, {
      rw zip_with_head,
      rw cons_head,
      rw cons_head,
    },{
      rw zip_with_tail,
      rw cons_tail,
      rw cons_tail,
      refl,
    }
  end

lemma vector.add_comm {n : ℕ} (v1 v2 : vector ℕ n) : v1 + v2 = v2 + v1 := begin
  induction n with n n_ih, {
    simp *,
  }, {
    have hv1 := vector.exists_eq_cons v1,
    have hv2 := vector.exists_eq_cons v2,
    cases hv1 with x,
    cases hv1_h with xs hx,
    cases hv2 with y,
    cases hv2_h with ys hy,
    rw hx,
    rw hy,
    rw vector.cons_add_eq_add_cons,
    rw vector.cons_add_eq_add_cons,
    rw n_ih,
    rw nat.add_comm,
  }
end

lemma vector.zero_add {n : ℕ} (v : vector ℕ n) : 0 + v = v := begin
  rw vector.add_comm,
  rw vector.add_zero,
end

lemma vector.add_assoc {n : ℕ} (v1 v2 v3 : vector ℕ n) : (v1 + v2) + v3 = v1 + (v2 + v3) := begin
  induction n with n n_ih, {
    simp *,
  }, {
    have hv1 := vector.exists_eq_cons v1,
    have hv2 := exists_eq_cons v2,
    have hv3 := exists_eq_cons v3,
    cases hv1 with x,
    cases hv1_h with xs hx,
    cases hv2 with y,
    cases hv2_h with ys hy,
    cases hv3 with z,
    cases hv3_h with zs hz,
    rw [hx, hy, hz],
    rw vector.cons_add_eq_add_cons,
    rw vector.cons_add_eq_add_cons,
    rw vector.cons_add_eq_add_cons,
    rw vector.cons_add_eq_add_cons,
    rw nat.add_assoc,
    rw n_ih,
  }
end

def vector.nsmul {n : ℕ} : ℕ → vector ℕ n → vector ℕ n 
| 0     v := 0
| (x+1) v := v + vector.nsmul x v

instance (n : ℕ) : add_comm_monoid (vector ℕ n) := { 
  add := has_add.add,
  add_assoc := vector.add_assoc,
  zero := repeat 0 n,
  zero_add := vector.zero_add,
  add_zero := vector.add_zero,
  nsmul := vector.nsmul,
  nsmul_zero' := λ x, rfl,
  nsmul_succ' := λ n x, rfl,
  add_comm := vector.add_comm,
}
import tactic.choose
import data.finset.image
import data.finset.lattice
import data.fintype.basic
import data.vector
import data.vector.zip
import data.set.basic
import vector_add_monoid

noncomputable theory

open classical finset set vector

lemma single_preimage {α β : Type*} [decidable_eq β] [decidable_eq α]
  (S : set α) (v' : finset β) (f : α → β) (sub : ↑v' ⊆ f '' S) :
  (∃ (v : finset α), ↑v ⊆ S ∧ finset.image f v = v') :=
begin
  let h := set.mem_image f S,
  let h' : ∀ (y : subtype (f '' S)), ∃ (x : α), x ∈ S ∧ f x = y := begin
    intro y,
    exact (h y.val).mp y.property,
  end,
  choose F hF using axiom_of_choice h',
  let FF : subtype (f '' S) → α := F,
  let v'' : finset (subtype (f '' S)) := @finset.subtype β (f '' S)
                                            (dec_pred (f '' S)) v',
  let v := finset.image FF v'',
  apply exists.intro v,
  apply and.intro, {
    simp *,
    rw set.subset_def,
    intros x _,
    exact (hF x).left,
  }, {
    simp *,
    rw ←coe_inj,
    rw coe_image,
    rw coe_image,
    apply eq_of_subset_of_subset, { 
      simp *,
      intros x hx,
      have hF_x := hF x,
      simp *,
      rw finset.mem_coe at hx,
      rw finset.mem_subtype at hx,
      exact hx,
    }, {
      intros x h_x,
      simp *,
      have x_sub_fS := mem_of_subset_of_mem sub h_x,
      let a := FF ⟨ x, x_sub_fS ⟩,
      existsi a,
      split, {
        existsi x,
        apply and.intro h_x,
        existsi x_sub_fS,
        refl,
      }, {
        exact (hF ⟨ x, x_sub_fS ⟩).right,
      }
    },
  },
end

lemma subtype_axiom_of_choice {α β : Type} {p : α → β → Prop}
  (h : ∀ (a : α), ∃ (b : β), p a b) : Π(a:α), {b // p a b} :=
  begin
    intro a,
    specialize h a,
    choose b hb using h,
    exact ⟨ b, hb ⟩,
  end

def upper_set {n : ℕ} (v : finset (vector ℕ n)) : (set (vector ℕ n)) :=
  {s : vector ℕ n | ∃ (x s' : vector ℕ n) (H : s' ∈ v), s = x + s'}

def P {n : ℕ} (S : set (vector ℕ n)) (v : finset (vector ℕ n)) : Prop := 
    ↑v ⊆ S ∧
      S ⊆ upper_set v

lemma dickson_zero (S : set (vector ℕ 0)) :
  ∃ v : finset (vector ℕ 0), ↑v ⊆ S ∧ S ⊆ upper_set v := begin
  by_cases S.nonempty, {
    cases h with x hx,
    apply exists.intro (finset.has_singleton.singleton x),
    split, {
      rw coe_singleton,
      exact set.singleton_subset_iff.2 hx,
    }, {
      intros s hs,
      rw upper_set,
      existsi [s, x, finset.mem_singleton_self x],
      rw vector.eq_nil s,
      simp,
    }
  }, {
    rw set.not_nonempty_iff_eq_empty at h,
    apply exists.intro ∅,
    split, {
      rw finset.coe_empty,
      exact set.empty_subset _,
    }, {
      rw h,
      exact set.empty_subset _,
    },
  }
end

lemma upper_set_of_empty_eq_empty (n : ℕ) : @upper_set n ∅ = ∅ := begin
  rw upper_set,
  rw ←set.subset_empty_iff,
  intros x hx,
  rcases hx with ⟨ x', s, hs, hx ⟩,
  exfalso,
  exact finset.not_mem_empty s hs,
end

lemma dickson_partition (n M : ℕ) (S : set (vector ℕ n.succ)) :
  S = {s ∈ S | s.head ≥ M} ∪ ⋃(i : fin M), {s ∈ S | i.val = s.head} :=
begin
  apply set.eq_of_subset_of_subset, {
    intros s hs,
    cases nat.decidable_le M s.head, {
      rw not_le at h,
      let i : fin M := ⟨ s.head, h ⟩,
      apply set.mem_union_right,
      rw mem_Union,
      existsi i,
      apply mem_sep hs,
      simp,
    }, {
      apply set.mem_union_left,
      apply mem_sep hs,
      exact h,
    }
  }, {
    intros s hs,
    cases hs, {
      exact (mem_sep_iff.mp hs).left
    }, {
      rw set.mem_Union at hs,
      cases hs with i hs,
      exact (mem_sep_iff.mp hs).left,
    }
  }
end

lemma lift_upperset {n : ℕ} (i : ℕ) (S : set (vector ℕ n.succ))
                    (v : finset (vector ℕ n.succ))
                    (H : (tail '' S) ⊆ upper_set (image tail v))
                    (H2 : ∀ s ∈ S, i ≤ head s)
                    (H3 : ∀ s ∈ v, head s ≤ i) : S ⊆ upper_set v :=
begin
  intros s hs,
  rw upper_set,
  rw mem_set_of_eq,
  have s'_in_S' := mem_image_of_mem tail hs,
  have s'_in_upperset := mem_of_subset_of_mem H s'_in_S',
  rcases s'_in_upperset with ⟨ x',s0', hs0', hs0''⟩,
  rcases finset.mem_image.mp hs0' with ⟨ s0, s0_in_v, hs0 ⟩,
  let x := (head s - head s0) ::ᵥ x',
  existsi [x, s0, s0_in_v],
  rw ←(cons_head_tail s),
  rw eq_comm,
  rw eq_cons_iff,
  split, {
    simp *,
    refine nat.sub_add_cancel _,
    specialize H3 s0 s0_in_v,
    specialize H2 s hs,
    exact le_trans H3 H2,
  }, {
    simp *,
  }
end

theorem dickson (n : ℕ) (S : set (vector ℕ n)) :
  ∃ v : finset (vector ℕ n), ↑v ⊆ S ∧ S ⊆ upper_set v :=
begin
  -- The proof is by induction in n
  induction n with n n_ih, {
    -- The base case is handled in a lemma
    exact dickson_zero S,
  }, { 
    -- Now, let S' = tail(S) and use the induction hypothesis
    -- to find v'
    let S' := image vector.tail S,
    have ih := n_ih S',
    cases ih with v' hv,
    cases hv with v'_sub_S' S'_sub,
    -- Find v s.t. tail(v) = v'
    have ex_v := single_preimage S v' vector.tail v'_sub_S',
    cases ex_v with v,
    cases ex_v_h with v_sub_S tv_eq_v',
    -- We need that v ≠ ∅.
    -- If not, we get that S = ∅
    cases (@finset.decidable_nonempty (vector ℕ n.succ) v),
    {
      -- If v = ∅ then v' = ∅, so S' = ∅, which implies S = ∅. 
      -- When S = ∅, it's easy.
      rw finset.not_nonempty_iff_eq_empty at h,
      apply exists.intro v,
      rw h,
      split, {
        rw finset.coe_empty,
        exact empty_subset S,
      }, {
        rw h at tv_eq_v',
        rw finset.image_empty at tv_eq_v',
        have upper_empty := upper_set_of_empty_eq_empty n,
        rw tv_eq_v' at upper_empty,
        rw upper_empty at S'_sub, 
        rw subset_empty_iff at S'_sub,
        rw set.image_eq_empty at S'_sub,
        rw S'_sub,
        exact empty_subset _,
      }
    }, {
      -- Now that v ≠ ∅, we can find the maximum.
      have image_v_nonempty := finset.nonempty.image h head,
      let M : ℕ := finset.max' (finset.image head v) image_v_nonempty,
      -- Now, partition S into S_gtM and S_i as in the proof.
      let Si := λ (i : (fin M)), ({s ∈ S | i.val = head s}),
      let S_gtM := {s ∈ S | M ≤ head s},
      let S_U := S_gtM ∪ ⋃ i, Si i,
      -- Show that this is actually a partition, using a lemma
      have S_eq_S_U : S = S_U := dickson_partition n M S,
      -- Show that S_gtM ⊆ upper_set v, using a lemma
      have S_gtM'_sub_S' : tail '' S_gtM ⊆ S' := image_subset tail
                                                   (sep_subset S _),
      have c_gtM : S_gtM ⊆ upper_set v := lift_upperset M S_gtM v
        (subset_trans S_gtM'_sub_S' (eq.subst tv_eq_v'.symm S'_sub))
        (λs hs, hs.2) (λs hs, le_max' (image head v) (head s)
                        (mem_image_of_mem head hs)),
      
      -- We use the induction hypothesis to find v_i'
      let t' := λ (i : fin M),  n_ih ((@tail ℕ n.succ) '' (Si i)),
      
      -- For technical reasons, it's easier to define the finite sets
      -- v_i using subtypes.
      -- Thus, vi is a function from fin M to finite sets b, s.t.
      -- b ⊆ Si i and Si i ⊆ upper_set b.
      have vi' := @subtype_axiom_of_choice
                  (fin M)
                  (finset (vector ℕ n))
                  (λ (i : fin M) (v : finset (vector ℕ n)),
                    P ((@tail ℕ n.succ) '' (Si i)) v)
                  t',
      let vi : Π (i : fin M), {b // P (Si i) b} := 
      begin
        intro i,
        let b' := vi' i,
        have P_b' := b'.property,
        cases P_b',
        have ex_b := single_preimage (Si i) b'.val vector.tail P_b'_left,
        choose b hb using ex_b,
        exact ⟨ b, begin
          split, {
            exact hb.1,
          }, {
            rw ←hb.2 at P_b'_right,
            refine lift_upperset i (Si i) b P_b'_right
              (λs hs, le_of_eq hs.2)
              (λs hs, begin exact le_of_eq
                (mem_of_subset_of_mem hb.1 hs).2.symm end),
          }
        end ⟩,
      end,
      -- Then, we can unpack the subtype, to get two functions,
      -- vi_val giving us finite sets and vi_P giving us proofs,
      -- that vi_val i satisfies the proper conditions.
      let vi_val := λ (i : fin M), (vi i).val,
      have vi_P := λ (i : fin M), (vi i).property,
      -- All that work lets us define the finite set V
      let V := v ∪ finset.bUnion (finset.univ) vi_val,
      existsi V,
      -- Now, we have to prove that V ⊆ S and S ⊆ upper_set V
      split, {
        -- V ⊆ S since every constituent of V is a subset of S
        rw coe_union,
        refine union_subset v_sub_S _,
        rw coe_bUnion,
        refine Union_subset _,
        intro i,
        apply Union_subset,
        intro _,
        exact subset_trans (vi_P i).1 (sep_subset S _),
      },{
        -- Now, we prove that S ⊆ upper_set V
        rw S_eq_S_U,
        intro s,
        assume hs,
        cases ((set.mem_union _ _ _).mp hs), {
          -- If s ∈ S_gtM, we use the s', x we know exists since
          -- S_gtM ⊆ upper_set v
          have s_in_upper_v := set.mem_of_subset_of_mem c_gtM h_1,
          rcases s_in_upper_v with ⟨ x, s', s'_in_v, hs' ⟩,
          have s'_in_V : s' ∈ V := finset.mem_union_left _ s'_in_v,
          exact ⟨x, s', s'_in_V, hs'⟩,
        }, {
          -- If s ∈ ⋃Si i, then find the i s.t. s ∈ Si i. 
          rw mem_Union at h_1,
          cases h_1 with i s_in_Si,
          -- Find the right vi and get that Si i ⊆ upper_set vi v
          cases (vi_P i) with vi_sub_Si Si_sub_upper,
          have s_in_upper := set.mem_of_subset_of_mem Si_sub_upper s_in_Si,
          rcases s_in_upper with ⟨ x, s', s'_in_vi, hs' ⟩,
          -- Prove that s' ∈ ⋃vi i, to then prove that s' ∈ V.
          have s'_in_Uvi : s' ∈ (finset.bUnion univ vi_val) := begin
            rw finset.mem_bUnion,
            apply exists.intro i,
            apply exists.intro (finset.mem_univ i),
            exact s'_in_vi,
          end,
          have s'_in_V : s' ∈ V := finset.mem_union_right _ s'_in_Uvi,
          exact ⟨ x, s', s'_in_V, hs' ⟩,
        }
      },
    }
  }
end

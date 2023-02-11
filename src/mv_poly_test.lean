import algebra.monoid_algebra.support
import data.finsupp.antidiagonal
import order.symm_diff
import ring_theory.adjoin.basic
import data.mv_polynomial.basic
import data.nat.order
import data.set
import data.vector.zip
import data.nat.psub

noncomputable theory

open mv_polynomial finsupp finset set vector classical

universes u v w x
variables {R : Type u} [comm_semiring R] [decidable_eq R] {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}
variables {σ : Type*} [fintype σ] [inhabited σ] {e : ℕ} /-{x y : σ}-/ {s s₁ s₂ : σ →₀ ℕ} [decidable_eq σ]

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

variables {M : Type} [has_zero M] [decidable_eq M] {α : Type} [decidable_eq α]

def mv_mon (σ : Type*) : Type* := σ →₀ ℕ 

def my_single (a : α) (b : M) : α →₀ M :=
⟨if b = 0 then ∅ else {a}, pi.single a b, λ a', begin
  obtain rfl | hb := eq_or_ne b 0,
  { simp },
  rw [if_neg hb, finset.mem_singleton],
  obtain rfl | ha := eq_or_ne a' a,
  { simp [hb] },
  simp [pi.single_eq_of_ne', ha],
end⟩

#eval (my_single (1:ℕ) (1:ℕ))

#check (0 : (σ →₀ ℕ))
def my_monomial (s : mv_mon σ) (a : R) : mv_polynomial σ R := single s a

class is_term_order (r : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop) extends is_linear_order (σ →₀ ℕ) r :=
  (zero_le_v : ∀ v : (σ →₀ ℕ), 0 ≤ v)
  (additive : ∀ v v₁ v₂ : (σ →₀ ℕ), v₁ ≤ v₂ → v + v₁ = v + v₂)


def restrict {α : Type*} {β : Type*} (f : α → β) (s : set α) : (subtype s) → β :=
  λ (x : subtype s) , f x


-- Se: https://math.berkeley.edu/~kmill/talks/2020-06-26-lean-seminar.pdf
-- for info om hvordan mængder virker
-- Bem: ↑ staves "\ upa" og coercer et finset eller andet set-like til set.
theorem dickson (S : set (σ → ℕ)) [fin_σ : fintype σ] :
 ∃ v : finset (σ → ℕ), ↑v ⊆ S ∧ S ⊆ {n : (σ → ℕ) | ∃ (n' : σ → ℕ) (v' ∈ S) , n = n' + v'} := 
  begin
    unfreezingI {
      induction fin_σ with fin_σ_s fin_σ_complete,
      induction fin_σ_s using finset.induction_on,

      {
        -- Brug fin_σ_complete og default _inst_4 σ til at få modstrid :)
        -- I stedet for alt det nedenfor.
        apply exists.intro ∅,
        apply and.intro,
        apply set.empty_subset,

        rw set.subset_def,
        intro m,
        intro h,
        rw set.mem_def,
        apply exists.intro,
        swap,
        exact 0,
        apply exists.intro,
        swap,
        exact 0,
        apply exists.intro,

        admit,
        admit,
      },
      {
        rename fin_σ_s_a x,
        rename fin_σ_s_s s_σ,
        rename fin_σ_s_ᾰ x_nin_s_σ,
        rename fin_σ_s_ᾰ_1 hd,

        by_cases ∃ (x' : σ), x ∈ s_σ,
        {
          cases h with x' x'_in_s_σ ,
          
          admit,
        },
        {
          admit
        },

      }
    }
  end


def restrict' {α β : Type*} (p : α → Prop) (f : α → β) : (subtype p) → β :=
  λ (x : subtype p), f ↑x

def generalize {α β : Type*} [has_zero β] (p : α → Prop) (f : subtype p → β) : (α → β) :=
  λ (x : α),
    have decidable (p x), from prop_decidable (p x),
  @dite β(p x)(prop_decidable (p x)) (λ t, f ⟨ x, t ⟩ ) (λ f, 0)


-- instance (n : ℕ) : has_add (vector ℕ n) :=
--   ⟨ λ v1 v2, sorry ⟩

lemma zip_with_head {α β γ : Type*} {n : ℕ} (f : α → β → γ) (x : vector α n.succ) (y : vector β n.succ) :
  (vector.zip_with f x y).head = f (x.head) (y.head) := begin
    rw ←nth_zero,
    rw ←nth_zero,
    rw ←nth_zero,
    exact (zip_with_nth f x y 0),
  end

def single_preimage {α β : Type*} [decidable_eq β] [decidable_eq α] (S : set α) (v' : finset β) (f : α → β) (sub : ↑v' ⊆ f '' S)
  (h : ∀ (y : β), y ∈ f '' S ↔ ∃ (x : α), x ∈ S ∧ f x = y) :
  (∃ (v : finset α), ↑v ⊆ S ∧ finset.image f v = v') :=
begin
  let h' : ∀ (y : subtype (f '' S)), ∃ (x : α), x ∈ S ∧ f x = y := begin
    intro y,
    exact (h y.val).mp y.property,
  end,
  let F' : ∃ (f_1 : Π (x : subtype (f '' S)), α), ∀ (x : subtype (f '' S)), (λ (y : subtype (f '' S)) (x : α), x ∈ S ∧ f x = ↑y) x (f_1 x) := axiom_of_choice h',
  choose F hF using axiom_of_choice h',
  let FF : subtype (f '' S) → α := F,
  let v'' : finset (subtype (f '' S)) := @finset.subtype β (f '' S) (dec_pred (f '' S)) v',
  let v := finset.image FF v'',
  apply exists.intro v,
  apply and.intro, {
    simp *,
    rw set.subset_def,
    intro x,
    assume h_x,
    have h_Fx := hF x,
    exact h_Fx.left,
  }, {
    simp *,
    rw ←coe_inj,
    rw coe_image,
    rw coe_image,
    apply eq_of_subset_of_subset, {
    simp *,
    intro x,
    assume h_x,
    have hF_x := hF x,
    simp *,
    rw finset.mem_coe at h_x,
    rw finset.mem_subtype at h_x,
    exact h_x,
    }, {
      intro x,
      simp *,
      assume h_x,
      have x_sub_fS := mem_of_subset_of_mem sub h_x,
      let a := FF ⟨ x, x_sub_fS ⟩,
      apply exists.intro a,
      apply and.intro,
      apply exists.intro x,
      apply and.intro h_x,
      apply exists.intro,
      trivial,
      exact x_sub_fS,
      exact (hF ⟨ x, x_sub_fS ⟩).right,
    },
  },
end

lemma single_choice {α : Type*} {p : α → Prop} (h : ∃ (a : α), p a) : {a // p a} := begin
  choose b hb using h,
  exact ⟨ b, hb ⟩,
end

lemma exists_implies_commute {α β : Type} {p : α → β → Prop}
  (f : ∀ (a: α), ∃ (b : β), p a b) : (∃ (f : Π(a:α), {b // p a b}), true) :=
  begin
    apply exists.intro,
    intro a,
    have h := f a,
    choose b hb using h,
    exact ⟨ b, hb ⟩,
    exact true.intro,
  end

def upper_set (n : ℕ) (v : finset (vector ℕ n)) : (set (vector ℕ n)) :=
  {x : vector ℕ n | ∃ (x' s : vector ℕ n) (H : s ∈ v), x = zip_with (+) x' s}


def P (n : ℕ) (S : set (vector ℕ n)) (v : finset (vector ℕ n)) : Prop := 
    ↑v ⊆ S ∧
      S ⊆ upper_set n v


theorem set_dickson (n : ℕ) (S : set (vector ℕ n)) :
  -- ∃ v : finset (vector ℕ n), ↑v ⊆ S ∧ S ⊆ {x : vector ℕ n | ∃ (x' : vector ℕ n) (s ∈ v) , x = vector.zip_with (+) x' s} :=
  ∃ v : finset (vector ℕ n), ↑v ⊆ S ∧ S ⊆ upper_set n v :=
  begin
  unfreezingI {
    induction n, {
      by_cases S.nonempty, {
        cases h,
        apply exists.intro (finset.has_singleton.singleton h_w),
        split, {
          intro s,
          assume hs,
          rw finset.mem_coe at hs,
          have s_eq_w : s = h_w := finset.eq_of_mem_singleton hs,
          rw s_eq_w,
          exact h_h,
        }, {
          intro s,
          assume hs,
          apply exists.intro s,
          apply exists.intro h_w,
          apply exists.intro (finset.mem_singleton_self h_w),
          rw vector.eq_nil s,
          rw vector.eq_nil (zip_with has_add.add nil h_w),
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
    }, { 
      let S' := image vector.tail S,
      -- have S'_eq_tail_S : S' = image vector.tail S := rfl,
      -- rewrite nat.succ_sub_one at S',
      have ih := n_ih S',
      cases ih with v' hv,
      cases hv with v'_sub_S' S'_sub,
      have h := set.mem_image vector.tail S,
      have ex_v := single_preimage S v' vector.tail v'_sub_S' h,
      cases ex_v with v,
      cases ex_v_h with v_sub_S tv_eq_v',
      cases (@finset.decidable_nonempty (vector ℕ n_n.succ) v),
      {
        -- v er tom, dvs v' er tom så S' er tom så S er tom. Vis det, buddy.
        rw finset.not_nonempty_iff_eq_empty at h_1,
        apply exists.intro v,
        rw h_1,
        split, {
          rw finset.coe_empty,
          exact empty_subset S,
        }, {
          have upper_empty : (upper_set n_n v') = ∅ := begin
            rw ←set.subset_empty_iff,
            rw ←tv_eq_v',
            rw h_1,
            intro s,
            assume hs,
            cases hs,
            cases hs_h,
            cases hs_h_h,
            rw finset.image_empty at hs_h_h_w,
            exfalso,
            exact finset.not_mem_empty _ hs_h_h_w,
          end,
          rw upper_empty at S'_sub, 
          rw subset_empty_iff at S'_sub,
          rw set.image_eq_empty at S'_sub,
          rw S'_sub,
          exact empty_subset _,
        }
      }, {
        have image_v_nonempty := finset.nonempty.image h_1 head,
        let M : ℕ := finset.max' (finset.image head v) image_v_nonempty,
        let Si := λ (i : (fin M)), ({s ∈ S | i.val = head s}),
        let S_gtM := {s ∈ S | M ≤ head s},
        let S_U := S_gtM ∪ ⋃ i, Si i,
        have S_eq_S_U : S = S_U := begin
          apply set.eq_of_subset_of_subset, {
            assume s,
            assume s_in_S : s ∈ S,
            cases nat.decidable_le M (head s),
            {
              rw not_le at h_2,
              -- Find ud af hvilket Si i, s skal tilhøre
              let i : fin M := ⟨ s.head, h_2 ⟩,
              apply mem_union_right S_gtM,
              rw mem_Union,
              apply exists.intro, swap,
              exact i,
              apply set.mem_sep,
              exact s_in_S,
              refl,
            }, {
              apply mem_union_left ⋃ (i : fin M), Si i,
              exact mem_sep s_in_S h_2,
            }
          }, {
            assume s,
            assume s_in_S_U : s ∈ S_U,
            rw set.mem_union at s_in_S_U,
            cases s_in_S_U,
            {
              exact (mem_sep_iff.mp s_in_S_U).left,
            }, {
              rw set.mem_Union at s_in_S_U,
              cases s_in_S_U with i hs,
              rw mem_sep_iff at hs,
              exact hs.left,
            }
          }
        end,
        
          rw S_eq_S_U,
          let t' :=
            λ (i : fin M),  n_ih ((@tail ℕ n_n.succ) '' (Si i)),
          have t := (@exists_implies_commute
                     (fin M)
                      (finset (vector ℕ n_n))
                      (λ (i : fin M) (v : finset (vector ℕ n_n)),
                        P n_n ((@tail ℕ n_n.succ) '' (Si i)) v)) t',
          cases t,
          -- have t_w0 := (t_w 0).val,
          have t_w_finset := λ (a : fin M), (t_w a).val,
          have c_gtM : S_gtM ⊆ upper_set n_n.succ v := 
          begin
            intro s,
            assume h_s,
            rw upper_set,
            rw mem_set_of_eq,
            cases h_s with h_s_in_S h_M_leq_s_head,
            have s_in_S_gtM : s ∈ S_gtM := mem_sep h_s_in_S h_M_leq_s_head, 
            let s' := tail s,
            have s'_sub_S' : s' ∈ tail '' S := mem_image_of_mem tail h_s_in_S,
            have s'_sub_upperset : s' ∈ upper_set n_n v' := mem_of_subset_of_mem S'_sub s'_sub_S',
            choose x' hx' using s'_sub_upperset,
            choose s0' hs0' using hx',
            cases hs0',
            have s0'_in_S' : s0' ∈ S' := mem_of_subset_of_mem v'_sub_S' hs0'_left,
            rw ←tv_eq_v' at hs0'_left,
            choose s0 hs0 using finset.mem_image.mp hs0'_left,
            let s_head_diff := (head s) - (head s0),
            rw tv_eq_v' at hs0'_left,
            let x : vector ℕ n_n.succ := (head s - head s0) ::ᵥ x',
            apply exists.intro x,
            apply exists.intro s0,
            apply exists.intro hs0.left,
            have s_eq_head_tail : s.head ::ᵥ s.tail = s := cons_head_tail s,
            rw ←s_eq_head_tail,
            rw eq_comm,
            rw eq_cons_iff,
            apply and.intro,{
              rw zip_with_head,
              rw head_cons,
              have s0_head : s0.head ∈ (finset.image head v) :=
                mem_image_of_mem head hs0.left,
              have s0_leq_M : s0.head ≤ M :=
                le_max' (image head v) (head s0) s0_head,
              have s0_leq_s_heads : s0.head ≤ s.head := has_le.le.trans s0_leq_M h_M_leq_s_head,
              rw (nat.sub_add_cancel s0_leq_s_heads),
            },{
              rw (zip_with_tail (+) x s0),
              rw hs0.right,
              rw (tail_cons s_head_diff x'),
              rw eq_comm,
              exact hs0'_right,
            },
          end,
          let vi : Π (i : fin M), {b // P n_n.succ (Si i) b} := 
          begin
            intro i,
            let b' := t_w i,
            have P_b' := b'.property,
            cases P_b',
            have Si_sub_S : (Si i) ⊆ S := begin
              intro s,
              assume hs,
              rw S_eq_S_U,
              apply set.mem_union_right,
              exact set.mem_Union_of_mem i hs,
            end,
            have ex_b := single_preimage (Si i) b'.val vector.tail P_b'_left (set.mem_image vector.tail (Si i)),
            choose b hb using ex_b,
            exact ⟨ b, begin
              split, {
                exact hb.left,
              }, {
                intro s,
                assume hs,
                unfold upper_set,
                let s' := tail s,
                have s'_in_Si' : s' ∈ tail '' Si i := mem_image_of_mem tail hs,
                have s'_in_upper : s' ∈ upper_set n_n b'.val := mem_of_subset_of_mem P_b'_right s'_in_Si',
                rw mem_set_of_eq,
                choose x' hx' using s'_in_upper,
                choose s0' hs0' using hx',
                cases hs0',
                have s0'_in_Si' : s0' ∈ (tail '' (Si i)) := mem_of_subset_of_mem P_b'_left hs0'_left,
                rw ←hb.right at hs0'_left,
                choose s0 hs0 using finset.mem_image.mp hs0'_left,
                rw hb.right at hs0'_left,
                let x : vector ℕ n_n.succ := 0 ::ᵥ x',
                apply exists.intro x,
                apply exists.intro s0,
                apply exists.intro hs0.left,
                rw ←(cons_head_tail s),
                rw eq_comm,
                rw eq_cons_iff,
                apply and.intro,{
                  rw zip_with_head,
                  rw head_cons,
                  rw nat.zero_add,
                  have s_head_eq_i : i.val = s.head := (mem_sep_iff.mp hs).right,
                  have s0_in_Si : s0 ∈ (Si i) := mem_of_subset_of_mem hb.left hs0.left,
                  have s0_head_eq_i : i.val = s0.head := (mem_sep_iff.mp s0_in_Si).right,
                  rw ←s_head_eq_i,
                  rw ←s0_head_eq_i,
                },{
                  rw (zip_with_tail (+) x s0),
                  rw hs0.right,
                  rw (tail_cons 0 x'),
                  rw eq_comm,
                  exact hs0'_right,
                },
              }
            end ⟩,
         end,
          let vi_val := λ (i : fin M), (vi i).val,
          have vi_P : Π (i:fin M), (P n_n.succ (Si i) (vi_val i)) := λ (i : fin M), (vi i).property,
          let V := v ∪ finset.bUnion (finset.univ) vi_val,
          apply exists.intro V,
          apply and.intro, {
            intro s,
            assume hs,
            rw mem_coe at hs,
            rw finset.mem_union at hs,
            cases hs, {
              rw ←finset.mem_coe at hs,
              rw ←S_eq_S_U,
              exact set.mem_of_subset_of_mem v_sub_S hs,
            }, {
              rw finset.mem_bUnion at hs,
              cases hs with i hs,
              cases hs with i_in_univ s_in_vi,
              have Ps := vi_P i,
              cases Ps,
              rw ←finset.mem_coe at s_in_vi,
              apply set.mem_union_right _ _,
              have s_in_Si : s ∈ (Si i) := mem_of_subset_of_mem Ps_left s_in_vi,
              exact mem_Union_of_mem i s_in_Si,
            }
          },{
            intro s,
            assume hs,
            cases ((set.mem_union _ _ _).mp hs), {
              have s_in_upper_v := set.mem_of_subset_of_mem c_gtM h_2,
              cases s_in_upper_v with x hx,
              apply exists.intro x,
              cases hx with s_1 hs_1,
              cases hs_1,
              have s_1_in_V : s_1 ∈ V := finset.mem_union_left _ hs_1_w,
              apply exists.intro s_1,
              apply exists.intro s_1_in_V,
              exact hs_1_h,
            }, {
              rw mem_Union at h_2,
              cases h_2 with i s_in_Si,
              have hi := vi_P i,
              cases (vi_P i) with vi_sub_Si Si_sub_upper,
              have s_in_upper := set.mem_of_subset_of_mem Si_sub_upper s_in_Si,
              cases s_in_upper with x hx,
              apply exists.intro x,
              cases hx with s_1 hs_1,
              cases hs_1,
              have s_1_in_Uvi : s_1 ∈ (finset.bUnion univ vi_val) := begin
                rw finset.mem_bUnion,
                apply exists.intro i,
                apply exists.intro (finset.mem_univ i),
                exact hs_1_w,
              end,
              have s_1_in_V : s_1 ∈ V := finset.mem_union_right _ s_1_in_Uvi,
              apply exists.intro s_1,
              apply exists.intro s_1_in_V,
              exact hs_1_h,
            }
          },
      }
    }
  }
  end

#check set_dickson
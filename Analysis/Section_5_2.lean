import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.closeSeq_def]
  intro a h1 h2
  rw [Rat.Close]
  simp_all
  set n := a.toNat
  calc |(-1:ℚ)^n - 1.1 * (-1)^n| = |(1 - 1.1) * (-1)^n| := by grind
    _ = 0.1 * |(-1)^n| := by grind
    _ = 0.1 := by grind [abs_neg_one_pow]
    _ ≤ 0.1 := by simp

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  by_contra h
  rw [Rat.Steady] at h
  specialize h 0 (by simp) 1 (by simp)
  rw [Rat.Close] at h
  simp at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  by_contra h
  rw [Rat.Steady] at h
  specialize h 0 (by simp) 1 (by simp)
  rw [Rat.Close] at h
  simp at h
  norm_num at h

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [eventuallyClose_def]
  constructor
  . intro h
    obtain ⟨ m, hm ⟩ := h
    rw [Rat.closeSeq_def] at hm
    let m' := max ((a:Sequence).from m).n₀ ((b:Sequence).from m).n₀

    use m'.toNat
    intro n hn
    have hn1: n ≥ m' := by grind
    specialize hm n (by grind) (by grind)
    rw [Rat.Close] at hm
    simp at hm

    have: ((a:Sequence).from m).n₀ ≥ m := by grind
    simp [show n ≥ m by grind] at hm
    exact hm
  . intro h
    obtain ⟨ m, hm ⟩ := h
    use m
    rw [Rat.closeSeq_def]
    intro n h1 h2
    rw [Rat.Close]
    simp [show n ≥ m by grind]
    simp [show n ≥ 0 by grind]
    specialize hm n.toNat (by grind)
    exact hm

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by

  by_contra h
  rw [Rat.closeSeq_def] at h
  simp at h

  specialize h 0 (by simp)
  rw [Rat.Close] at h
  simp at h
  norm_num at h

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by

  rw [Rat.eventuallyClose_iff]
  simp
  use 1
  intro n hn

  set M := (10:ℚ) ^ (-(n:ℤ) - 1)

  have: M ≥ 0 := by positivity
  have: M ≤ 10 ^ (-2:ℤ) := by
    apply zpow_le_zpow_right₀ (show (1:ℚ) ≤ 10 by norm_num) (show -(n:ℤ) - 1 ≤ -(2:ℤ) by linarith)

  grind

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by

  rw [Rat.eventuallyClose_iff]
  simp
  use 2
  intro n hn

  set M := (10:ℚ) ^ (-(n:ℤ) - 1)

  have: M ≥ 0 := by positivity
  have: M ≤ 10 ^ (-3:ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num: (1:ℚ) ≤ 10) (by linarith: -(n:ℤ) - 1 ≤ -(3:ℤ))

  grind

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [equiv_def]
  constructor
  . intro h ε hε
    rw [←Rat.eventuallyClose_iff]
    specialize h ε hε
    exact h
  . intro h ε hε
    rw [Rat.eventuallyClose_iff]
    specialize h ε hε
    exact h

lemma Sequence.equiv_symm (a b: ℕ → ℚ) : Equiv a b ↔ Equiv b a := by

  rw [equiv_iff, equiv_iff]

  constructor
  . intro h ε hε
    specialize h ε hε
    obtain ⟨ N, hN ⟩ := h
    use N
    grind [abs_sub_comm]
  . intro h ε hε
    specialize h ε hε
    obtain ⟨ N, hN ⟩ := h
    use N
    grind [abs_sub_comm]

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

private lemma Sequence.isCauchy_of_equiv_aux {a b: ℕ → ℚ} (hab: Equiv a b) :
  (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by

  rw [Sequence.equiv_def] at hab
  rw [isCauchy_def, isCauchy_def]
  intro ha ε hε
  specialize hab (ε / 3) (by linarith)
  specialize ha (ε / 3) (by linarith)

  obtain ⟨ N1, hN1 ⟩ := hab
  obtain ⟨ N2, ⟨hN20, hna ⟩⟩ := ha

  rw [Rat.CloseSeq] at hN1

  rw [Rat.Steady] at hna

  let M1 := max ((a:Sequence).from N1).n₀ ((b:Sequence).from N1).n₀
  let M2 := max ((a:Sequence).from N2).n₀ ((b:Sequence).from N2).n₀
  -- let M := max M1 M2

  let M := max (max M1 M2) 0

  rw [Rat.EventuallySteady]
  use M
  -- M = max (0, N1, N2)
  have hm1: M ≥ 0 := by grind [Sequence.ofNatFun]

  simp [hm1]
  rw [Rat.steady_def]
  simp [hm1]
  intro i hi j hj

  have hni := hN1 i (by grind) (by grind)
  have hnj := hN1 j (by grind) (by grind)
  specialize hna i (by grind) j (by grind)

  rw [Rat.Close] at hni hnj hna ⊢

  have hipos: i ≥ 0 := by grind
  have hjpos: j ≥ 0 := by grind
  simp [hipos, hjpos] at hni hnj hna ⊢

  simp [hi, hj]

  simp [show i ≥ N1 by grind] at hni
  simp [show j ≥ N1 by grind] at hnj
  simp [show i ≥ N2 by grind, show j ≥ N2 by grind] at hna

  set ai := a i.toNat
  set aj := a j.toNat
  set bi := b i.toNat
  set bj := b j.toNat

  -- have: bi - bj = bi - ai + ai - aj + aj - bj := by grind
  have hend: |bi - bj| ≤ |bi - ai| + |ai - aj| + |aj - bj| := by grind

  -- have: |bi - bj| ≤ 3 * (ε / 3) := by grind
  grind

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by

  have hba : Equiv b a := by rwa [Sequence.equiv_symm] at hab

  exact ⟨isCauchy_of_equiv_aux hab, isCauchy_of_equiv_aux hba⟩

private lemma Sequence.bounded_close_aux {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded → (b:Sequence).IsBounded := by

  rw [IsBounded, IsBounded]
  rw [Rat.eventuallyClose_iff] at hab
  intro ha
  obtain ⟨ M1, ⟨ha1, ha2 ⟩⟩ := ha
  obtain ⟨ N, hab1 ⟩ := hab

  -- b_0_N = b.0 ~ .N
  set b_0_N : Fin N → ℚ := fun n ↦ b n
  choose M2 hM2 hM2Bound using IsBounded.finite b_0_N

  set Up := M1 + M2 + |ε|
  use Up
  simp [show Up ≥ 0 by positivity]
  rw [BoundedBy]
  intro idx
  by_cases h0: idx < 0
  . have: (b:Sequence).n₀ = 0 := by grind [Sequence.ofNatFun]
    rw [(b:Sequence).vanish idx (by grind)]
    simp; grind
  . push_neg at h0
    -- lift idx to ℕ using h0
    by_cases h_idx: idx ≥ N
    . -- b.N ~ ...
      simp [h0]
      specialize hab1 idx.toNat (by grind)
      rw [BoundedBy] at ha2
      specialize ha2 idx
      simp [h0] at ha2
      grind
    . -- b.0 ~ b.N
      push_neg at h_idx
      unfold Chapter5.BoundedBy at hM2Bound

      specialize hM2Bound ⟨idx.toNat, by grind⟩
      simp [h0]
      grind

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by

  have hba: ε.EventuallyClose b a := by
    rw [Rat.eventuallyClose_iff] at hab ⊢
    obtain ⟨m, h1⟩ := hab
    use m
    grind

  exact ⟨bounded_close_aux hab, bounded_close_aux hba⟩

end Chapter5

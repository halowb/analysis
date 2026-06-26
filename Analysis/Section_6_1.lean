import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $`ε`-closeness, $`ε`-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℝ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from {lean}`ℕ` to {lean}`ℝ` can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  {given -show}`n₁, n₀`
  {lean}`a.from n₁` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed {name}`a`, the function `ε ↦ ε.Steady s` is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed {name}`a`, the function `ε ↦ ε.EventuallySteady s` is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as {name}`Chapter5.Sequence.IsCauchy.coe` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by

  rw [Rat.steady_def, Real.steady_def]
  have ha: a.n₀ = (a:Sequence).m := by rfl
  constructor
  . rw [ha]
    intros h n hn m hm
    specialize h n hn m hm
    rw [Rat.Close] at h; simp; rw [Rat.dist_eq]
    have : (|a.seq n - a.seq m|:ℝ) ≤ (ε:ℝ) := by norm_cast
    grind
  . rw [ha]
    intros h n hn m hm
    specialize h n hn m hm
    rw [Rat.Close]
    simp at h; rw [Rat.dist_eq] at h
    norm_cast at h

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by

  rw [Rat.eventuallySteady_def, Real.eventuallySteady_def]
  have ha: a.n₀ = (a:Sequence).m := by rfl
  rw [ha]
  constructor
  . intro h
    choose M hM1 hM2 using h
    use M
    have : (a.from M) = ((a:Sequence).from M) := by grind
    rw [←this]
    grind [Sequence.is_steady_of_rat ε (a.from M)]
  . intro h
    choose M hM1 hM2 using h
    use M
    have : (a.from M) = ((a:Sequence).from M) := by grind
    rw [←this] at hM2
    grind [Sequence.is_steady_of_rat ε (a.from M)]

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by

  rw [tendsTo_def]; simp [Real.EventuallyClose, Real.CloseSeq, Real.dist_eq]
  simp_all

  constructor
  . intro h ε hε
    specialize h ε hε
    choose N h1 h2 using h
    use N
    intro M hM
    specialize h2 M
    simp [show a.m ≤ M by linarith, hM] at h2
    exact h2
  . intro h ε hε
    specialize h ε hε
    choose N h1 using h
    use max a.m N
    simp
    intro n hn1 hn2
    specialize h1 n
    simp [hn2] at h1
    exact h1

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  rw [Real.EventuallyClose];
  use 1
  simp [show seq_6_1_6.m = 0 by rfl]
  rw [seq_6_1_6, Real.CloseSeq]; simp [Real.dist_eq]
  intro n hn
  simp [hn, show n ≥ 0 by linarith]
  rw [show (1e-2:ℝ) = (10:ℝ)^(-2:ℤ) by norm_num]
  gcongr <;> grind

/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  rw [Sequence.tendsTo_def]
  have h1: seq_6_1_6.m = 0 := by rfl
  intro ε hε
  rw [Real.EventuallyClose, h1]
  choose N hN using exists_nat_gt (1 / ε)
  field_simp at hN
  use N+1
  rw [Real.CloseSeq, show (seq_6_1_6.from (N+1)).m = (N+1) by rfl]
  simp [Real.dist_eq, h1, show ((N:ℤ) + 1) ≥ 0 by positivity]
  intro n hn
  have hnN : (N:ℝ) < (n:ℝ) := by norm_cast
  simp [seq_6_1_6, hn, show n ≥ 0 by linarith]

  have: (10:ℝ)^(-n - 1) = 1 / (10:ℝ)^(n+1) := by
    rw [show -n - 1 = -(n + 1) by ring]
    rw [zpow_neg]
    grind

  rw [this]; field_simp;

  have := Nat.lt_pow_self (a:=10) (n:=(n+1).toNat) (by omega)
  simp at this
  have h2: (n + 1) < (10:ℝ)^(n+1).toNat  := by exact_mod_cast this
  have : (10:ℝ)^(n+1).toNat = (10:ℝ)^(n+1) := by grind [zpow_natCast]
  rw [this] at h2

  have: (10:ℝ) ^ (n + 1) * ε > 1 := by
    calc _ > (n+1) * ε := by gcongr
      _ > n * ε := by grind
      _ > N * ε := by gcongr
      _ > 1 := by linarith

  grind

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of {lean}`0` if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  rw [Convergent] at h
  obtain ⟨L, hL⟩ := h
  rw [Sequence.tendsTo_def] at hL
  rw [IsCauchy]
  intro ε hε
  obtain ⟨N, hN, hN2⟩ := hL (ε/2) (by positivity)
  rw [Real.CloseSeq] at hN2; simp [Real.dist_eq] at hN2

  rw [Real.eventuallySteady_def]
  use N; simp [hN]
  rw [Real.steady_def]
  intro n hn m hm
  simp [Real.dist_eq, hn, hm]

  have hn' := hN2 n (by grind) (by grind)
  simp [show n ≥ a.m by grind, show n ≥ N by grind] at hn'
  have hm' := hN2 m (by grind) (by grind)
  simp [show m ≥ a.m by grind, show m ≥ N by grind] at hm'

  grind

/-- Example 6.1.13 -/
private lemma Ex6_1_13: ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  rw [Real.EventuallySteady]
  by_contra h
  obtain ⟨N, hN⟩ := h
  have h2 := hN.right
  rw [Real.steady_def] at h2
  let n' := (((fun n ↦ (-1:ℝ) ^ n):Sequence).from N).m

  specialize h2 n' (by omega) (n'+1) (by omega)
  simp [Real.dist_eq] at h2

  have hn1: n' ≥ 0 := by grind
  have hn2: n' ≥ N := by grind
  have: n' + 1 ≥ 0 := by grind
  have: n' + 1 ≥ N := by grind

  simp_all

  clear_value n'
  lift n' to ℕ using hn1
  simp at h2

  rw [pow_add (a:=-1)] at h2
  simp at h2
  rw [←mul_two, abs_mul] at h2

  have: |(-1:ℝ) ^ n'| = 1 := by simp [abs_pow (-1:ℝ) n']
  rw [this] at h2; simp at h2
  linarith

/-- Example 6.1.13 -/
private lemma Ex6_1_13_cauchy : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy]
  by_contra h
  specialize h (0.1:ℝ) (by positivity)
  have := Ex6_1_13
  contradiction

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  by_contra h
  have := Sequence.IsCauchy.convergent h
  have := Ex6_1_13_cauchy
  contradiction

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by sorry

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

-- finitie sequences are bounded
abbrev BoundedBy {n:ℕ} (a: Fin n → ℝ) (M:ℝ) : Prop := ∀ i, |a i| ≤ M
-- copy/pasted the proof 6.1.16

lemma IsBounded.finite {n:ℕ} (a: Fin n → ℝ) : ∃ M ≥ 0, BoundedBy a M := by
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℝ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [isBounded_def]

  rw [Sequence.IsCauchy] at h
  specialize h 1 (by norm_num)
  obtain ⟨N, hN, hNClose⟩ := h
  rw [Real.steady_def] at hNClose
  specialize hNClose N (by grind)

  obtain ⟨M, hM, hMBound⟩ := IsBounded.finite (n:= (N - a.m).toNat) (fun n ↦ a (a.m + n))

  let M' := max M (|a.seq N| + 1)
  use M'
  simp [Sequence.boundedBy_def, show M' ≥ 0 by grind]

  intro idx

  by_cases hidx: idx < a.m
  . -- vanish
    rw [a.vanish idx (by grind)]
    simp; grind
  . push_neg at hidx
    by_cases hidx_N: idx ≥ N
    . -- a.N ~ ...
      specialize hNClose idx (by grind)
      rw [Real.Close, Real.dist_eq] at hNClose
      simp [hN, hidx_N] at hNClose
      grind
    . -- a.m ~ a.N
      push_neg at hidx_N
      rw [Chapter6.BoundedBy] at hMBound
      specialize hMBound ⟨(idx - a.m).toNat, by grind⟩
      grind

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  have hcauchy := Sequence.IsCauchy.convergent h
  exact Sequence.bounded_of_cauchy hcauchy

/-- Example 6.1.18 -/
private lemma Ex6_1_18_Bound : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  rw [Sequence.IsBounded]
  by_contra h
  obtain ⟨M, hM, hMBound⟩ := h
  rw [Sequence.boundedBy_def] at hMBound
  choose N hN using exists_nat_gt M

  specialize hMBound N
  simp at hMBound
  grind

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  by_contra h
  have := Sequence.bounded_of_convergent h
  have := Ex6_1_18_Bound
  contradiction

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by

  rw [Sequence.TendsTo] at *
  intros ε hε
  specialize ha (ε/2) (by positivity)
  specialize hb (ε/2) (by positivity)
  obtain ⟨N1, hN1, hClose1⟩ := ha
  obtain ⟨N2, hN2, hClose2⟩ := hb
  let N := max N1 N2
  use N
  have: N ≥ (a+b).m := by
    have: (a + b).m = min a.m b.m := by rfl
    grind
  simp [this]
  rw [Real.closeSeq_def] at *
  simp [Real.dist_eq] at *
  simp_all
  intro n hn1 hn2
  specialize hClose1 n (by grind) (by grind)
  specialize hClose2 n (by grind) (by grind)
  grind

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have h1 := Sequence.tendsTo_add hL hM

  constructor
  . use L + M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    have hmb:= (Sequence.lim_eq).mp hM
    grind

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by

  rw [Sequence.TendsTo] at *

  have h_lemma {ε:ℝ} (hε: ε > 0) (h1: ε ≤ 1) : ε.EventuallyClose (a * b) (L * M) := by
    specialize ha (ε/((|M|+1) * 3)) (by positivity)
    specialize hb (ε/((|L|+1) * 3)) (by positivity)
    obtain ⟨N1, hN1, hClose1⟩ := ha
    obtain ⟨N2, hN2, hClose2⟩ := hb
    let N := max N1 N2
    use N
    have: N ≥ (a*b).m := by
      have: (a*b).m = min a.m b.m := by rfl
      grind
    simp [this]
    rw [Real.closeSeq_def] at *
    simp [Real.dist_eq] at *
    simp_all
    intro n hn1 hn2
    specialize hClose1 n (by grind) (by grind)
    specialize hClose2 n (by grind) (by grind)

    set ta := a.seq n - L
    set tb := b.seq n - M

    set S := |a.seq n * b.seq n - L * M|

    have : S = |ta * tb + ta * M + tb * L| := by grind
    have : S ≤ |ta * tb| + |ta * M| + |tb * L| := by grind

    have: |ta * M| < ε/3 := by
      calc _ = |ta| * |M| := by grind
        _ ≤ ε / ((|M| + 1) * 3) * |M| := by gcongr
        _ < ε / 3 := by field_simp; linarith

    have: |tb * L| < ε/3 := by
      calc _ = |tb| * |L| := by grind
        _ ≤ ε / ((|L| + 1) * 3) * |L| := by gcongr
        _ < ε / 3 := by field_simp; linarith

    have: |ta| ≤ ε/3 := by
      calc _ ≤ ε / ((|M| + 1) * 3) := hClose1
        _ ≤ ε / 3 := by field_simp; grind

    have: |tb| ≤ 1 := by
      calc _ ≤ ε / ((|L| + 1) * 3) := hClose2
        _ ≤ 1 := by field_simp; grind

    have: |ta * tb| ≤ ε/3 := by
      calc _ = |ta| * |tb| := by grind
        _ ≤ ε / 3 * 1 := by gcongr
        _ = ε / 3 := by grind

    grind

  intros ε hε

  by_cases h1: ε ≤ 1
  . exact h_lemma hε h1
  . have := h_lemma (ε := 1) (by norm_num) (by norm_num)
    exact Real.EventuallyClose.mono (a:=a*b) (ε₁:= 1) (ε₂:= ε) (L := L*M) (by linarith) this

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have h1 := Sequence.tendsTo_mul hL hM

  constructor
  . use L * M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    have hmb:= (Sequence.lim_eq).mp hM
    grind

instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by

  rw [Sequence.TendsTo] at *
  intros ε hε
  specialize ha (ε/(|c|+1)) (by positivity)
  rw [Real.eventuallyClose_def] at *
  obtain ⟨N, hN, hClose⟩ := ha
  use N
  have heq: (c • a).m = a.m := by rfl
  simp [show N ≥ (c • a).m by grind]
  rw [Real.closeSeq_def] at *
  simp [Real.dist_eq] at *
  intros n hn1 hn2
  specialize hClose n (by grind) (by grind)
  simp [hn2, show n ≥ a.m by grind] at hClose
  simp [hn1, hn2]
  calc _ = |c * (a.seq n -  L)| := by grind
    _ = |c| * |a.seq n -  L| := by grind
    _ ≤ |c| * (ε / (|c| + 1)) := by gcongr
    _ ≤ ε := by field_simp; linarith

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by

  rw [Sequence.Convergent] at *
  obtain ⟨L, hL⟩ := ha

  have h1 := Sequence.tendsTo_smul c hL

  constructor
  . use c * L
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    grind

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by

  rw [Sequence.TendsTo] at *
  intros ε hε
  specialize ha (ε/2) (by positivity)
  specialize hb (ε/2) (by positivity)
  obtain ⟨N1, hN1, hClose1⟩ := ha
  obtain ⟨N2, hN2, hClose2⟩ := hb
  let N := max N1 N2
  use N
  have: N ≥ (a-b).m := by
    have: (a-b).m = min a.m b.m := by rfl
    grind
  simp [this]
  rw [Real.closeSeq_def] at *
  simp [Real.dist_eq] at *
  simp_all
  intro n hn1 hn2
  specialize hClose1 n (by grind) (by grind)
  specialize hClose2 n (by grind) (by grind)
  grind

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have h1 := Sequence.tendsTo_sub hL hM

  constructor
  . use L - M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    have hmb:= (Sequence.lim_eq).mp hM
    grind

noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by

  rw [Sequence.TendsTo] at *

  have h_lemma {ε:ℝ} (hε: ε > 0) (h1: ε ≤ 1 / |L|) : ε.EventuallyClose a⁻¹ L⁻¹ := by
    field_simp at h1
    specialize ha (ε* |L| * |L| / 2) (by positivity)

    obtain ⟨N, hN, hClose⟩ := ha

    use N

    have: (a⁻¹).m = a.m := by rfl
    simp [show N ≥ (a⁻¹).m by grind]

    rw [Real.closeSeq_def] at *
    simp [Real.dist_eq] at *
    simp_all
    intro n hn1 hn2
    specialize hClose n (by grind) (by grind)

    set an := a.seq n

    by_cases haz : an = 0
    . simp_all; field_simp at hClose; field_simp; grind

    field_simp;
    rw [abs_div, abs_mul]; field_simp

    have: |an| ≥ |L| / 2 := by
      calc |an| ≥ |L| - |an - L| := by grind
        _ ≥ |L| - ε * |L| * |L| / 2 := by linarith
        _ ≥ |L| / 2 := by field_simp; grind

    have: |an| * |L| * ε ≥ ε * |L| * |L| / 2 := by field_simp; grind

    grind

  intros ε hε

  by_cases h1: ε ≤ 1/|L|
  . exact h_lemma hε h1
  . have := h_lemma (ε := 1/|L|) (hε := by positivity) (h1 := by linarith)
    exact Real.EventuallyClose.mono (a:=a⁻¹) (ε₁:= 1/|L|) (ε₂:= ε) (L := L⁻¹) (by linarith) this

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha

  have ⟨hL1, hL2⟩:= (Sequence.lim_eq).mp hL

  have hinv := Sequence.tendsTo_inv hL (show L ≠ 0 by grind)

  constructor
  . use L⁻¹
  . have := (Sequence.lim_eq).mp hinv
    grind

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by

  exact Sequence.tendsTo_mul ha (Sequence.tendsTo_inv hb hnon)

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have ⟨hM1, hM2⟩:= (Sequence.lim_eq).mp hM
  have h1 := Sequence.tendsTo_div hL hM (show M ≠ 0 by grind)

  constructor
  . use L / M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    grind

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by

  rw [Sequence.TendsTo] at *
  intros ε hε
  specialize ha (ε/2) (by positivity)
  specialize hb (ε/2) (by positivity)
  obtain ⟨N1, hN1, hClose1⟩ := ha
  obtain ⟨N2, hN2, hClose2⟩ := hb
  let N := max N1 N2
  use N
  have: N ≥ (max a b).m := by
    have: (max a b).m = min a.m b.m := by rfl
    grind
  simp [this]
  rw [Real.closeSeq_def] at *
  simp [Real.dist_eq] at *
  simp_all
  intro n hn1 hn2
  specialize hClose1 n (by grind) (by grind)
  specialize hClose2 n (by grind) (by grind)
  grind

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have h1 := Sequence.tendsTo_max hL hM

  constructor
  . use max L M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    have hmb:= (Sequence.lim_eq).mp hM
    grind

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by

  rw [Sequence.TendsTo] at *
  intros ε hε
  specialize ha (ε/2) (by positivity)
  specialize hb (ε/2) (by positivity)
  obtain ⟨N1, hN1, hClose1⟩ := ha
  obtain ⟨N2, hN2, hClose2⟩ := hb
  let N := max N1 N2
  use N
  have: N ≥ (min a b).m := by
    have: (min a b).m = min a.m b.m := by rfl
    grind
  simp [this]
  rw [Real.closeSeq_def] at *
  simp [Real.dist_eq] at *
  simp_all
  intro n hn1 hn2
  specialize hClose1 n (by grind) (by grind)
  specialize hClose2 n (by grind) (by grind)
  grind

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by

  rw [Sequence.convergent_def] at *
  obtain ⟨L, hL⟩ := ha
  obtain ⟨M, hM⟩ := hb

  have h1 := Sequence.tendsTo_min hL hM

  constructor
  . use min L M
  . have hm:= (Sequence.lim_eq).mp h1
    have hma:= (Sequence.lim_eq).mp hL
    have hmb:= (Sequence.lim_eq).mp hM
    grind

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by

  revert m
  apply Nat.le_induction
  . exact ha n
  . intro m hm1 hm2
    specialize ha m
    grind

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by

  rw [Sequence.TendsTo] at *
  constructor
  . intros h1 ε hε
    specialize h1 ε hε
    obtain ⟨N, hN, hClose⟩ := h1
    use max m N

    have: (a.from N).m = max a.m N := by rfl
    have: (a.from m).m = max a.m m := by rfl

    rw [Real.closeSeq_def] at *
    simp [Real.dist_eq] at *
    simp_all
    grind
  . intros h1 ε hε
    specialize h1 ε hε
    obtain ⟨N, hN, hClose⟩ := h1
    use max m N

    have: (a.from N).m = max a.m N := by rfl
    have: (a.from m).m = max a.m m := by rfl

    rw [Real.closeSeq_def] at *
    simp [Real.dist_eq] at *
    simp_all

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by

  rw [Sequence.TendsTo, Sequence.TendsTo]
  constructor
  . intros h1 ε hε
    specialize h1 ε hε
    obtain ⟨N, hN, hClose⟩ := h1
    use N; simp [hN];
    rw [Real.closeSeq_def] at *; simp;
    intro n hn1 hn2
    specialize hClose (n+k) (by grind)
    rw [Real.dist_eq] at *; simp [hn1, hn2]
    have: (a.from N).seq n = a.seq n := by grind
    grind
  . intros h1 ε hε
    specialize h1 ε hε
    obtain ⟨N, hN, hClose⟩ := h1
    have: (mk' a.m fun n ↦ a.seq (↑n + ↑k)).m = a.m := by rfl
    rw [this] at hN
    use N + k; simp [show N + k ≥ a.m by linarith];
    rw [Real.closeSeq_def] at *; simp;
    intro n hn1 hn2
    specialize hClose (n-k) (by grind)
    rw [Real.dist_eq] at *; simp [hn1, hn2]
    simp [show a.m ≤ n - k ∧ N ≤ n - k by grind] at hClose
    grind

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by

  rw [Chapter5.Sequence.isBounded_def, Sequence.isBounded_def]
  constructor
  . rintro ⟨q, hq, hbound⟩
    use q; simp [hq]
    rw [Chapter5.Sequence.boundedBy_def] at hbound
    rw [Sequence.boundedBy_def]
    intro n
    specialize hbound n
    simp
    exact_mod_cast hbound
  . rintro ⟨M, hM, hbound⟩
    choose N hN using exists_int_gt M
    use max N 0
    simp
    rw [Chapter5.Sequence.boundedBy_def]
    rw [Sequence.boundedBy_def] at hbound
    intro n
    specialize hbound n
    simp at hbound
    have: |↑(a.seq n)| ≤ (N:ℝ) := by linarith
    norm_cast at this
    grind

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by

  have ⟨h1, h2⟩:= Sequence.lim_harmonic

  set a := ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence)
  use a, a

  have ha1: lim a / lim a = 0 := by rw [h2]; grind

  have: a.m = 0 := by rfl

  have: (a / a).TendsTo 1 := by
    rw [Sequence.tendsTo_def]
    intros ε hε
    use 0
    simp [show (a / a).m = 0 by rfl]
    rw [Real.closeSeq_def]
    intro n hn
    rw [Real.dist_eq]; simp [hn]
    simp [show a.seq n ≠ 0 by grind]
    grind

  have ha2: lim (a / a) = 1 := by grind [Sequence.lim_eq.mp this]

  rw [ha1, ha2]; simp_all;

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by

  rw [Chapter5.Sequence.isCauchy_def]
  constructor
  . intro h ε hε
    choose ε' hε' hlt using exists_pos_rat_lt hε
    specialize h ε' hε'

    obtain ⟨N, hN, hClose⟩ := h
    use N; simp [hN]
    intro n hn m hm

    rw [Rat.steady_def] at hClose
    specialize hClose n (by grind) m (by grind)
    rw [Rat.Close] at hClose
    simp at hClose
    simp [hn, hm, show n ≥ a.n₀ ∧ m ≥ a.n₀ by grind] at hClose

    have: |a.seq n - a.seq m| ≤ (ε':ℝ) := by exact_mod_cast hClose
    simp at this
    grind

  . intros h ε hε
    specialize h ε (by positivity)
    obtain ⟨N, hN, hClose⟩ := h
    rw [Rat.eventuallySteady_def]
    use N; simp [hN]
    rw [Rat.Steady]
    intro n hn m hm
    rw [Rat.Close]; simp [hn, hm];
    specialize hClose n (by grind) m (by grind)
    norm_cast at hClose

end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by sorry

end Chapter6

import Mathlib.Tactic
import Analysis.Section_4_3

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.1.1 (Sequence). To avoid some technicalities involving dependent types, we extend
  sequences by zero to the left of the starting point {name (full := Sequence.n₀)}`n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℚ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Functions from {lean}`ℕ` to {lean}`ℚ` can be thought of as sequences starting from 0; {name}`Sequence.ofNatFun` performs this conversion.

The {attr}`coe` attribute allows the delaborator to print {lean}`Sequence.ofNatFun f` as {lit}`↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (f : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then f n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
If {given}`a : ℕ → ℚ` is used in a context where a {name}`Sequence` is expected, automatically coerce {name}`a` to {lean}`Sequence.ofNatFun a` (which will be pretty-printed as {lean (type :="Sequence")}`↑a`).
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Example 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Example 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Example 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Example 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Example 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- need to temporarily leave the `Chapter5` namespace to introduce the following notation

end Chapter5

/--
A slight generalization of Definition 5.1.3 - definition of {name}`ε`-steadiness for a sequence with an
arbitrary starting point {lean}`a.n₀`
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Definition 5.1.3 - definition of {name}`ε`-steadiness for a sequence starting at 0
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Not in textbook: the sequence 3, 3 ... is 1-steady.
Intended as a demonstration of {name}`Rat.Steady.coe`.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
{given -show}`hn : n ≥ 0, hm : m ≥ 0`
Compare: if you need to work with {name}`Rat.Steady` on the coercion directly, there will be side
conditions {lean}`hn : n ≥ 0` and {lean}`hm : m ≥ 0` that you will need to deal with.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is 1-steady.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Split into four cases based on whether n and m are even or odd
  -- In each case, we know the exact value of a n and a m
  split_ifs <;> simp [Rat.Close]

/--
Example 5.1.5: The sequence `1, 0, 1, 0, ...` is not ½-steady.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is 0.1-steady.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Example 5.1.5: The sequence 0.1, 0.01, 0.001, ... is not 0.01-steady. Left as an exercise.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro h; specialize h 0 1
  simp [Rat.Close] at h
  norm_num at h

/-- Example 5.1.5: The sequence 1, 2, 4, 8, ... is not ε-steady for any ε. Left as an exercise.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by

  have two_pow_succ_gt_n : ∀ n : ℕ, 2^(n+1) > (n+1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => grind

  rw [Rat.Steady.coe]
  unfold Rat.Close
  push_neg
  by_cases h : ε < 0
  . use 0, 0; norm_num; grind
  .
    push_neg at h
    let x := ⌊ε⌋ + 1
    have h1: x > ε := by grind [Int.lt_floor_add_one]
    have hn: x ≥ (0:ℚ) := by grind
    norm_cast at hn
    clear_value x
    lift x to ℕ using hn
    use x+1, x
    simp [pow_add, mul_assoc, ←mul_sub]
    norm_num
    rw [←pow_succ]
    have h2 := two_pow_succ_gt_n x
    calc ε < (x : ℚ)        := by exact_mod_cast h1
      _ < (x + 1 : ℚ)       := by grind
      _ < (2 ^ (x + 1) : ℚ) := by exact_mod_cast h2

/-- Example 5.1.5:The sequence 2, 2, 2, ... is ε-steady for any ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
The sequence 10, 0, 0, ... is 10-steady.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Split into 4 cases based on whether n and m are 0 or not
  split_ifs <;> simp [Rat.Close]

/--
The sequence 10, 0, 0, ... is not ε-steady for any smaller value of ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  {name}`Sequence.from` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Definition 5.1.6 (Eventually ε-steady) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is not 0.1-steady
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h

/--
Example 5.1.7: The sequence `a_10, a_11, a_12, ...` is 0.1-steady
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Example 5.1.7: The sequence 1, 1/2, 1/3, ... is eventually 0.1-steady
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Example 5.1.7

The sequence 10, 0, 0, ... is eventually ε-steady for every ε > 0. Left as an exercise.
-/
lemma Sequence.ex_5_1_7_d1 {ε:ℚ} (hε:ε>0) :
  ε.Steady (((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence).from 1) := by

  rw [Rat.Steady]
  intro m hm n hn; simp at hm hn
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp [Rat.Close]
  simp [show n ≠ 0 by linarith, show m ≠ 0 by linarith]
  positivity

lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) :=
  ⟨1, by simp, (Sequence.ex_5_1_7_d1 hε)⟩

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Definition of Cauchy sequences, for a sequence starting at {lean}`0` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/

private lemma Sequence.sqrt_two_increasing (m n : ℕ) (h: m ≤ n) : sqrt_two m ≤ sqrt_two n := by
  unfold sqrt_two
  simp
  rw [←mul_le_mul_iff_of_pos_right (show (0:ℚ) < 10 ^ n by positivity)]
  have (x:ℚ): x / 10 ^ m * 10 ^ n  = x * 10^(n-m) := by grind [pow_sub₀]
  simp [this]

  have : (10:ℝ)^n = 10^m * 10^(n-m)  := by grind [pow_add, Nat.sub_add_cancel]
  rw [this, ←mul_assoc]
  norm_cast

  set m' := √2 * ↑((10:ℕ) ^ m)
  set p := 10^(n-m)

  have h1 := Int.floor_le m'
  rw [le_iff_exists_nonneg_add] at h1
  obtain ⟨ c, h2, h3 ⟩ := h1

  calc ⌊m' * p⌋ = ⌊⌊m'⌋ * p + c * p⌋ := by grind
    _ = ⌊m'⌋ * p + ⌊c * p⌋ := by grind [Int.floor_intCast_add (⌊m'⌋ * p) (c * p)]
    _ ≥ ⌊m'⌋ * p := by grind [show ⌊c * p⌋ ≥ 0 by positivity]

private lemma Sequence.sqrt_two_gap (m n : ℕ) (h: m ≤ n) : sqrt_two n - sqrt_two m ≤ 1 / 10^m := by
  unfold sqrt_two
  simp

  have: (0:ℚ) < 10 ^ n := by positivity
  rw [←mul_le_mul_iff_of_pos_right this]
  simp [add_mul]

  have (x:ℚ): x / 10 ^ m * 10 ^ n  = x * 10^(n-m) := by grind [pow_sub₀]
  simp [this]
  have : ((10:ℚ)^m)⁻¹ * 10 ^ n  = 10^(n-m) := by grind [pow_sub₀]
  simp [this]

  have : (10:ℝ)^n = 10^m * 10^(n-m)  := by grind [pow_add, Nat.sub_add_cancel]
  rw [this, ←mul_assoc]
  norm_cast

  set m' := √2 * ↑((10:ℕ) ^ m)
  set p := 10^(n-m)

  -- have : (p:ℝ) > 0 := by positivity
  have h1 := Int.floor_le (m' * p)
  have h2 := Int.lt_floor_add_one m'

  have h3: m' * p < (⌊m'⌋ + 1) * p := by gcongr
  have h4: ⌊m' * p⌋ ≤ (p:ℝ) + ⌊m'⌋ * (p:ℝ) := by grind

  exact_mod_cast h4

lemma Sequence.sqrt_two_dist (m n : ℕ) (h: m ≤ n) : |sqrt_two n - sqrt_two m| ≤ 1 / 10^m := by

  have := sqrt_two_increasing m n h

  have: |sqrt_two.seq n - sqrt_two.seq m| = sqrt_two.seq n - sqrt_two.seq m := by grind

  grind [sqrt_two_gap]

theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by
  rw [Rat.Steady]
  intro n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [Rat.Close]

  have h1 (x:ℕ): (1:ℚ) / 10^x ≤ 1 := by
    rw [div_le_one (show (10^x:ℚ) > 0 by positivity)]
    norm_cast
    grind

  by_cases h : m ≤ n
  . have := sqrt_two_dist m n h
    grind
  . push_neg at h
    have := sqrt_two_dist n m (show n ≤ m by linarith)
    grind

/--
  Example 5.1.10. (This requires extensive familiarity with Mathlib's API for the real numbers.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by
  rw [Rat.Steady]
  intro n hn m hm
  simp at hn hm
  lift n to ℕ using (by linarith)
  lift m to ℕ using (by linarith)
  simp [Rat.Close, hn, hm]

  have h1 (x:ℕ) (h: 1 ≤ x): (1:ℚ) / 10^x ≤ 1 / 10 := by
    have ha: 0 < (10:ℚ) := by positivity
    have hb: 0 < (10^x:ℚ) := by positivity
    rw [one_div_le_one_div hb ha]
    norm_cast
    rw [←Nat.pow_one 10, Nat.pow_le_pow_iff_right (show 1 < 10 by norm_num)]
    grind

  by_cases h : m ≤ n
  . have h2 := sqrt_two_dist m n h
    grind
  . push_neg at h
    have: n ≤ m := by grind
    have h3 := sqrt_two_dist n m this
    grind

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two := by
  rw [Rat.EventuallySteady]
  have : sqrt_two.n₀ = 0 := by unfold sqrt_two; simp
  use 1
  grind [Sequence.ex_5_1_10_b]

/-- Proposition 5.1.11. The harmonic sequence, defined as a₁ = 1, a₂ = 1/2, ... is a Cauchy sequence. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- We go by reverse from the book - first choose N such that N > 1/ε
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N:ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    We establish the following bounds:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    These imply that the distance between 1/j and 1/k is at most 1/N - when they are as "far apart" as possible.
    -/
    have : 1/j ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/j
    have : 1/k ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Definition 5.1.12 (bounded sequences). Here we start sequences from {lean}`0` rather than {lean}`1` to align
  better with Mathlib conventions.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 5.1.12 (bounded sequences) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Example 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by
  rw [Sequence.IsBounded]
  simp [Sequence.BoundedBy]
  intro M h

  let x := ⌊M⌋ + 1

  have h1: x > M := by grind [Int.lt_floor_add_one]
  have : (x:ℚ) ≥ 0 := by linarith
  have h2: x ≥ 0 := mod_cast this

  use x

  simp [h2]; norm_cast

  have : x.toNat > M := by rwa [← Int.toNat_of_nonneg h2] at h1

  grind

/-- Example 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Example 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁: Odd N
  observe h₂: Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Lemma 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- this proof is written to follow the structure of the original text.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Lemma 5.1.15 (Cauchy sequences are bounded) / Exercise 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [Sequence.IsBounded]
  rw [isCauchy_def] at h
  specialize h (1.0 : ℚ) (by norm_num)
  rw [Rat.eventuallySteady_def] at h
  choose N hpos haN using h

  -- aN = a.N ...
  set aN := a.from N
  have hN: N = (a.from N).n₀ := by grind

  -- aM = a.n₀ ~ a.N
  set n0toN := (N - a.n₀).toNat
  set aM : Fin n0toN → ℚ := fun n ↦ a (n + a.n₀)
  choose M haM hBound using IsBounded.finite aM

  set Up := M + 1.0 + |aN N|
  use Up
  simp [show Up ≥ 0 by positivity]

  rw [BoundedBy]
  intro idx
  by_cases h: idx < a.n₀
  . rw [a.vanish idx h]; simp; grind
  .
    by_cases h1: idx ≥ N
    . -- a.N ...
      have := Sequence.from_eval a h1
      rw [←this]
      rw [Rat.steady_def] at haN
      have: N ≥ (a.from N).n₀ := by grind
      have hN' := haN N this idx
      rw [hN] at h1
      specialize hN' h1
      unfold Rat.Close at hN'
      grind
    . -- a.0 ~ a.N
      unfold Chapter5.BoundedBy at hBound

      set y := (idx - a.n₀).toNat
      have hy: y < (N - a.n₀).toNat := by grind

      specialize hBound ⟨y, hy⟩
      grind

/-- Exercise 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by

  rw [IsBounded] at ha hb
  obtain ⟨Ma, ⟨hma1, hma2⟩⟩ := ha
  obtain ⟨Mb, ⟨hmb1, hmb2⟩⟩ := hb

  rw [boundedBy_def] at hma2 hmb2

  rw [IsBounded]
  use Ma + Mb
  simp [show Ma + Mb ≥ 0 by grind]
  rw [boundedBy_def]

  intro idx

  specialize hma2 idx
  specialize hmb2 idx

  by_cases h1: idx ≥ 0
  . simp [h1] at hma2 hmb2 ⊢
    grind
  . simp [h1]
    grind

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by

  rw [IsBounded] at ha hb
  obtain ⟨Ma, ⟨hma1, hma2⟩⟩ := ha
  obtain ⟨Mb, ⟨hmb1, hmb2⟩⟩ := hb

  rw [boundedBy_def] at hma2 hmb2

  rw [IsBounded]
  use Ma + Mb
  simp [show Ma + Mb ≥ 0 by grind]

  rw [boundedBy_def]

  simp_all
  grind

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by

  rw [IsBounded] at ha hb
  obtain ⟨Ma, ⟨hma1, hma2⟩⟩ := ha
  obtain ⟨Mb, ⟨hmb1, hmb2⟩⟩ := hb

  rw [boundedBy_def] at hma2 hmb2

  rw [IsBounded]
  use Ma * Mb
  have : Ma * Mb ≥ 0 := by grind [mul_nonneg]
  simp [this]
  rw [boundedBy_def]

  simp_all
  grind [mul_le_mul]

end Chapter5

import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers {lean}`ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

theorem abs_of_nonneg {x: ℚ} (hx: 0 ≤ x) : abs x = x := by grind

theorem abs_of_nonpos {x: ℚ} (hx: x ≤ 0) : abs x = -x := by grind
/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  rcases lt_trichotomy x 0 with hlt | hz | hgt
  . have h1: |x| = -x := by grind
    have h2:= abs_of_neg hlt
    rw [h1, h2]
  · rw [hz, abs_of_zero]; simp
  · have h1: |x| = x := by grind
    have h2:= abs_of_pos hgt
    rw [h1, h2]

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  rw [←abs_eq_abs]
  rcases lt_trichotomy x 0 with hlt | hz | hgt
  . have h:= abs_of_neg hlt
    rw [h]; linarith
  · rw [hz, abs_of_zero]
  · have h:= abs_of_pos hgt
    rw [h]; linarith

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  rw [←abs_eq_abs]
  constructor
  . intro h
    rcases lt_trichotomy x 0 with hlt | hz | hgt
    . have h1:= abs_of_neg hlt
      rw [h1] at h
      simp at h
      exact h
    . exact hz
    . have h1:= abs_of_pos hgt
      rw [h1] at h
      exact h
  . intro h; rw [h, abs_of_zero]

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  rw [←abs_eq_abs, ←abs_eq_abs, ←abs_eq_abs]
  rcases lt_trichotomy x 0 with hxn | hxz | hxp
  . rcases lt_trichotomy y 0 with hyn | hyz | hyp
    . have: x + y < 0 := by linarith
      rw [abs_of_neg hxn, abs_of_neg hyn, abs_of_neg this]
      simp
    . rw [hyz, abs_of_zero]; simp;
    . rw [abs_of_neg hxn, abs_of_pos hyp]
      rcases lt_trichotomy (x+y) 0 with hlt | hz | hgt
      . rw [abs_of_neg hlt]; simp; linarith
      . rw [hz, abs_of_zero]; linarith
      . rw [abs_of_pos hgt]; simp; linarith
  . rw [hxz, abs_of_zero]; simp;
  . rcases lt_trichotomy y 0 with hyn | hyz | hyp
    . rw [abs_of_pos hxp, abs_of_neg hyn]
      rcases lt_trichotomy (x+y) 0 with hlt | hz | hgt
      . rw [abs_of_neg hlt]; simp; linarith
      . rw [hz, abs_of_zero]; linarith
      . rw [abs_of_pos hgt]; simp; linarith
    . rw [hyz, abs_of_zero]; simp;
    . have: x + y > 0 := by linarith
      rw [abs_of_pos hxp, abs_of_pos hyp, abs_of_pos this]

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  rcases lt_trichotomy x 0 with hxn | hxz | hxp
  . rw [←abs_eq_abs, abs_of_neg hxn]
    constructor
    . intro ⟨h1, h2⟩
      linarith
    . intro h
      constructor
      . linarith
      . linarith
  . rw [hxz]; simp;
  . rw [←abs_eq_abs, abs_of_pos hxp]
    constructor
    . intro ⟨h1, h2⟩
      linarith
    . intro h
      constructor
      . linarith
      . linarith

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  rw [abs_le_iff]

lemma abs_mul_nonneg (x y:ℚ) (hx: 0 ≤ x) : |x * y| = x * |y| := by
  rw [←abs_eq_abs, ←abs_eq_abs]
  by_cases h: 0 ≤ y
  . rw [abs_of_nonneg h]
    have : x * y ≥ 0 := by positivity
    rw [abs_of_nonneg this]
  · push_neg at h
    rw [abs_of_neg h]
    have : x * y ≤ 0 := by grind [mul_nonpos_iff]
    rw [abs_of_nonpos this]
    simp

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  by_cases hx: 0 ≤ x
  . rw [abs_mul_nonneg x y hx, ←abs_eq_abs x, abs_of_nonneg hx]
  . push_neg at hx
    by_cases hy: 0 ≤ y
    . rw [←abs_eq_abs y, abs_of_nonneg hy]
      rw [mul_comm x y, abs_mul_nonneg y x hy]
      rw [mul_comm]
    . push_neg at hy
      simp [←abs_eq_abs]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  rw [←abs_eq_abs, ←abs_eq_abs]

  by_cases hx: 0 ≤ x
  . have: -x ≤ 0 := by linarith
    rw [abs_of_nonneg hx, abs_of_nonpos this]
    simp
  . push_neg at hx
    have: -x > 0 := by linarith
    rw [abs_of_pos this, abs_of_neg hx]

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  rw [dist_eq]
  apply abs_nonneg

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [dist_eq, abs_eq_zero_iff]; grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  rw [dist_eq, dist_eq, ←abs_neg (x-y)]; simp

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  rw [dist_eq, dist_eq, dist_eq]
  have := abs_add (x-y) (y-z)
  simpa

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff]; norm_num; linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [close_iff]; simp

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor
  . intro h a ha
    rw [close_iff, h]; simp; linarith
  . intro h
    by_contra hne
    have h1: |x - y| ≠ 0 := by grind
    have h2: |x - y| > 0 := by grind [abs_nonneg]
    have h3: |x-y| / 2 > 0 := by grind
    specialize h (|x-y| / 2) h3
    rw [close_iff] at h
    have: |x-y| ≤ 0 := by grind
    linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  rw [close_iff, close_iff, ←abs_neg (x-y)]; simp

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
  rw [close_iff] at hxy hyz ⊢
  have := abs_add (x-y) (y-z)
  simp at this
  linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
  rw [close_iff] at hxy hzw ⊢
  have h := abs_add (x-y) (z-w)
  have: x - y + (z - w) = (x+z) - (y+w) := by grind
  rw [←this]
  linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
  rw [close_iff] at hxy hzw ⊢
  rw [←abs_neg] at hzw
  simp at hzw
  have h := abs_add (x-y) (w-z)
  have: x - y + (w - z) = (x-z) - (y-w) := by grind
  rw [←this]
  linarith

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly weakened -/
theorem close_add {ε x y z:ℚ} (hxy: ε.Close x y) :
    ε.Close (x+z) (y+z) := by
  rw [close_iff] at hxy ⊢
  have : x + z - (y + z) = x - y := by grind
  rwa [this]

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
  rw [close_iff] at hxy ⊢
  linarith

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rw [close_iff] at hxy hxz ⊢

  rcases hbetween with (⟨h1, h2⟩ | ⟨h3, h4⟩)
  . by_cases hw: x ≤ w
    . have hx: x ≤ z := by linarith
      have: (z - w) + (w - x) = (z - x) := by grind
      have: |z - w| + |w - x| = |z - x| := by grind
      have: |w-x| ≤ |z-x| := by grind
      have: |x-w| ≤ |x-z| := by grind
      linarith
    . push_neg at hw
      have: x > y := by linarith
      have: (w - y) + (x - w) = (x - y) := by grind
      have: |w - y| + |x - w| = |x - y| := by grind
      have: |x-w| ≤ |x-y| := by grind
      linarith
  . by_cases hw: x ≤ w
    . have hx: x ≤ y := by linarith
      have: (y - w) + (w - x) = (y - x) := by grind
      have: |y - w| + |w - x| = |y - x| := by grind
      have: |x-w| ≤ |x-y| := by grind
      linarith
    . push_neg at hw
      have: x > z := by linarith
      have: (w - z) + (x - w) = (x - z) := by grind
      have: |w - z| + |x - w| = |x - z| := by grind
      have: |x-w| ≤ |x-z| := by grind
      linarith

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
  rw [close_iff] at hxy ⊢
  rw [←sub_mul, abs_mul]
  have: |z| ≥ 0 := by grind
  apply mul_le_mul_of_nonneg_right hxy this

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
  rw [close_iff] at hxy hzw ⊢
  have h1 := mul_le_mul_of_nonneg_right hxy (abs_nonneg z)
  have h2 := mul_le_mul_of_nonneg_right hzw (abs_nonneg y)
  rw [←abs_mul, sub_mul] at h1 h2
  rw [mul_comm z y, mul_comm w y] at h2
  have h3:= abs_add (x * z - y * z) (y * z - y * w)
  simp at h3
  linarith

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with m ih
  . rw [pow_zero]; simp
  . rw [pow_succ, ←mul_assoc, ih, ←pow_succ, add_assoc]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m ih
  . rw [pow_zero]; simp
  . rw [pow_succ, ih, pow_add, mul_add]; simp

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n ih
  . rw [pow_zero, pow_zero, pow_zero]; simp
  . rw [pow_succ, ←mul_assoc, ih, pow_succ, pow_succ]; ring

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by

  constructor
  . intro h1
    have h1: 1 ≤ n := by linarith
    induction n, h1 using Nat.le_induction with
    | base => simp at h1; exact h1
    | succ k hk ih =>
      specialize ih hk
      rw [pow_succ] at h1
      by_contra hnz
      push_neg at hnz
      have h2:  x^k = 0 / x := by grind [div_eq_iff]
      simp [hnz] at h2
  . intro h1
    rw [h1]; simp; grind

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  . rw [pow_zero]; simp
  . rw [pow_succ]; grind [mul_nonneg_iff]

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n ih
  . rw [pow_zero]; simp
  . rw [pow_succ]; grind [mul_pos_iff]

theorem pow_nz {x:ℚ} (n:ℕ) (hx: x ≠ 0) : x^n ≠ 0 := by
  induction' n with n ih
  . rw [pow_zero]; simp
  . rw [pow_succ]; grind

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  . rw [pow_zero]; simp
  . rw [pow_succ, pow_succ]
    calc x ^ n * x ≥ y ^ n * x := by grind [mul_le_mul_of_nonneg_right]
      _ ≥ y ^ n * y := by grind [mul_le_mul_of_nonneg_left, pow_nonneg]

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction n, hn using Nat.le_induction with
  | base => simp; exact hxy
  | succ k hk ih =>
    simp at hk
    rw [pow_succ, pow_succ]
    have: x > 0 := by linarith
    calc x ^ k * x > y ^ k * x := by grind [mul_lt_mul_of_pos_right]
      _ ≥ y ^ k * y := by grind [mul_le_mul_of_nonneg_left, pow_nonneg]

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero]; simp
  . rw [pow_succ, pow_succ, ih, abs_mul]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

theorem zpow_neg_nat (x:ℚ) (n:ℤ) (h: n ≥ 0) : x^(-n) = 1/(x^(Int.toNat n)) := by
  lift n to Nat using h
  rw [zpow_neg]; simp

theorem zpow_noneg_nat (x:ℚ) (n:ℤ) (h: n ≥ 0) : x^n = x^(Int.toNat n) := by
  lift n to Nat using h
  simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by

  let n1 : Nat := Int.natAbs n
  let m1 : Nat := Int.natAbs m

  rcases Int.lt_trichotomy n 0 with hnl | hn0 | hng
  . have: n1 = -n := by grind
    have: n = -n1 := by grind
    rw [this, zpow_neg]
    rcases Int.lt_trichotomy m 0 with hml | hm0 | hmg
    . have: m1 = -m := by grind
      have: m = -m1 := by grind
      rw [this, zpow_neg, ←Int.neg_add]
      norm_cast
      rw [zpow_neg]
      grind
    . rw [hm0]; simp
    . have: m1 = m := by grind
      rw [←this]
      norm_cast
      by_cases hmn: m1 ≤ n1
      . rw [show -(n1:ℤ) + (m1:ℤ) = -((n1 - m1):ℤ) by grind]
        have hpos: ((n1:ℤ) - (m1:ℤ)) ≥ 0 := by linarith
        rw [zpow_neg_nat _ _ hpos]
        simp
        have hnz: x^(n1-m1) ≠ 0 := by grind [pow_nz]
        apply mul_left_cancel₀ hnz
        rw [←mul_assoc, mul_inv_cancel₀ hnz]
        rw [mul_comm, ←mul_assoc, pow_add]
        rw [show m1 + (n1 - m1) = n1 by grind]
        rw [mul_inv_cancel₀ (pow_nz _ hx)]
      . push_neg at hmn
        rw [show -(n1:ℤ) + (m1:ℤ) = (m1 - n1) by grind]
        simp
        have hpos: (m1:ℤ) - (n1:ℤ) ≥ 0 := by linarith
        rw [zpow_noneg_nat _ _ hpos]
        simp
        have hnz := pow_nz n1 hx
        apply mul_left_cancel₀ hnz
        rw [←mul_assoc, mul_inv_cancel₀ hnz, pow_add]
        rw [show n1 + (m1 - n1) = m1 by grind]
        simp
  . rw [hn0]; simp;
  . have: n1 = n := by grind
    rw [←this]
    rcases Int.lt_trichotomy m 0 with hml | hm0 | hmg
    . have: m1 = -m := by grind
      have: m = -m1 := by grind
      rw [this, zpow_neg]
      norm_cast
      by_cases hmn: m1 ≤ n1
      . rw [show (n1:ℤ) + (-m1:ℤ) = (n1 - m1) by grind]
        have hpos: ((n1:ℤ) - (m1:ℤ)) ≥ 0 := by linarith
        rw [zpow_noneg_nat _ _ hpos]
        simp
        have hnz := pow_nz m1 hx
        apply mul_left_cancel₀ hnz
        rw [mul_comm (x^n1) (x ^ m1)⁻¹, ←mul_assoc, mul_inv_cancel₀ hnz, pow_add]
        rw [show m1 + (n1 - m1) = n1 by grind]
        simp
      . push_neg at hmn
        rw [show (n1:ℤ) + (-m1:ℤ) = -(m1 - n1) by grind]
        have hpos: (m1:ℤ) - (n1:ℤ) ≥ 0 := by linarith
        rw [zpow_neg_nat _ _ hpos]
        simp
        have hnz: x^(m1-n1) ≠ 0 := by grind [pow_nz]
        apply mul_left_cancel₀ hnz
        rw [←mul_assoc, mul_inv_cancel₀ hnz, pow_add]
        rw [show m1 - n1 + n1 = m1 by grind]
        rw [mul_inv_cancel₀ (pow_nz _ hx)]
    . rw [hm0]; simp
    . have: m1 = m := by grind
      rw [←this]
      norm_cast
      grind

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  let n1 : Nat := Int.natAbs n
  let m1 : Nat := Int.natAbs m

  by_cases hm: m ≤ 0
  . by_cases hn: n ≤ 0
    . rw [show n = -n1 by grind]
      rw [show m = -m1 by grind]
      simp
      have: (n1:ℤ) * (m1:ℤ) ≥ 0 := by grind
      rw [zpow_noneg_nat _ _ this]
      grind [pow_mul]
    . push_neg at hn
      rw [show n = n1 by grind]
      rw [show m = -m1 by grind]
      simp
      have: (n1:ℤ) * (m1:ℤ) ≥ 0 := by grind
      rw [zpow_noneg_nat _ _ this]
      grind [pow_mul]
  . push_neg at hm
    by_cases hn: n ≤ 0
    . rw [show n = -n1 by grind]
      rw [show m = m1 by grind]
      simp
      have: (n1:ℤ) * (m1:ℤ) ≥ 0 := by grind
      rw [zpow_noneg_nat _ _ this]
      grind [pow_mul]
    . push_neg at hn
      rw [show n = n1 by grind]
      rw [show m = m1 by grind]
      simp
      have: (n1:ℤ) * (m1:ℤ) ≥ 0 := by grind
      rw [zpow_noneg_nat _ _ this]
      grind [pow_mul]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  let n1 : Nat := Int.natAbs n

  by_cases hn: n ≤ 0
  . rw [show n = -n1 by grind, zpow_neg, zpow_neg, zpow_neg, mul_pow]
    grind
  . rw [show n = n1 by grind]; norm_cast; rw [mul_pow]

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  let n1 : Nat := Int.natAbs n

  by_cases hn: n ≤ 0
  . rw [show n = -n1 by grind, zpow_neg]
    positivity
  . rw [show n = n1 by grind]; norm_cast
    positivity

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  lift n to ℕ using (show n ≥ 0 by linarith)
  norm_cast
  grind [pow_ge_pow]

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by

  let n1 : Nat := Int.natAbs n
  have hn1: n = -n1 := by grind

  rw [hn1, zpow_neg, zpow_neg]

  have h1 : (-n) > 0 := by grind
  have h2 := zpow_ge_zpow hxy hy h1
  rw [hn1] at h2; simp at h2

  have : y^n ≥ 0 := by grind [zpow_pos]
  have h3 := mul_le_mul_of_nonneg_right h2 this

  rw [hn1] at h3; simp at h3
  have: y^n1 > 0 := by grind [pow_pos]
  have: y^n1 ≠ 0 := by grind
  rw [mul_inv_cancel₀ this] at h3

  have : x^n ≥ 0 := by grind [zpow_pos]
  have h4 := mul_le_mul_of_nonneg_left h3 this
  rw [hn1] at h4; simp at h4
  have: x^n1 > 0 := by grind [pow_pos]
  have: x^n1 ≠ 0 := by grind
  rw [←mul_assoc, mul_comm (x ^ n1)⁻¹  (x ^ n1), mul_inv_cancel₀ this] at h4

  grind

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  . -- x < y -> x^n < y^n
    by_cases hn: n ≤ 0
    . let n1 : Nat := Int.natAbs n
      have hn1: n = -n1 := by grind
      rw [hn1, zpow_neg, zpow_neg] at hxy
      have: x^n1 = y^n1 := by grind
      have h1: x^n1 < y^n1 := by grind [pow_gt_pow]
      linarith
    . push_neg at hn
      lift n to ℕ using (show n ≥ 0 by linarith)
      have h1: x^n < y^n := by grind [pow_gt_pow]
      norm_cast at hxy
      linarith
  . exact heq
  . -- x > y -> x^n > y^n
    by_cases hn: n ≤ 0
    . let n1 : Nat := Int.natAbs n
      have hn1: n = -n1 := by grind
      rw [hn1, zpow_neg, zpow_neg] at hxy
      have: x^n1 = y^n1 := by grind
      have h1: x^n1 > y^n1 := by grind [pow_gt_pow]
      linarith
    . push_neg at hn
      lift n to ℕ using (show n ≥ 0 by linarith)
      have h1: x^n > y^n := by grind [pow_gt_pow]
      norm_cast at hxy
      linarith

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by
  rcases lt_trichotomy x 0 with hlt | hz | hgt
  . simp;
  . rw [hz]; simp
  . simp

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  by_cases h: N = 0
  . rw [h]; norm_num
  . push_neg at h
    have hn: N > 0 := by grind
    induction N, hn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      simp at hk
      specialize ih (show k ≠ 0 by linarith)
      have: 2 ^ (k + 1) = 2 ^ k * 2 := by grind
      rw [this]
      linarith

import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases h: x = 0
  . grind
  . push_neg at h
    obtain ⟨a, ha, ⟨c, hc, hd⟩, hgc⟩ := boundedAwayZero_of_nonzero h
    have ha1 := (Sequence.IsCauchy.coe a).mp ha
    choose N ha2 using ha1 (c/2) (by positivity)
    simp only [Section_4_3.dist] at ha2

    let a' : ℕ → ℚ := fun n ↦ a (n + N)
    have heq: Sequence.Equiv a a' := by
      rw [Sequence.equiv_iff]
      intro ε hε
      choose N1 hmn using ha1 ε hε
      simp only [Section_4_3.dist] at hmn
      use N1; intro n hn;
      rw [show a' n = a (n + N) by rfl]
      exact hmn n (by grind) (n + N) (by grind)

    have h_cauchy: (a':Sequence).IsCauchy := by exact (Sequence.isCauchy_of_equiv heq).mp ha
    have h_eq_x: x = LIM a' := by grind [(Real.LIM_eq_LIM ha h_cauchy).mpr heq]

    have hnc1: ∀ (n : ℕ), |a' n| ≥ c := by grind
    have hnc2: ∀ (j k : ℕ), |a' j - a' k| ≤ c / 2 := by grind

    rcases lt_trichotomy (a' 0) 0 with hlt | heq | hgt
    . have h_a_neg: BoundedAwayNeg a' := by
        rw [boundedAwayNeg_def]
        use c; simp [show c > 0 by grind];
        intro n
        specialize hnc2 0 n
        have: a' 0 ≤ -c := by grind
        grind
      have: x.IsNeg := by exact (isNeg_def x).mpr ⟨ a', h_a_neg, h_cauchy, h_eq_x ⟩
      grind
    . grind
    . have h_a_pos: BoundedAwayPos a' := by
        rw [boundedAwayPos_def]
        use c; simp [show c > 0 by grind];
        intro n
        specialize hnc2 0 n
        have: a' 0 ≥ c := by grind
        grind
      have: x.IsPos := by exact (isPos_def x).mpr ⟨ a', h_a_pos, h_cauchy, h_eq_x ⟩
      grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  by_contra ⟨hz, hpos⟩
  obtain ⟨a, hba, h_cauchy, _⟩ := hpos

  have := BoundedAwayZero.boundedAwayPos hba
  have := Real.lim_of_boundedAwayZero this h_cauchy

  grind

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  by_contra ⟨hz, hneg⟩
  obtain ⟨a, hba, h_cauchy, _⟩ := hneg

  have := BoundedAwayZero.boundedAwayNeg hba
  have := Real.lim_of_boundedAwayZero this h_cauchy

  grind

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  by_contra ⟨hpos, hneg⟩
  obtain ⟨a, hpos, hc1, h1⟩ := hpos
  obtain ⟨a', hneg, hc2, h2⟩ := hneg

  obtain ⟨c, hc, ha⟩ := hpos
  obtain ⟨c', hc', ha'⟩ := hneg

  have hequ: LIM a = LIM a' := by grind
  rw [LIM_eq_LIM hc1 hc2, Sequence.equiv_iff] at hequ

  specialize hequ c (by positivity)

  obtain ⟨N, hle⟩ := hequ

  have hgt: ∀ (n:ℕ), |a n - a' n| > c := by grind

  specialize hle N; simp at hle
  specialize hgt N
  linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  rw [isNeg_def, isPos_def]
  constructor
  . intro ⟨a, hneg, hcauchy, hx⟩
    use -a
    refine ⟨?_, ?_, ?_⟩
    . obtain ⟨c, hc, hc1⟩ := hneg
      rw [boundedAwayPos_def]
      use c; simp [hc]; grind
    . exact Sequence.IsCauchy.neg a hcauchy
    . rw [←Real.neg_LIM a hcauchy, hx]

  . intro ⟨a, hpos, hcauchy, hx⟩
    use -a
    refine ⟨?_, ?_, ?_⟩
    . obtain ⟨c, hc, hc1⟩ := hpos
      rw [boundedAwayNeg_def]
      use c; simp [hc]; grind
    . exact Sequence.IsCauchy.neg a hcauchy
    . rw [←Real.neg_LIM a hcauchy]; grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, ⟨c, hc, hc1⟩, ha_cauchy, ha⟩ := hx
  obtain ⟨b, ⟨d, hd, hd1⟩, hb_cauchy, hb⟩ := hy
  rw [isPos_def]
  use a + b
  refine ⟨?_, ?_, ?_⟩
  . rw [boundedAwayPos_def]; simp;
    use c+d; simp [show c+d > 0 by positivity]; grind
  . exact Sequence.IsCauchy.add ha_cauchy hb_cauchy
  . rw [ha, hb, Real.LIM_add ha_cauchy hb_cauchy]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, ⟨c, hc, hc1⟩, ha_cauchy, ha⟩ := hx
  obtain ⟨b, ⟨d, hd, hd1⟩, hb_cauchy, hb⟩ := hy
  rw [isPos_def]
  use a * b
  refine ⟨?_, ?_, ?_⟩
  . rw [boundedAwayPos_def]; simp;
    use c*d; simp [show c*d > 0 by positivity];
    intro n; specialize hc1 n; specialize hd1 n
    grind [mul_le_mul]
  . exact Sequence.IsCauchy.mul ha_cauchy hb_cauchy
  . rw [ha, hb, Real.LIM_mul ha_cauchy hb_cauchy]

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  rw [isPos_def]
  constructor
  . intro ⟨a, ⟨c, hc, hpos⟩, hcaucy, hq⟩
    rw [ratCast_def, LIM_eq_LIM (Sequence.IsCauchy.const q) hcaucy] at hq
    rw [Sequence.equiv_iff] at hq
    by_contra hq_neg
    push_neg at hq_neg
    specialize hq (c/2-q) (by linarith)
    obtain ⟨N, hq⟩ := hq
    specialize hq N (by grind)
    specialize hpos N
    rw [abs_of_neg (show (q - a N) < 0 by linarith)] at hq
    simp at hq
    grind
  . intro hq
    use (fun _ ↦ q)
    refine ⟨?_, ?_, ?_⟩
    . rw [boundedAwayPos_def]
      use q; simp [hq]
    . exact (Sequence.IsCauchy.const q)
    . rw [ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  rw [isNeg_def]
  constructor
  . intro ⟨a, ⟨c, hc, hpos⟩, hcaucy, hq⟩
    rw [ratCast_def, LIM_eq_LIM (Sequence.IsCauchy.const q) hcaucy] at hq
    rw [Sequence.equiv_iff] at hq
    by_contra hq_pos
    push_neg at hq_pos
    specialize hq (c/2+q) (by linarith)
    obtain ⟨N, hq⟩ := hq
    specialize hq N (by grind)
    specialize hpos N
    rw [abs_of_pos (show (q - a N) > 0 by linarith)] at hq
    simp at hq
    grind
  . intro hq
    use (fun _ ↦ q)
    refine ⟨?_, ?_, ?_⟩
    . rw [boundedAwayNeg_def]
      use -q; simp [hq]
    . exact (Sequence.IsCauchy.const q)
    . rw [ratCast_def]

open Classical in
/-- Need to use classical logic here because {name}`IsPos` and {name}`IsNeg` are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  rw [gt_iff_lt, lt_iff, neg_iff_pos_of_neg]; simp;

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  rw [ge_iff_le, le_iff, gt_iff_lt]; grind

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  rw [lt_iff, ratCast_sub, Real.neg_of_coe]; simp

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.le_of_coe (q q':ℚ): q ≤ q' ↔ (q:Real) ≤ (q':Real) := by
  rw [le_iff]
  constructor
  . intro h
    have hq : q < q' ∨ q = q' := Rat.le_iff_eq_or_lt.mp h
    grind [lt_of_coe]
  . intro h
    rcases h with (h1 | h2)
    . have := (lt_of_coe q q').mpr h1
      grind
    . grind [Real.ratCast_inj]

theorem Real.ge_of_coe (q q':ℚ): q ≥ q' ↔ (q:Real) ≥ (q':Real) := by
  rw [ge_iff]
  constructor
  . intro h
    have hq : q' < q ∨ q' = q := Rat.le_iff_eq_or_lt.mp h
    grind [lt_of_coe]
  . intro h
    rcases h with (h1 | h2)
    . have := (gt_of_coe q q').mpr h1
      grind
    . grind [Real.ratCast_inj]

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by simp [Real.gt_iff x 0]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by simp [Real.lt_iff x 0]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  have h:= Real.trichotomous (x-y)
  have: x - y = 0 → x = y := by grind
  have: (x - y).IsPos → x > y := by grind [gt_iff]
  have: (x - y).IsNeg → x < y := by grind [lt_iff]
  grind

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]
  exact not_pos_neg (x-y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  have: x = y ↔ x - y = 0 := by grind
  rw [gt_iff, this]
  grind [not_zero_pos (x-y)]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  have: x = y ↔ x - y = 0 := by grind
  rw [lt_iff, this]
  grind [not_zero_neg (x-y)]

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  rw [lt_iff, gt_iff, neg_iff_pos_of_neg]; simp

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [lt_iff] at hxy hyz ⊢

  obtain ⟨a, ha_neg, ha_cauchy, ham⟩ := hxy
  obtain ⟨b, hb_neg, hb_cauchy, hbm⟩ := hyz

  rw [isNeg_def]
  use (a + b)

  refine ⟨?_, ?_, ?_⟩
  . obtain ⟨c, hc, hac⟩ := ha_neg
    obtain ⟨c', hc', hbc⟩ := hb_neg
    rw [boundedAwayNeg_def]
    use c + c'
    simp [show c + c' > 0 by linarith]
    grind
  . exact (Sequence.IsCauchy.add ha_cauchy hb_cauchy)
  . have h: (x - y) + (y - z) = x - z := by ring
    rw [ham, hbm] at h
    rw [←h]
    exact Real.LIM_add ha_cauchy hb_cauchy

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff]; simp
  rw [←gt_iff]; grind

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at hxy ⊢
  rcases hxy with (hlt | heq)
  . have h:= Real.mul_lt_mul_right hlt hz
    rw [mul_comm, mul_comm y z] at h
    grind
  . have: z * x = z * y := by grind
    grind

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  obtain ⟨a, hpos, ha_cauchy, hma⟩ := hx
  obtain ⟨b, hneg, hb_cauchy, hmb⟩ := hy
  rw [isNeg_def]
  use a * b
  refine ⟨?_, ?_, ?_⟩
  . rw [boundedAwayNeg_def]
    obtain ⟨c, hc, hac⟩ := hneg
    obtain ⟨d, hd, had⟩ := hpos
    use c*d; simp [show c*d > 0 by positivity]
    intro n;
    specialize hac n; specialize had n;
    have: - (b n) ≥ c := by grind
    have := mul_le_mul_of_nonneg this had (by grind) (by grind)
    grind
  . exact Sequence.IsCauchy.mul ha_cauchy hb_cauchy
  . rw [hma, hmb]
    exact Real.LIM_mul ha_cauchy hb_cauchy

open Classical in
/--
  (Not from textbook) {name}`Real` has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by intro a; rw [le_iff]; grind
  le_trans := by
    intro a b c h1 h2
    rw [le_iff] at h1 h2 ⊢
    rcases h1 with (h_lt_ab | heq_ab)
    . rcases h2 with (h_lt_ac | heq_ac)
      . grind [lt_trans h_lt_ab h_lt_ac]
      . rw [heq_ac] at h_lt_ab; grind
    . rcases h2 with (h_lt_ac | heq_ac)
      . rw [←heq_ab] at h_lt_ac; grind
      . grind
  lt_iff_le_not_ge := by
    intro a b;
    rw [le_iff, le_iff]; push_neg;
    constructor
    . intro hab; simp [hab]
      refine ⟨?_, ?_⟩
      . by_contra h1
        have := not_gt_and_lt a b
        simp [h1, hab] at this
      . by_contra h
        rw [h, lt_iff] at hab; simp at hab;
        have := not_zero_pos 0
        simp [hab] at this;
    . intro ⟨ h1, h2, h3 ⟩
      rcases h1 with (ha | hb)
      . exact ha
      . grind

  le_antisymm := by
    intro a b h1 h2
    rw [le_iff] at h1 h2
    rcases h1 with (ha | hb)
    . rcases h2 with (h3 | h4)
      . have := not_gt_and_lt a b
        simp [ha, h3] at this
      . grind
    . rcases h2 with (h3 | h4)
      . grind
      . grind

  le_total := by
    intro a b
    rw [le_iff, le_iff]
    rcases Real.trichotomous' a b with (hgt | heq | hlt)
    . grind
    . grind
    . grind

  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) {name}`LinearOrder`s come with a definition of absolute value {lean (type := "Real → Real")}`(|·|)`.
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by

  have: |x| = max x (-x) := by rfl

  rcases Real.trichotomous x with (hzero | hpos | hneg)
  · -- x = 0
    simp [hzero]; grind
  · -- x.IsPos → x > 0 → -x < x
    simp [hpos]
    have hnegx_lt_x : -x < x := by
      rw [lt_iff]; simp;
      exact pos_add hpos hpos
    grind
  · -- x.IsNeg → x < 0 → x ≤ -x
    simp [hneg]
    have hnegx_lt_x : x < -x := by
      rw [lt_iff]; simp;
      have hpos': (-x).IsPos := (neg_iff_pos_of_neg x).mp hneg
      exact pos_add hpos' hpos'
    grind

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq]
  exact pos_mul hx (inv_of_pos hy)

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) {name}`Real` has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hle c
    rw [le_iff] at hle ⊢
    rcases hle with (hlt | heq)
    . have := add_lt_add_right c hlt
      grind
    . grind

  add_le_add_right := by
    intro a b hle c
    rw [le_iff] at hle ⊢
    rcases hle with (hlt | heq)
    . have h1:= add_lt_add_right c hlt
      grind [add_comm]
    . grind

  mul_lt_mul_of_pos_left := by
    intro a ha b c hlt
    have: a.IsPos := by grind [Real.isPos_iff]
    have := mul_lt_mul_right hlt this
    grind [mul_comm]

  mul_lt_mul_of_pos_right := by
    intro a ha b c hlt
    have: a.IsPos := by grind [Real.isPos_iff]
    exact mul_lt_mul_right hlt this

  le_of_add_le_add_left := by
    intro a b c hle
    rw [le_iff] at hle ⊢
    rcases hle with (hlt | heq)
    . have := add_lt_add_right (-a) hlt
      simp at this
      grind
    . grind

  zero_le_one := by
    rw [le_iff]
    have h:= (pos_of_coe (1:ℚ)).mpr (show (1:ℚ) > 0 by linarith)
    rw [isPos_iff, gt_iff_lt] at h
    observe : (1:Real) = (1:ℚ)
    rw [←this] at h
    grind

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by

  let a := fun n:ℕ ↦ 1/((n:ℚ) + 1)
  use a; use (-a)

  have ha: (a:Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    simp [Section_4_3.dist]
    use ⌊2/ε⌋.toNat
    intro j hj k hk
    have: ⌊2/ε⌋ + 1 > 2/ε := by grind [Int.lt_floor_add_one]
    have: ⌊2/ε⌋.toNat = ⌊2/ε⌋ := by grind [Int.toNat_of_nonneg (show ⌊2/ε⌋ ≥ 0 by positivity)]
    qify at hj hk this
    have: j + 1 ≥ 2/ε := by linarith
    have hj_le:= (inv_le_inv₀ (show ((j:ℚ)+1) > 0 by positivity) (show 2/ε > 0 by positivity)).mpr this
    have: k + 1 ≥ 2/ε := by linarith
    have hk_le:= (inv_le_inv₀ (show ((k:ℚ)+1) > 0 by positivity) (show 2/ε > 0 by positivity)).mpr this
    simp at hj_le hk_le
    have: ((j:ℚ) + 1)⁻¹ ≥ 0 := by positivity
    have: ((k:ℚ) + 1)⁻¹ ≥ 0 := by positivity
    grind

  have ha_zero: LIM a = 0 := by
    rw [←LIM.zero, LIM_eq_LIM ha (Sequence.IsCauchy.const 0)]
    rw [Sequence.equiv_iff]
    intro ε hε
    simp; use ⌈1/ε⌉.toNat
    intro n hn
    simp [show |a n| = a n by grind]
    have h1: ⌈1 / ε⌉.toNat = ⌈1 / ε⌉ := by grind [Int.toNat_of_nonneg (show ⌈1 / ε⌉ ≥ 0 by positivity)]
    observe: ⌈1 / ε⌉ ≥ 1 / ε
    have: n + 1 > ⌈1 / ε⌉.toNat := by linarith
    qify at h1 this
    have: (n:ℚ) + 1 ≥ 1 / ε := by grind
    have h_le:= (inv_le_inv₀ (show ((n:ℚ) + 1) > 0 by positivity) (show 1/ε > 0 by positivity)).mpr this
    grind

  refine ⟨?_, ?_, ?_, ?_⟩
  . exact ha
  . exact Sequence.IsCauchy.neg a ha
  . intro n; simp; positivity
  . have h:= Real.neg_LIM a ha
    rw [ha_zero] at h; simp at h;
    have: LIM (a) = LIM (-a) := by grind
    grind

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by

  obtain ⟨xs, hx_cauchy, hx⟩ := x.eq_lim
  obtain ⟨ys, hy_cauchy, hy⟩ := y.eq_lim

  have hx_cauchy2 := hx_cauchy
  have hy_cauchy2 := hy_cauchy

  rw [lt_iff] at hxy

  rw [hx, hy, LIM_sub hx_cauchy hy_cauchy] at hxy

  obtain ⟨a, ⟨c, hc, ha_le⟩, ha_cauchy, hs_eq⟩ := hxy

  rw [LIM_eq_LIM (Sequence.IsCauchy.sub hx_cauchy hy_cauchy) ha_cauchy] at hs_eq
  rw [Sequence.equiv_iff] at hs_eq; simp at hs_eq

  rw [Sequence.IsCauchy.coe] at hx_cauchy hy_cauchy
  simp only [Section_4_3.dist] at hx_cauchy hy_cauchy

  specialize hx_cauchy (c/6) (by positivity)
  obtain ⟨m1, hx_cauchy⟩ := hx_cauchy

  specialize hy_cauchy (c/6) (by positivity)
  obtain ⟨m2, hy_cauchy⟩ := hy_cauchy

  specialize hs_eq (c/6) (by positivity)
  obtain ⟨ m3, hs_eq⟩ := hs_eq

  let N := max m3 (max m1 m2)

  specialize hx_cauchy N (by grind)
  specialize hy_cauchy N (by grind)

  let q := xs N + c/2
  use q

  rw [lt_iff, lt_iff]
  constructor
  . rw [hx, Real.ratCast_def q, LIM_sub hx_cauchy2 (Sequence.IsCauchy.const q)]
    rw [isNeg_def]
    let f:ℕ → ℚ := fun n ↦ if n < N then - c/6 else (xs n) - q
    use f

    have hf: (f:Sequence).IsCauchy := by
      rw [Sequence.IsCauchy.coe]
      intro ε hε
      choose M hm using (Sequence.IsCauchy.coe xs).mp hx_cauchy2 ε hε
      simp [Section_4_3.dist] at hm ⊢
      let t := (max M N)
      use t
      intro j hj k hk
      simp [f, show ¬(j < N) by grind, show ¬(k < N) by grind]
      specialize hm j (by grind) k (by grind)
      grind

    refine ⟨ ?_, ?_, ?_ ⟩
    . rw [boundedAwayNeg_def]; simp
      use c / 6; simp [hc]
      intro n
      by_cases hn: n < N
      . simp [f, hn]; grind
      . simp [f, hn, q]
        push_neg at hn
        specialize hx_cauchy n (by grind)
        grind
    . exact hf
    . rw [LIM_eq_LIM (Sequence.IsCauchy.sub hx_cauchy2 (Sequence.IsCauchy.const q)) hf]
      rw [Sequence.equiv_iff]
      simp; intro ε hε;
      use N; intro n hn; simp [f, show ¬(n < N) by grind]
      grind

  . rw [hy, Real.ratCast_def q, LIM_sub (Sequence.IsCauchy.const q) hy_cauchy2]
    rw [isNeg_def]
    let f:ℕ → ℚ := fun n ↦ if n < N then - c/6 else q - (ys n)
    use f

    have hf: (f:Sequence).IsCauchy := by
      rw [Sequence.IsCauchy.coe]
      intro ε hε
      choose M hm using (Sequence.IsCauchy.coe ys).mp hy_cauchy2 ε hε
      simp [Section_4_3.dist] at hm ⊢
      let t := (max M N)
      use t
      intro j hj k hk
      simp [f, show ¬(j < N) by grind, show ¬(k < N) by grind]
      specialize hm j (by grind) k (by grind)
      grind

    refine ⟨ ?_, ?_, ?_ ⟩
    . rw [boundedAwayNeg_def]; simp
      use c / 6; simp [hc]
      intro n
      by_cases hn: n < N
      . simp [f, hn]; grind
      . simp [f, hn, q]
        push_neg at hn
        specialize hx_cauchy n (by grind)
        specialize hy_cauchy n (by grind)
        specialize hs_eq n (by grind)
        specialize ha_le n
        grind
    . exact hf
    . rw [LIM_eq_LIM (Sequence.IsCauchy.sub (Sequence.IsCauchy.const q) hy_cauchy2) hf]
      rw [Sequence.equiv_iff]
      simp; intro ε hε;
      use N; intro n hn; simp [f, show ¬(n < N) by grind]
      grind

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  . -- exist
    -- (x - 0.1) < p < x < q < x + 0.1
    obtain ⟨p, hp1, hp2⟩ := rat_between (show (x - 0.1) < x by linarith)
    obtain ⟨q, hq1, hq2⟩ := rat_between (show x < x + 0.1 by linarith)

    -- (x - 1.1) < ⌊p⌋ ≤ p < x < q ≤ ⌈q⌉ < x + 1.1
    -- ⌈q⌉ = ⌊q⌋ + 1 or ⌊q⌋ + 2
    let p' := ⌊p⌋
    let q' := ⌈q⌉

    have: q' ≥ q := Int.le_ceil q
    have := (ge_of_coe q' q).mp this

    have: p ≥ p' := Int.floor_le p
    have := (ge_of_coe p p').mp this

    have: p < p' + 1 := Int.lt_floor_add_one p
    have hp':= (lt_of_coe p (p' + 1:ℚ)).mp this
    simp at hp'

    have: q' < q + 1 := Int.ceil_lt_add_one q
    have hq' := (lt_of_coe q' (q + 1)).mp this
    simp at hq'

    have hxp': x ≥ (p':ℚ) := by grind
    have hxq': x < (q':ℚ) := by grind
    norm_cast at hxp' hxq'

    -- 0 < (q' - p') < 3 --> q' = p' + 1 ∨ q' = p' + 2
    have: (q':Real) - (p':Real) < 3 := by linarith
    norm_cast at this

    have: q' > p' := by
      have: (q:Real) > p := by linarith
      have hg1: q > p := (gt_of_coe q p).mpr this
      have: (q':ℚ) > p' := by linarith
      norm_cast at this

    have: q' = p' + 1 ∨ q' = p' + 2 := by omega
    rcases this with (hpq1 | hpq2)
    . use p'
      qify at hpq1
      have := (Real.ratCast_inj q' (p'+1)).mpr hpq1
      simp at this; rw [←this]
      grind
    . by_cases h: x < p' + 1
      . grind
      . use p' + 1
        push_neg at h
        simp [h]
        qify at hpq2
        have := (Real.ratCast_inj q' (p'+2)).mpr hpq2
        simp at this
        grind

  . -- unique
    intro M N hM hN
    have h1: (M:Real) + 1 > N := by linarith
    have h2: (N:Real) + 1 > M := by linarith
    norm_cast at h1 h2
    have: N ≤ M := by grind
    have: M ≤ N := by grind
    grind

-- prove come from: https://github.com/rkirov/analysis/blob/main/Analysis/Section_5_4.lean
theorem Real.floor_exist2 (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  . wlog hx : x > 0
    . simp at hx
      by_cases h': x = 0
      . subst x
        use 0
        simp
      . have h: x < 0 := by grind
        specialize this (-x) (by linarith)
        obtain ⟨N, hN, hN'⟩ := this
        by_cases hx: (N:Real) = -x
        . use -N
          observe : x = -(N: Real)
          subst x
          simp
        use -N-1
        simp
        grind
    obtain ⟨M, hM, h⟩ := le_mul (ε := 1) (by exact (pos_of_coe ↑1).mpr rfl) x
    simp at h
    induction' M with M ih
    . contradiction
    . by_cases hM': (M:Real) ≤ x
      . use M
        simp [hM']
        norm_cast
      . simp at hM'
        by_cases hz: M = 0
        . subst M
          norm_cast at hM'
          linarith
        . have : M > 0 := by
            have : 0 ≤  M := by exact Nat.zero_le M
            rw [le_iff_lt_or_eq] at this
            aesop
          specialize ih this hM'
          exact ih
  . intro N N' hN hN'
    have h1 := lt_of_le_of_lt hN.1 hN'.2
    have h2 := lt_of_le_of_lt hN'.1 hN.2
    norm_cast at h1 h2
    have h1': N ≤ N' := by exact (Int.add_le_add_iff_right 1).mp h1
    have h2': N' ≤ N := by exact (Int.add_le_add_iff_right 1).mp h2
    exact Int.le_antisymm h1' h2'

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N > 0 ∧ (N:Real)⁻¹ < x := by
  obtain ⟨N, hN, hmul⟩ := Real.le_mul hx 1
  use N
  simp [hN]
  qify at hN
  have hpos: (N:Real).IsPos := (Real.pos_of_coe (N:ℚ)).mpr hN

  have:= (N:Real).not_zero_pos

  have h:= Real.mul_lt_mul_right hmul (Real.inv_of_pos hpos)
  simp at h
  rw [mul_comm, ←mul_assoc] at h
  have hinv := Real.inv_mul_self (show (N:Real) ≠ 0 by grind)
  rw [hinv] at h
  grind

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw [abs_eq_abs];
  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . have: (x-y).IsPos := by grind [Real.gt_iff]
    simp [this]
    grind
  . have: (x-y).IsNeg := by grind [Real.lt_iff]
    simp [this]
    grind

  . rw [heq]; simp;

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rw [abs_eq_abs];
  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . have: (x-y).IsPos := by grind [Real.gt_iff]
    simp [this]
    grind
  . have: (x-y).IsNeg := by grind [Real.lt_iff]
    simp [this]
    grind

  . rw [heq]; simp;

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  . intro h
    by_contra h1
    simp at h1
    simp [gt_iff] at h1
    have := Real.exists_rat_le_and_nat_gt h1
    obtain ⟨⟨q, hq, hq1⟩, _⟩ := this
    specialize h (q / 2) (by positivity)
    have: (q:Real) ≤ q / 2 := by linarith
    norm_cast at this
    grind
  . intro h;
    simp [le_iff] at h
    rcases h with (hlt | heq)
    . simp [gt_iff] at hlt
      intro ε hε
      have := Real.exists_rat_le_and_nat_gt hlt
      obtain ⟨⟨q, hq, hq1⟩, _⟩ := this
      have: x + ε + q ≤ y + ε := by grind
      have := (gt_of_coe q 0).mp hq
      have: ((0:ℚ):Real) = (0:Real) := by rfl
      grind
    . rw [heq]; grind

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  . rw [abs_eq_abs];
    rcases Real.trichotomous' x y with (hlt | hgt | heq)
    . have: (x-y).IsPos := by grind [Real.gt_iff]
      rw [abs_of_pos (x-y) this]
      intro h;
      have: ∀ ε > 0, x ≤ y + ε := by grind
      have := (le_add_eps_iff x y).mp this
      grind
    . have: (x-y).IsNeg := by grind [Real.lt_iff]
      rw [abs_of_neg (x-y) this]
      intro h;
      have: ∀ ε > 0, y ≤ x + ε := by grind
      have := (le_add_eps_iff y x).mp this
      grind
    . rw [heq]; simp
  . grind

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by

  by_contra h1
  simp at h1
  obtain ⟨q, hq1, hq2⟩ := Real.rat_between h1

  have: ∀ (n : ℕ), a n ≤ q := by grind [le_of_coe]

  have := LIM_mono hcauchy (Sequence.IsCauchy.const q) this
  have: LIM a ≤ q := by grind [ratCast_def]
  grind

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by

  by_contra h1
  simp at h1
  obtain ⟨q, hq1, hq2⟩ := Real.rat_between h1

  have: ∀ (n : ℕ), a n ≥ q := by grind [le_of_coe]

  have := LIM_mono (Sequence.IsCauchy.const q) hcauchy this
  have: LIM a ≥ q := by grind [ratCast_def]
  grind

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by grind

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by grind

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by grind

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by grind

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by grind

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by

  have (x y :Real) {z:Real} (hz: z.IsPos) (hxy: x < y): max (x * z) (y * z) = max x y * z := by
    have h:= Real.mul_lt_mul_right hxy hz
    rw [max_eq, max_eq]
    simp [show ¬(x ≥ y) by linarith]
    intro h1
    have := mul_le_mul_left h1 (show z⁻¹.IsPos by linarith)
    grind

  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . specialize this y x hz hlt; grind
  . grind
  . grind

/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by grind

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by grind

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by grind

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  have (x y :Real) {z:Real} (hz: z.IsPos) (hxy: x < y): min (x * z) (y * z) = min x y * z := by
    have h:= Real.mul_lt_mul_right hxy hz
    rw [min_eq, min_eq]
    simp [show x ≤ y by linarith]
    intro h1
    grind

  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . specialize this y x hz hlt; grind
  . grind
  . grind

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by

  have {x y :Real} (hx:x.IsPos) (hy:y.IsPos) (hxy: x < y): (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
    have h:= Real.mul_lt_mul_right hxy (inv_of_pos hx)
    simp [self_mul_inv (show x ≠ 0 by grind [x.not_zero_pos])] at h
    have h1:= Real.mul_lt_mul_right h (inv_of_pos hy); simp at h1
    rw [mul_comm, ←mul_assoc, mul_comm y⁻¹ y] at h1
    simp [self_mul_inv (show y ≠ 0 by grind [y.not_zero_pos])] at h1
    simp [show (x ≤ y) by linarith]
    grind

  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . specialize this hy hx hlt; grind
  . grind
  . grind

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  have {x y :Real} (hx:x.IsPos) (hy:y.IsPos) (hxy: x < y): (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
    have h:= Real.mul_lt_mul_right hxy (inv_of_pos hx)
    simp [self_mul_inv (show x ≠ 0 by grind [x.not_zero_pos])] at h
    have h1:= Real.mul_lt_mul_right h (inv_of_pos hy); simp at h1
    rw [mul_comm, ←mul_assoc, mul_comm y⁻¹ y] at h1
    simp [self_mul_inv (show y ≠ 0 by grind [y.not_zero_pos])] at h1
    simp [show (x ≤ y) by linarith]
    grind

  rcases Real.trichotomous' x y with (hlt | hgt | heq)
  . specialize this hy hx hlt; grind
  . grind
  . grind

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    simp
    intro x y h
    simp [ratCast_def]
    apply LIM_mono (Sequence.IsCauchy.const x) (Sequence.IsCauchy.const y)
    intro n
    exact h

end Chapter5

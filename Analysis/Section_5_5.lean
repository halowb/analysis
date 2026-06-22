import Mathlib.Tactic
import Analysis.Section_5_4
import Analysis.Section_4_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds). Here we use the {name}`upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def, Real.Icc_def]
  constructor
  . intro h
    specialize h 1; simp at h; grind
  . intro h
    grind

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  by_contra h
  obtain ⟨M, hM⟩ := h
  rw [Real.upperBound_def, Real.Ioi_def] at hM
  have h1:= hM 1; simp at h1;
  have h2:= hM (M + 1); simp at h2;
  simp [show M + 1 > 0 by linarith] at h2
  linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M
  rw [Real.upperBound_def]
  grind

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by

  rw [Real.upperBound_def] at hb ⊢
  intro x hx
  specialize hb x
  simp [hx] at hb
  linarith

/-- Definition 5.5.5 (least upper bound).  Here we use the {name}`IsLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  rw [Real.isLUB_def, Real.upperBound_def, Real.Icc_def]
  constructor
  . grind
  . intro M' hM'
    rw [Real.upperBound_def] at hM'
    specialize hM' 1
    simp at hM'
    linarith

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  by_contra h
  obtain ⟨M, hM⟩ := h
  rw [Real.isLUB_def] at hM
  obtain ⟨ h1, h2 ⟩ := hM
  specialize h2 (M-1)
  have: M - 1 ∈ upperBounds ∅ := by grind [Real.upperBound_def]
  simp at h2
  linarith

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  grind [Real.isLUB_def]

/-- Definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by

  simp at hL hK

  by_contra h
  push_neg at h
  have h1: ∀ i:ℕ, L ≤ (K - i) → (K - i) * ((1/(n+1):ℚ):Real) ∈ upperBounds E := by
    intro i
    induction' i with i ih
    . simp [show L ≤ K by linarith]; exact hK
    . specialize h (K - i)
      intro h1
      have h2: L < K - i := by omega
      simp [h2] at h
      simp [show L ≤ K - i by linarith] at ih
      simp [ih] at h
      simp; grind

  specialize h1 (K - L).toNat
  norm_cast at h1
  have: K - (K - L).toNat = L := by grind
  rw [this] at h1
  simp at h1
  contradiction

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by

  rw [Real.upperBound_def] at hm1 hm2 hm'1 hm'2
  push_neg at hm2 hm'2
  simp_all

  have hpos: ((n:Real) + 1)⁻¹.IsPos := by
    rw [isPos_iff]; positivity

  rcases lt_trichotomy m m' with hlt | heq | hgt
  . obtain ⟨x, hx1, hx2⟩ := hm'2
    specialize hm1 x hx1
    have: m  ≤ m' - 1 := by omega
    qify at this
    have: ((m:ℚ):Real) ≤ (((m'-1):ℚ):Real) := by grind [Real.le_of_coe]
    simp at this

    have := mul_le_mul_left this hpos
    -- contradiction: hx2 hm1
    grind

  . exact heq
  . obtain ⟨x, hx1, hx2⟩ := hm2
    specialize hm'1 x hx1

    have: m - 1 ≥ m' := by omega
    qify at this
    have: (((m-1):ℚ):Real) ≥ ((m':ℚ):Real) := by grind [Real.ge_of_coe]
    simp at this

    have := mul_le_mul_left this hpos
    -- contradiction: hx2 hm'1
    grind

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by

  rw [Sequence.IsCauchy.coe] at ha ⊢
  simp [Section_4_3.dist_eq] at ha ⊢
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, hN⟩ := ha
  use N
  grind

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by

  rw [LIM_eq_LIM ha hb, Sequence.equiv_iff] at h
  rw [LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb), Sequence.equiv_iff]

  intro ε hε
  specialize h ε hε
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn

  have: |a| n - |b| n = |a n| - |b n| := by rfl
  grind

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by

  rw [LIM_eq_LIM ha (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
  rw [←Real.isPos_iff] at h
  obtain ⟨a', ⟨c, hcpos, hc⟩, ha'cauchy, ha'⟩ := h
  rw [LIM_eq_LIM ha ha'cauchy, Sequence.equiv_iff] at ha'
  intro ε hε
  specialize ha' c hcpos
  obtain ⟨N, hN⟩ := ha'
  use N
  intro n hn
  specialize hN n hn
  specialize hc n
  have: |a| n = |a n| := by rfl
  grind

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by

  rcases Real.trichotomous' (LIM a) 0 with (hgz | hlz | hz)
  . have := Real.LIM.abs_eq_pos hgz ha; grind
  . have hneg: -LIM a = LIM (-a) := Real.neg_LIM a ha
    have ha' := (Sequence.IsCauchy.neg a ha)
    have: LIM (-a) > 0 := by grind
    have h:= Real.LIM.abs_eq_pos this ha'
    rw [←hneg] at h
    have: LIM |(-a)| = LIM |a| := by
      rw [Real.LIM_eq_LIM (Sequence.IsCauchy.abs ha') (Sequence.IsCauchy.abs ha)]
      rw [Sequence.equiv_iff]
      simp
      intro ε hε; use 0;
      grind
    grind
  . rw [hz]; simp;
    rw [←LIM.zero, LIM_eq_LIM ha (Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hz
    simp at hz
    rw [←LIM.zero, LIM_eq_LIM (Sequence.IsCauchy.const 0) (Sequence.IsCauchy.abs ha)]
    rw [Sequence.equiv_iff]
    simp; exact hz

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by

  obtain ⟨N, hN⟩ := h

  let b := fun n ↦ a (n + N)

  have heq: Sequence.Equiv a b := Sequence.equiv_sub_seq a hcauchy b (by rfl)

  have hb_cauchy : (b:Sequence).IsCauchy := (Sequence.isCauchy_of_equiv heq).mp hcauchy

  have: ∀ (n:ℕ), b n ≤ x := by grind
  have : LIM b ≤ x := Real.LIM_of_le hb_cauchy this

  have : LIM a = LIM b := (Real.LIM_eq_LIM hcauchy hb_cauchy).mpr heq

  grind

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by

  have hcauchy : (q:Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]; simp [Section_4_3.dist_eq]
    intro ε hε
    have hpos: (ε:Real).IsPos := by simp [Real.isPos_iff]; exact hε
    have := Real.le_mul hpos 1
    obtain ⟨M, hM, hgt⟩ := this
    specialize hq (M-1)
    use M-1

    intro j hj k hk
    specialize hq j hj k hk
    have : (M - 1) + 1 = M := by grind
    qify at this
    simp [this] at hq

    norm_cast at hgt
    have: (↑M)⁻¹ < ε := by field_simp; exact hgt
    linarith

  constructor
  . exact hcauchy
  . intro M
    let q' := fun n ↦ q (n + M)
    have heq: Sequence.Equiv q q' := Sequence.equiv_sub_seq q hcauchy q' (by rfl)
    have hq'cauchy := (Sequence.isCauchy_of_equiv heq).mp hcauchy
    have heq_lim := (Real.LIM_eq_LIM hcauchy hq'cauchy).mpr heq

    let b := fun n ↦ |q M - q' n|
    have hb_cauchy: (b:Sequence).IsCauchy := by
      have := Sequence.IsCauchy.sub (Sequence.IsCauchy.const (q M)) hq'cauchy
      have := Sequence.IsCauchy.abs this
      grind

    have: ∀ (n:ℕ), b n ≤ 1 / (↑M + 1) := by grind
    have hle:= Real.LIM_mono hb_cauchy (Sequence.IsCauchy.const (1 / (↑M + 1))) this
    simp [b, ←Real.ratCast_def] at hle

    rw [heq_lim]
    rw [ratCast_def, Real.LIM_sub (Sequence.IsCauchy.const (q M)) hq'cauchy]
    have := Sequence.IsCauchy.sub (Sequence.IsCauchy.const (q M)) hq'cauchy
    have h_abs_cauchy := Sequence.IsCauchy.abs this
    rw [Real.LIM_abs this]
    simp;

    let b' := |(fun x ↦ q M) - q'|

    have: b = b' := by ext n; simp [b, b']

    grind

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound
    obtain ⟨ M, hbound ⟩ := hbound

    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]

    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem

  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ ((m n):ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)

  have hb : (b:Sequence).IsCauchy := .harmonic'

  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hm1 (n:ℕ) : (a n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ((a - b) n: Real) ∉ upperBounds E := (claim1 n).exists.choose_spec.2

  have claim2 (N:ℕ) := LUB_claim2 N (by grind) hm1 hm2
  have ha : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1

  -- S = LIM a = LIM (a-b)
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub ha hb, S, this]

  rw [isLUB_def, upperBound_def]

  constructor
  . -- S ∈ upperBounds
    intro x hx
    apply LIM_of_ge ha
    intro n
    exact (upperBound_def E (a n)).mp (hm1 n) x hx
  . -- S is the least upper bound
    intro y hy
    have claim5 (n:ℕ) : y ≥ (a-b) n := by
      contrapose! hm2;
      use n;
      apply upperBound_upper _ hy;
      order
    rw [claim4]
    apply LIM_of_le _ claim5
    exact Sequence.IsCauchy.sub ha hb

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers {syntax term}`⊤` to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers {syntax term}`⊥` to denote the -∞ element. -/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two: ∃ x:Real, x^2 = 2 := by
  set E := { x:Real | x ≥ 0 ∧ x^2 < 2 }

  have h2upper: 2 ∈ upperBounds E := by
    intro x ⟨hx1, hx2⟩
    have: x^2 < 2^2 := by grind
    have: x < 2 := by grind [sq_lt_sq₀]
    linarith

  have hbound: BddAbove E := by rw [Real.bddAbove_def]; use 2

  have hone: 1 ∈ E := by simp [E]
  observe hnon: E.Nonempty

  obtain ⟨c, hLUB⟩ := Real.LUB_exist hnon hbound
  rw [Real.isLUB_def] at hLUB
  obtain ⟨hUB, hLUB⟩ := hLUB
  rw [Real.upperBound_def] at hUB

  have hc1: c ≥ 1 := hUB 1 hone
  have hc2: c ≤ 2 := hLUB 2 h2upper

  rcases Real.trichotomous' (c^2) 2 with (hgt | hlt | heq)
  . have: ∃ e, 0 < e ∧ e ≤ 1 ∧ (c - e)^2 ≥ 2 := by
      let a := c^2 - 2
      let b := a / (2 * c)
      use b
      have hb: b > 0 := by
        observe: a > 0
        have: c > 0 := by positivity
        positivity
      simp [hb]
      constructor
      . simp [b, a]; field_simp
        have: c^2 ≤ 2^2 := by grind [sq_le_sq₀]
        calc _ ≤ 2^2 - 2 := by grind
          _ = (2:Real) := by grind
          _ ≤ c * 2:= by grind
      . have: (c - b) ^ 2 - 2 > 0 := by
          calc _ = c^2 - 2 * c * b + b^2 - 2 := by grind
            _ = a - a + b^2 := by grind
            _ = b^2         := by grind
            _ > 0           := by positivity
        grind

    obtain ⟨e, he0, he1, he2⟩ := this

    have hup: (c - e) ∈ upperBounds E := by
      intro x ⟨hx1, hx2⟩
      have: (c - e)^2 > x^2 := by grind
      have: c - e > x := by grind [sq_lt_sq₀]
      linarith

    have: c - e ≥ c := hLUB (c-e) hup
    linarith
  . have: ∃ e, 0 < e ∧ (c + e)^2 < 2 := by
      let a := 2 - c^2
      let b := a / (4 * c)
      use b
      have hb: b > 0 := by
        observe: a > 0
        have: c > 0 := by positivity
        positivity
      simp [hb]

      have: 2 * c - b > 0 := by
        simp [b]; field_simp
        have: c^2 ≥ 1^2 := by grind [sq_le_sq₀]
        grind

      have: 2 - (c + b) ^ 2 > 0 := by
        calc _ = 2 - c^2 - 2 * c * b - b^2 := by grind
          _ = a - a / 2 - b^2 := by grind
          _ = a/(4*c) * (2*c - b) := by grind
          _ > 0 := by positivity

      grind

    obtain ⟨e, he0, he1⟩ := this
    have: c+e ∈ E := by simp [E]; grind

    have: c + e ≤ c := hUB (c+e) this
    linarith

  . use c

theorem Real.exist_sqrt_two2 : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by
      have: (x - ε)^2 > y^2 := by grind
      have: (x - ε) > y := by grind [sq_lt_sq₀]
      grind

    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  obtain ⟨c, hc⟩ := Real.exist_sqrt_two2
  use c
  by_contra h
  obtain ⟨q, hq⟩ := h
  rw [hq] at hc
  norm_cast at hc
  have := Rat.not_exist_sqrt_two
  grind

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

theorem Real.lowerBound_upperBound (E: Set Real): M ∈ upperBounds E ↔ -M ∈ lowerBounds (-E) := by
  rw [upperBound_def, lowerBound_def]

  constructor
  . intro hx x hE
    observe: -x ∈ E
    specialize hx (-x) this
    linarith
  . intro hx x hE
    observe: -x ∈ -E
    specialize hx (-x) this
    linarith

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by

  rw [isLUB_def] at h
  obtain ⟨h1, h2⟩ := h
  rw [isGLB_def]
  constructor
  . exact (lowerBound_upperBound E).mp h1
  . intro M' hM'
    rw [show M' = -(-M') by simp] at hM'
    have: (-M') ∈ upperBounds E := (lowerBound_upperBound E).mpr hM'
    specialize h2 (-M') this
    linarith

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by

  observe hE': Set.Nonempty (-E)

  obtain ⟨M, hM⟩ := hbound

  rw [show E = -(-E) by simp] at hM
  rw [show M = -(-M) by simp] at hM
  have: -M ∈ upperBounds (-E) := (lowerBound_upperBound (-E)).mpr hM
  have: BddAbove (-E) := by rw [bddAbove_def]; grind

  obtain ⟨S, hs⟩ := Real.LUB_exist hE' this

  have := Real.inf_neg hs
  simp at this
  use -S

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by

  choose q hq1 hq2 using Real.rat_between hxy
  choose z hz using Real.exist_irrational

  -- use: q + (z / M)
  have hexist {z:Real} (h: z > 0) (hnq: ¬ ∃ q:ℚ, z = (q:Real)) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by

    let d := y - q
    observe hdpos: d.IsPos
    choose M hM1 hM2 using Real.le_mul hdpos z
    have: z / M < (y - q) := by field_simp; grind
    let a := q + (z / M)
    have: z / M > 0 := by positivity
    use a
    simp [show a > x by linarith, show a < y by linarith]
    intro p
    by_contra hp
    simp [a] at hp
    field_simp at hp
    have: z = M * (p - q) := by grind
    let q':ℚ := M * (p - q)
    have: ∃ q:ℚ, z = (q:Real) := by use q'; simp [q']; grind
    contradiction

  rcases Real.trichotomous' z 0 with (hgt | hlt | heq)
  . exact hexist hgt hz
  . have hz': ¬∃ q:ℚ, (-z) = q := by
      by_contra h
      choose q' hq' using h
      have: z = -q' := by grind
      have: ∃ q:ℚ, z = q := by use (-q'); rw [this]; norm_cast;
      grind

    exact hexist (show (-z) > 0 by linarith) hz'
  . have: ∃ (q:ℚ), z = q := by use 0; simp; grind
    grind

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the {name}`sSup` operation to build a conditionally complete lattice structure on {name}`Real`. -/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5

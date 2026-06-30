import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  rw [Sequence.sup]
  apply IsLUB.sSup_eq

  rw [isLUB_iff_le_iff]
  intro M

  constructor
  . rw [upperBounds]; simp;
    intro hM a m hm h
    lift m to ℕ using hm
    simp at h

    by_cases h1 : Even m
    . have hodd: Odd (m+1) := by grind
      rw [hodd.neg_one_pow] at h
      simp [h]
      have: (-1:EReal) ≤ 1 := by apply EReal.coe_le_coe; norm_num;
      grind
    . have: Odd m := by grind
      have heven: Even (m+1) := by grind
      rw [heven.neg_one_pow] at h
      simp [h]
      grind
  . intro h
    apply h; simp
    use 1; simp

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  rw [Sequence.inf]
  apply IsGLB.sInf_eq

  rw [isGLB_iff_le_iff]
  intro M

  constructor
  . rw [lowerBounds]; simp;
    intro hM a m hm h
    lift m to ℕ using hm
    simp at h

    by_cases h1 : Even m
    . have hodd: Odd (m+1) := by grind
      rw [hodd.neg_one_pow] at h
      simp [h]
      have: (-1:EReal) ≤ 1 := by apply EReal.coe_le_coe; norm_num;
      grind
    . have: Odd m := by grind
      have heven: Even (m+1) := by grind
      rw [heven.neg_one_pow] at h
      simp [h]
      have: (-1:EReal) ≤ 1 := by apply EReal.coe_le_coe; norm_num;
      grind
  . intro h
    apply h; simp
    use 0; simp

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  rw [Sequence.sup]
  apply le_antisymm -- a ≥ b ∧ b ≥ a → a = b
  . apply csSup_le
    . simp; use 1; use 0; simp
    . simp
      intro h x hx h2
      lift x to ℕ using hx
      simp at h2
      rw [h2]
      apply EReal.coe_le_coe
      field_simp; simp;
  . apply le_csSup
    . simp
    . use 0; simp

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  rw [Sequence.inf]
  apply IsGLB.sInf_eq

  rw [isGLB_iff_le_iff]
  intro M

  constructor
  . rw [lowerBounds]; simp;
    intro hM a m hm h
    lift m to ℕ using hm
    simp at h
    rw [h]
    have: (0:EReal) ≤ ((m:ℝ) + 1)⁻¹ := by apply EReal.coe_le_coe; field_simp; simp
    grind
  . rw [lowerBounds]
    intro h
    simp at h;
    by_contra hm
    push_neg at hm
    cases M with
    | bot => contradiction
    | top =>
      specialize h (a:=1) 0 (by grind)
      simp at h
      contradiction
    | coe r =>
      simp only [EReal.coe_pos] at hm
      -- r > 0, find n with 1/(n+1) < r
      set n := ⌈1/r⌉₊

      specialize h (a:=1/(n+1)) n (by linarith)
      simp at h
      have: ((n:EReal) + 1)⁻¹ = (((n+1):ℝ))⁻¹ := by simp [EReal.coe_inv]
      simp [this] at h
      field_simp at h

      have h1 : 1/r ≤ n := Nat.le_ceil (1/r)
      field_simp at h1
      have: r * (↑n + 1) ≤ r * ↑n := by linarith
      field_simp at this; simp at this;
      grind

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  rw [Sequence.sup]
  apply IsLUB.sSup_eq

  rw [isLUB_iff_le_iff]
  intro M

  constructor
  . rw [upperBounds]; simp;
    intro hM a m hm h
    lift m to ℕ using hm
    simp at h
    rw [h, show M = ⊤ by grind]
    exact le_top
  . rw [upperBounds]; simp;
    intro h
    by_contra hm
    push_neg at hm
    cases M with
    | bot => specialize h (a:=1) 0 (by grind); simp at h; contradiction
    | top => contradiction
    | coe M =>
      set n := ⌈M⌉₊
      specialize h (a:=n+1) n (by linarith)
      simp at h
      have h1 := EReal.coe_le_coe_iff.mp h; simp at h1
      have h2 : M ≤ n := Nat.le_ceil (M)

      have: (↑n + 1) ≤ ↑n := by linarith
      simp at this

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  rw [Sequence.inf]
  apply IsGLB.sInf_eq

  rw [isGLB_iff_le_iff]
  intro M

  constructor
  . rw [lowerBounds]; simp;
    intro hM a m hm h
    lift m to ℕ using hm
    simp at h
    have h1: m + 1 ≥ (1:ℝ) := by grind
    have h2 := EReal.coe_le_coe_iff.mpr h1; simp at h2
    rw [←h] at h2
    grind
  . intro h
    apply h; simp
    use 0; simp

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  rw [Sequence.IsBounded, Sequence.BddAbove, Sequence.BddBelow]
  constructor
  . intro ⟨M, hM, hBound⟩
    rw [Sequence.BoundedBy] at hBound
    constructor
    . use M; rw [Sequence.BddAboveBy]
      intro n hn
      specialize hBound n
      grind
    . use (-M)
      rw [Sequence.BddBelowBy]
      intro n hn
      specialize hBound n
      grind
  . intro ⟨⟨M1, hAbove⟩, ⟨M2, hBelow⟩⟩
    rw [Sequence.BddAboveBy] at hAbove
    rw [Sequence.BddBelowBy] at hBelow

    use max |M1| |M2|

    rw [Sequence.BoundedBy]
    simp;
    intro n
    specialize hAbove n
    specialize hBelow n
    by_cases hn: n < a.m
    . have: a.seq n = 0 := a.vanish n hn
      simp [this]
    . push_neg at hn
      simp [hn] at hAbove hBelow
      grind

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by

  obtain ⟨h1, h2⟩ := (Sequence.bounded_iff a).mp h

  obtain ⟨M1, hAbove⟩ := h1; rw [BddAboveBy] at hAbove
  obtain ⟨M2, hBelow⟩ := h2; rw [BddBelowBy] at hBelow

  have h1: a.sup ≤ M1 := by
    apply sSup_le
    simp; intro x n hn hx; rw [hx];
    specialize hAbove n hn
    apply EReal.coe_le_coe; exact hAbove

  have h2: a.sup ≥ M2 := by
    specialize hBelow a.m (by grind)
    have:= EReal.coe_le_coe_iff.mpr hBelow
    have: a.sup ≥ a.seq a.m := by
      apply le_sSup; simp; use a.m
    grind

  rcases EReal.def a.sup <;> grind

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  obtain ⟨h1, h2⟩ := (Sequence.bounded_iff a).mp h

  obtain ⟨M1, hAbove⟩ := h1; rw [BddAboveBy] at hAbove
  obtain ⟨M2, hBelow⟩ := h2; rw [BddBelowBy] at hBelow

  have h1: a.inf ≥ M2 := by
    apply le_sInf
    simp; intro x n hn hx; rw [hx];
    specialize hBelow n hn
    apply EReal.coe_le_coe; exact hBelow

  have h2: a.inf ≤ M1 := by
    specialize hAbove a.m (by grind)
    have:= EReal.coe_le_coe_iff.mpr hAbove
    have: a.inf ≤ a.seq a.m := by
      apply sInf_le; simp;
      use a.m
    grind

  rcases EReal.def a.inf <;> grind

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
  rw [Sequence.sup]; apply le_sSup; use n;

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  rw [Sequence.sup]; apply sSup_le;
  intro b ⟨n, hn1, hn2⟩
  rw [hn2]
  exact h n hn1

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by

  set S := { x | ∃ n ≥ a.m, x = ((a n):EReal) }

  have: ∃ n ≥ a.m, y < a n := by
    by_contra h1
    push_neg at h1
    have: ∀ x ∈ S, x ≤ y := by grind
    have h2:= sSup_le this
    -- contradiction h h2
    grind

  obtain ⟨n, hn1, hn2⟩ := this
  use n
  simp [hn1, hn2]
  exact Sequence.le_sup hn1

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
  rw [Sequence.inf]; apply sInf_le; use n

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  rw [Sequence.inf]; apply le_sInf;
  intro b ⟨n, hn1, hn2⟩
  rw [hn2]
  exact h n hn1

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by

  set S := { x | ∃ n ≥ a.m, x = ((a n):EReal) }

  have: ∃ n ≥ a.m, y > a n := by
    by_contra h1
    push_neg at h1
    have: ∀ x ∈ S, x ≥ y := by grind
    have h2:= le_sInf this
    -- contradiction h h2
    grind

  obtain ⟨n, hn1, hn2⟩ := this
  use n
  simp [hn1, hn2]
  exact Sequence.ge_inf hn1

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

private theorem Sequence.IsMonotone_iff {a:Sequence} {i j:ℤ} (hmono: a.IsMonotone) (h1: i ≥ a.m) (h2: j ≥ i)
  : a.seq j ≥ a.seq i := by

  simp [Sequence.IsMonotone] at hmono

  have hk: ∀ k:ℕ, a.seq (i + k) ≥ a.seq i := by
    intro k
    induction' k with k ih
    . grind
    . specialize hmono (i + k) (by grind)
      grind

  specialize hk (j - i).toNat
  simp [h2] at hk; grind

private theorem Sequence.IsAntitone_iff {a:Sequence} {i j:ℤ} (hanti: a.IsAntitone) (h1: i ≥ a.m) (h2: j ≥ i)
  : a.seq j ≤ a.seq i := by

  simp [Sequence.IsAntitone] at hanti

  have hk: ∀ k:ℕ, a.seq (i + k) ≤ a.seq i := by
    intro k
    induction' k with k ih
    . grind
    . specialize hanti (i + k) (by grind)
      grind

  specialize hk (j - i).toNat
  simp [h2] at hk; grind

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
private lemma Sequence.monotone_tendsTo_sup {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
  ∃ L, a.TendsTo L ∧ L = a.sup := by

  rw [Sequence.IsMonotone] at hmono

  have hBelow: a.BddBelow := by
    rw [Sequence.BddBelow]
    use a.seq a.m
    rw [Sequence.BddBelowBy]
    grind [Sequence.IsMonotone_iff]

  have hIsBound := (Sequence.bounded_iff a).mpr ⟨hbound, hBelow⟩
  obtain ⟨M, hM⟩ := Sequence.sup_of_bounded hIsBound
  use M
  simp [hM]

  rw [Sequence.tendsTo_iff]
  intro ε hε

  have hlt: a.sup - ε < a.sup := by
    rw [←hM]
    apply EReal.coe_lt_coe
    simp; grind

  obtain ⟨N, hN, h1, h2⟩ := Sequence.exists_between_lt_sup hlt
  rw [←hM] at h1 h2
  have h1 := EReal.coe_lt_coe_iff.mp h1; simp at h1
  simp [EReal.coe_le_coe_iff] at h2
  use N
  intro n hn
  have hnN := Sequence.IsMonotone_iff hmono hN hn
  have han: M ≥ a.seq n := by
    have h:=Sequence.le_sup (show n ≥ a.m by linarith);
    rw [←hM] at h
    grind [EReal.coe_le_coe_iff]

  have: |a.seq N - M| ≤ ε := by grind

  grind

theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by

  choose L h1 h2 using Sequence.monotone_tendsTo_sup hbound hmono
  use L

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by

  choose L h1 h2 using Sequence.monotone_tendsTo_sup hbound hmono
  rw [Sequence.lim_eq] at h1
  grind

private lemma Sequence.antitone_tendsTo_inf {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
  ∃ L, a.TendsTo L ∧ L = a.inf := by

  rw [Sequence.IsAntitone] at hmono

  have hAbove: a.BddAbove := by
    rw [Sequence.BddAbove]
    use a.seq a.m
    rw [Sequence.BddAboveBy]
    grind [Sequence.IsAntitone_iff]

  have hIsBound := (Sequence.bounded_iff a).mpr ⟨hAbove, hbound⟩
  obtain ⟨M, hM⟩ := Sequence.inf_of_bounded hIsBound
  use M
  simp [hM]

  rw [Sequence.tendsTo_iff]
  intro ε hε

  have hgt: a.inf + ε > a.inf := by
    rw [←hM]
    apply EReal.coe_lt_coe
    simp; grind

  obtain ⟨N, hN, h1, h2⟩ := Sequence.exists_between_gt_inf hgt
  rw [←hM] at h1 h2
  have h1 := EReal.coe_lt_coe_iff.mp h1; simp at h1
  simp [EReal.coe_le_coe_iff] at h2
  use N
  intro n hn
  have hnN := Sequence.IsAntitone_iff hmono hN hn
  have han: a.seq n ≥ M := by
    have h := Sequence.ge_inf (show n ≥ a.m by linarith);
    rw [←hM] at h
    grind [EReal.coe_le_coe_iff]

  have: |a.seq N - M| ≤ ε := by grind

  grind

theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by

  choose L h1 h2 using Sequence.antitone_tendsTo_inf hbound hmono
  use L

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by

  choose L h1 h2 using Sequence.antitone_tendsTo_inf hbound hmono
  rw [Sequence.lim_eq] at h1
  grind

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by

  constructor
  · exact bounded_of_convergent
  · intro hb; exact a.convergent_of_monotone (a.bounded_iff.mp hb).1 ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by

  constructor
  · exact bounded_of_convergent
  · intro hb; exact a.convergent_of_antitone (a.bounded_iff.mp hb).2 ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
private lemma Ex6_3_9_Monotone : (Example_6_3_9:Sequence).IsMonotone := by

  rw [Sequence.IsMonotone];
  have hm: (Example_6_3_9:Sequence).m = 0 := by rfl
  intro n hn
  simp_all
  simp [Example_6_3_9, show n+1≥0 by linarith]
  have: (10:ℝ) ^ (n + 1).toNat = 10 ^ (n.toNat + 1) := by grind
  rw [this, pow_add]
  field_simp; norm_cast; simp;

  set m := Real.pi * 10 ^ n.toNat

  have h1 := Int.floor_le m
  have h2 := Int.lt_floor_add_one (m * 10)

  have: (10:ℝ) * ⌊m⌋ < ⌊m * 10⌋ + 1 := by grind
  norm_cast at this
  grind

/-- Example 6.3.9 -/
private lemma Ex6_3_9_Above : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  --have hm: (Example_6_3_9:Sequence).m = 0 := by rfl
  rw [Sequence.BddAboveBy]
  simp [Example_6_3_9]
  intro n hn; simp [hn]
  field_simp; norm_cast; simp;
  have := Real.pi_le_four
  have h1: Real.pi * (10:ℝ) ^ n.toNat ≤ 4 * (10:ℝ) ^ n.toNat := by field_simp; grind

  have := Int.floor_le_floor h1

  have h2 := Int.floor_le (4 * (10:ℝ) ^ n.toNat)
  norm_cast at h2

  grind

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by

  exact Sequence.convergent_of_monotone ⟨4, Ex6_3_9_Above⟩ (Ex6_3_9_Monotone)

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by

  choose L h1 h2 using Sequence.monotone_tendsTo_sup ⟨4, Ex6_3_9_Above⟩ (Ex6_3_9_Monotone)
  rw [Sequence.lim_eq] at h1
  rw [h1.right]

  have h1:= Ex6_3_9_Above
  rw [Sequence.BddAboveBy] at h1
  simp at h1

  have h3: (Example_6_3_9:Sequence).sup ≤ 4 := by
    apply sSup_le
    intro x hx; simp at hx
    obtain ⟨n ,hn, hx⟩ := hx
    simp [hn] at hx
    specialize h1 n hn
    simp [hn] at h1
    rw [hx]
    apply EReal.coe_le_coe
    grind

  rw [←h2] at h3
  exact EReal.coe_le_coe_iff.mp h3

/-- Proposition 6.3.10-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have ham: a.m = 0 := by rfl
  have why : a.IsAntitone := by
    rw [Sequence.IsAntitone]
    intro n hn
    simp [ham] at hn
    lift n to ℕ using hn
    simp [a, show (n:ℤ)+1≥0 by linarith]
    rw [pow_add]; field_simp; grind

  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]

  set b :=  ((fun (n:ℕ) ↦ x^(n+1)):Sequence)
  have why2 : lim b = lim a := by

    have hta:= Sequence.lim_eq.mpr ⟨hconv, (show lim a = L by rfl)⟩
    rw [Sequence.tendsTo_iff] at hta

    have htb: b.TendsTo L := by
      rw [Sequence.tendsTo_iff]
      intro ε hε
      specialize hta ε hε
      obtain ⟨N, hN⟩ := hta
      simp [a] at hN
      use max N 0
      simp [b]
      intro n hn1 hn2
      specialize hN (n+1) (by linarith)
      simp [hn2]
      simp [show n+1≥0 by linarith] at hN
      have: (n + 1).toNat = n.toNat + 1 := by grind
      grind

    have ⟨hm1, hm2⟩:= Sequence.lim_eq.mp htb
    simp [L] at hm2
    exact hm2

  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hx: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
  by_contra h

  have hbound := Sequence.bounded_of_convergent h
  rw [Sequence.isBounded_def] at hbound
  obtain ⟨M, hM, hbound⟩ := hbound
  rw [Sequence.BoundedBy] at hbound

  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hx
  specialize hbound n
  simp at hbound

  grind


end Chapter6

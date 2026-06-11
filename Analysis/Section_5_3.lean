import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero. -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a {name}`CauchySequence`. -/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by

  rw [Sequence.equiv_def] at hab hbc ⊢
  intro ε hε
  specialize hab (ε/2) (by positivity)
  specialize hbc (ε/2) (by positivity)
  rw [Rat.eventuallyClose_iff] at hab hbc ⊢
  obtain ⟨n1, hn1⟩ := hab
  obtain ⟨n2, hn2⟩ := hbc
  let M := max n1 n2
  use M
  intros n hn
  specialize hn1 n (by grind)
  specialize hn2 n (by grind)
  grind

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
    refl := by
      intro a; rw [Sequence.equiv_def]
      intro ε hε; rw [Rat.eventuallyClose_iff]
      use 0; simp; grind
    symm := by
      intros a b hab; rw [Sequence.equiv_def] at hab ⊢
      intro ε hε; specialize hab ε hε
      rw [Rat.eventuallyClose_iff] at hab ⊢
      obtain ⟨n, hn⟩ := hab
      use n; grind
    trans := Sequence.equiv_trans
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy. -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy]
  intro ε hε
  rw [Rat.EventuallySteady]
  use 0; simp; rw [Rat.steady_def]
  intros n hn m hm
  rw [Rat.Close]; simp;

  set s := Sequence.ofNatFun (fun x ↦ a)
  have: (s.from 0).n₀ = 0 := by grind [Sequence.ofNatFun]
  rw [this] at hn hm
  simp [hn, hm]
  positivity

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of {lean}`0` to {lean}`LIM a` when {lean}`a` is not Cauchy.
  This requires classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind


/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by

  -- cachy is bounded
  choose Ma hmaz hma using Sequence.isBounded_of_isCauchy ha
  choose Mb hmbz hmb using Sequence.isBounded_of_isCauchy hb

  rw [Sequence.boundedBy_def] at hma hmb

  rw [coe] at *
  intro ε hε

  set M:= max (max Ma Mb) 1

  specialize ha (ε / (2 * M)) (by positivity)
  specialize hb (ε / (2 * M)) (by positivity)

  choose N1 ha using ha
  choose N2 hb using hb

  use max N1 N2
  intro j hj k hk

  specialize ha j (by grind) k (by grind)
  specialize hb j (by grind) k (by grind)

  simp [Section_4_3.dist] at *

  have ha1: |a j - a k| * |b j| ≤ (ε / (2 * M)) * |b j| := by grind [mul_le_mul_of_nonneg]
  have hb1: |b j - b k| * |a k| ≤ (ε / (2 * M)) * |a k| := by grind [mul_le_mul_of_nonneg]

  rw [←abs_mul] at ha1 hb1

  have hbj := hmb j; simp at hbj
  have hak := hma k; simp at hak

  calc |a j * b j - a k * b k| ≤ (ε / (2 * M)) * (|b j| + |a k|) := by grind
    _ ≤ (ε / (2 * M)) * (M + M) := by grind [mul_le_mul_of_nonneg]
    _ = ε := by grind

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by

  choose Mb hmbz hmb using Sequence.isBounded_of_isCauchy hb
  rw [Sequence.boundedBy_def] at hmb

  set M:= max Mb 1

  rw [equiv_def] at *
  intro ε hε
  specialize haa' (ε/M) (by positivity)
  rw [Rat.eventuallyClose_def] at *

  choose n1 hn using haa'
  set m := max n1 0
  use m

  rw [Rat.closeSeq_def] at *; simp_all

  intro i hi hi2

  specialize hn i (by positivity) (by grind)

  have hbi := hmb i; simp at hbi

  lift i to ℕ using hi

  rw [Rat.Close] at *; simp_all

  calc |a i * b i - a' i * b i| = |(a i - a' i) * b i| := by grind
    _ = |a i - a' i| * |b i| := by grind
    _ ≤ (ε/M) * M := by grind [mul_le_mul_of_nonneg]
    _ = ε := by grind

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  rw [ratCast_def, ratCast_def]
  constructor
  . intro h
    have hq := Sequence.IsCauchy.const q
    have hr := Sequence.IsCauchy.const r
    rw [LIM_eq_LIM hq hr, Sequence.equiv_iff] at h
    by_contra hne
    push_neg at hne
    have: |q - r| > 0 := by grind
    specialize h (|q - r| / 2) (by positivity)
    choose n hn using h
    specialize hn n (by grind)
    grind
  . intro h
    have hq := Sequence.IsCauchy.const q
    have hr := Sequence.IsCauchy.const r
    rw [LIM_eq_LIM hq hr, Sequence.equiv_iff]
    intro ε hε
    simp [h]
    use 0
    grind

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

theorem Real.LIM.one : LIM (fun _ ↦ (1:ℚ)) = 1 := by rw [←ratCast_def 1]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  have ha := Sequence.IsCauchy.const a
  have hb := Sequence.IsCauchy.const b
  have hab1 := Sequence.IsCauchy.const (a+b)
  have hab2:= Sequence.IsCauchy.add ha hb

  rw [ratCast_def, ratCast_def, LIM_add ha hb, ratCast_def, LIM_eq_LIM hab2 hab1]
  simp [Sequence.equiv_iff]
  intro ε hε
  use 0
  grind

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  have ha := Sequence.IsCauchy.const a
  have hb := Sequence.IsCauchy.const b
  have hab1 := Sequence.IsCauchy.const (a*b)
  have hab2:= Sequence.IsCauchy.mul ha hb

  simp [ratCast_def]
  rw [LIM_mul ha hb, LIM_eq_LIM hab2 hab1]
  simp [Sequence.equiv_iff]
  intro ε hε
  use 0; simp; grind

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- {name (full := RatCast.ratCast)}`ratCast` commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by

  calc -(a:Real) = ((-1:ℚ):Real) * (a:Real) := by rfl
    _ = (((-1) * a):ℚ)  := by rw [ratCast_mul]
    _ = (-a:ℚ) := by rw [show (-1:ℚ) * a = -a by grind]

/-- {name}`LIM` distributes over negation -/

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by

    rw [Sequence.isCauchy_def] at ha ⊢
    intro ε hε
    specialize ha ε hε
    rw [Rat.EventuallySteady] at ha ⊢
    obtain ⟨N, ⟨hn, ha1⟩⟩ := ha
    use N; simp
    rw [Rat.Steady] at ha1 ⊢
    simp_all
    intro m hm n hn
    specialize ha1 m hm n hn
    rw [Rat.Close] at ha1 ⊢
    grind

/-- It may be possible to omit the {name (full := Sequence.IsCauchy)}`IsCauchy` hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by

  have: -LIM a = ((-1:ℚ):Real) * LIM a := by rfl
  rw [this, ratCast_def, LIM_mul (Sequence.IsCauchy.const (-1)) ha]

  have h1 := Sequence.IsCauchy.mul (Sequence.IsCauchy.const (-1)) ha

  have h2 := Sequence.IsCauchy.neg a ha

  rw [LIM_eq_LIM h1 h2, Sequence.equiv_iff]
  intro ε hε
  use 0; simp;
  positivity

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms
  (by
    intro a b c
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    obtain ⟨sc, ⟨hc1, hc2⟩⟩ := Real.eq_lim c

    have hab := Sequence.IsCauchy.add ha1 hb1
    have hbc := Sequence.IsCauchy.add hb1 hc1

    have hab_c := Sequence.IsCauchy.add hab hc1
    have ha_bc := Sequence.IsCauchy.add ha1 hbc

    rw [ha2, hb2, hc2, LIM_add ha1 hb1, LIM_add hab hc1, LIM_add hb1 hc1, LIM_add ha1 hbc]

    rw [LIM_eq_LIM hab_c ha_bc, Sequence.equiv_iff]
    intro ε hε
    use 0; intro n;
    simp; grind
  )
  (by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    rw [ha2, ← Real.LIM.zero]
    rw [LIM_add (Sequence.IsCauchy.const 0) ha1]
    have hsum := Sequence.IsCauchy.add (Sequence.IsCauchy.const 0) ha1
    rw [LIM_eq_LIM hsum ha1, Sequence.equiv_iff]
    intro ε hε
    use 0; intro n
    simp; grind
  )
  (by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    rw [ha2, Real.neg_LIM sa ha1]
    have hneg := Sequence.IsCauchy.neg sa ha1

    rw [LIM_add hneg ha1, ←Real.LIM.zero]
    rw [LIM_eq_LIM (Sequence.IsCauchy.add hneg ha1) (Sequence.IsCauchy.const 0)]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n
    simp; grind
  )

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by

  rw [coe] at *
  simp [Section_4_3.dist] at *

  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega

  grind

/-- {name}`LIM` distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by

  rw [sub_eq_add_neg]

  have h1: LIM a + -LIM b + LIM b = LIM (a - b) + LIM b := by
    rw [Real.LIM_add (Sequence.IsCauchy.sub ha hb) hb]; simp

  apply add_right_cancel h1

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by

  rw [sub_eq_add_neg, neg_ratCast, ratCast_add]; grind

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    rw [ha2, hb2, LIM_add ha1 hb1, LIM_add hb1 ha1]
    rw [LIM_eq_LIM (Sequence.IsCauchy.add ha1 hb1) (Sequence.IsCauchy.add hb1 ha1)]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro a b
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    rw [ha2, hb2, LIM_mul ha1 hb1, LIM_mul hb1 ha1]
    rw [LIM_eq_LIM (Sequence.IsCauchy.mul ha1 hb1) (Sequence.IsCauchy.mul hb1 ha1)]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind
  mul_assoc := by
    intro a b c
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    obtain ⟨sc, ⟨hc1, hc2⟩⟩ := Real.eq_lim c

    have hab := Sequence.IsCauchy.mul ha1 hb1
    have hbc := Sequence.IsCauchy.mul hb1 hc1

    have hab_c := Sequence.IsCauchy.mul hab hc1
    have ha_bc := Sequence.IsCauchy.mul ha1 hbc

    rw [ha2, hb2, hc2, LIM_mul ha1 hb1, LIM_mul hab hc1, LIM_mul hb1 hc1, LIM_mul ha1 hbc]

    rw [LIM_eq_LIM hab_c ha_bc, Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  one_mul := by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    rw [ha2, ←LIM.one, LIM_mul (Sequence.IsCauchy.const 1) ha1]
    rw [LIM_eq_LIM (Sequence.IsCauchy.mul (Sequence.IsCauchy.const 1) ha1) ha1]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  mul_one := by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    rw [ha2, ←LIM.one, LIM_mul ha1 (Sequence.IsCauchy.const 1)]
    rw [LIM_eq_LIM (Sequence.IsCauchy.mul ha1 (Sequence.IsCauchy.const 1)) ha1]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := fun a b c => by
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    obtain ⟨sc, ⟨hc1, hc2⟩⟩ := Real.eq_lim c

    have h_add_bc := Sequence.IsCauchy.add hb1 hc1
    have h_mul_ab := Sequence.IsCauchy.mul ha1 hb1
    have h_mul_ac := Sequence.IsCauchy.mul ha1 hc1

    rw [ha2, hb2, hc2, LIM_mul ha1 hb1, LIM_add hb1 hc1, LIM_mul ha1 hc1]
    rw [LIM_mul ha1 h_add_bc]
    rw [LIM_add h_mul_ab h_mul_ac]

    rw [LIM_eq_LIM (Sequence.IsCauchy.mul ha1 h_add_bc) (Sequence.IsCauchy.add h_mul_ab h_mul_ac)]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  right_distrib := fun a b c => by
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    obtain ⟨sc, ⟨hc1, hc2⟩⟩ := Real.eq_lim c

    have h_add_ab := Sequence.IsCauchy.add ha1 hb1
    have h_mul_bc := Sequence.IsCauchy.mul hb1 hc1
    have h_mul_ac := Sequence.IsCauchy.mul ha1 hc1

    rw [ha2, hb2, hc2, LIM_add ha1 hb1, LIM_mul h_add_ab hc1]
    rw [LIM_mul ha1 hc1, LIM_mul hb1 hc1, LIM_add h_mul_ac h_mul_bc]

    rw [LIM_eq_LIM (Sequence.IsCauchy.mul h_add_ab hc1) (Sequence.IsCauchy.add h_mul_ac h_mul_bc)]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  zero_mul := by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    have h0 := Sequence.IsCauchy.const 0
    rw [ha2, ←LIM.zero, LIM_mul h0 ha1]
    rw [LIM_eq_LIM (Sequence.IsCauchy.mul h0 ha1) h0]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  mul_zero := by
    intro a
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    have h0 := Sequence.IsCauchy.const 0
    rw [ha2, ←LIM.zero, LIM_mul ha1 h0]
    rw [LIM_eq_LIM (Sequence.IsCauchy.mul ha1 h0) h0]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  mul_assoc := by
    intro a b c
    obtain ⟨sa, ⟨ha1, ha2⟩⟩ := Real.eq_lim a
    obtain ⟨sb, ⟨hb1, hb2⟩⟩ := Real.eq_lim b
    obtain ⟨sc, ⟨hc1, hc2⟩⟩ := Real.eq_lim c

    have hab := Sequence.IsCauchy.mul ha1 hb1
    have hbc := Sequence.IsCauchy.mul hb1 hc1

    have hab_c := Sequence.IsCauchy.mul hab hc1
    have ha_bc := Sequence.IsCauchy.mul ha1 hbc

    rw [ha2, hb2, hc2, LIM_mul ha1 hb1, LIM_mul hab hc1, LIM_mul hb1 hc1, LIM_mul ha1 hbc]

    rw [LIM_eq_LIM hab_c ha_bc, Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  natCast_succ := by
    intro n
    dsimp only [NatCast.natCast]
    rw [ratCast_def n, ratCast_def (n+1:ℕ), ←LIM.one]

    rw [LIM_add (Sequence.IsCauchy.const n) (Sequence.IsCauchy.const 1)]
    rw [LIM_eq_LIM (Sequence.IsCauchy.const (n+1:ℕ)) (Sequence.IsCauchy.add (Sequence.IsCauchy.const n) (Sequence.IsCauchy.const 1))]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0; intro n hn
    simp; grind

  intCast_negSucc := by
    intro n
    change ((Int.negSucc n : ℚ) : Real) = -(((n.succ : ℤ) : ℚ) : Real)
    rw [Real.neg_ratCast]  -- pushing the negation inside the rational cast: -(↑a : Real) = (↑(-a) : Real)
    simp  -- with ℚ's Ring lemmas (Int.negSucc n : ℚ) = -(n.succ : ℚ)

-- ring homomorphism from ℚ to Real
abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by simp [RatCast.ratCast, ←LIM_def]
  map_one' := by simp [RatCast.ratCast, ←LIM_def, LIM.one]
  map_add' := by
    intro a b
    simp [RatCast.ratCast, ←LIM_def, ←ratCast_def, ratCast_add]
  map_mul' := by
    intro a b
    simp [RatCast.ratCast, ←LIM_def, ←ratCast_def, ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

private lemma pow10_gt_n : ∀ (n:ℕ), 10^(n+1) > (n+1) := by
    intro n
    induction' n with n ih
    . simp
    . grind

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  by_contra h
  rw [bounded_away_zero_def] at h
  obtain ⟨c, hc, hn⟩ := h
  simp at hn

  choose n1 hn1 using exists_int_gt (2 / c)
  let n2 := n1.toNat
  have h1 := pow10_gt_n n2

  have h2: n2 + 1 > n1 := by grind
  qify at h1 h2
  have h3: 2 / c < 10 ^ (n2 + 1) := by linarith

  specialize hn n2
  have h4 : c/2 < 10 ^ (-(n2:ℤ) - 1) := by linarith  -- c > c / 2

  have h5 := mul_lt_mul_of_pos h3 h4 (by positivity) (by positivity)

  field_simp at h5
  rw [←zpow_natCast, ←zpow_add' (by grind)] at h5
  grind

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  by_contra h
  rw [bounded_away_zero_def] at h
  obtain ⟨c, hc, hn⟩ := h
  have h1:= hn 0
  simp at h1
  grind

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  by_contra h
  rw [Sequence.IsBounded] at h
  obtain ⟨M, hm, hn⟩ := h
  rw [Sequence.boundedBy_def] at hn
  simp at hn

  choose n1 hn1 using exists_int_gt M

  have h1 := pow10_gt_n n1.toNat
  have h2 : n1.toNat + 1 > n1 := by grind
  qify at h1 h2
  have: 10 ^ (n1.toNat + 1) > M := by linarith

  have h3 := hn n1
  have hgz : (n1:ℚ) ≥ 0 := by linarith
  norm_cast at hgz
  simp [hgz] at h3
  grind

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj
    have h1 := hb' j (by linarith) n₀ (by linarith)
    rw [Section_4_3.dist_eq] at h1
    grind
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro ε hε
    use n₀; intro m hm; grind
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by

  by_contra h
  rw [←LIM.zero, LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const 0)] at h
  rw [Sequence.equiv_iff] at h
  simp at h
  rw [BoundedAwayZero] at ha
  choose c hc ha using ha
  have h1 := h (c/2) (half_pos hc)
  choose N hn1 using h1
  have := hn1 N (by linarith)
  have := ha N
  grind

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by
        congr; simp only [Pi.inv_apply]; field_simp [ha' m, ha' n]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [Inv.inv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by

  have ⟨ a, ha, hbound, hlim ⟩ := (boundedAwayZero_of_nonzero hx)
  rw [hlim]

  have hinv := (Real.inv_isCauchy_of_boundedAwayZero hbound ha)
  have hmul:= Sequence.IsCauchy.mul ha hinv

  rw [inv_def hbound ha, ←LIM.one, LIM_mul ha hinv]
  rw [LIM_eq_LIM hmul (Sequence.IsCauchy.const 1)]
  rw [Sequence.equiv_iff]
  intro ε hε; use 0;
  intro m hm; simp; grind

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]
  exact self_mul_inv hx

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

theorem Real.inv_natCast (q:ℕ) : (q:Real)⁻¹ = (q:ℚ)⁻¹ := by
  have h:= inv_ratCast (q:ℚ)
  norm_cast at h

theorem Real.inv_intCast (q:ℤ) : (q:Real)⁻¹ = (q:ℚ)⁻¹ := by
  have h:= inv_ratCast (q:ℚ)
  norm_cast at h

/-- Default definition of division. -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    -- ratCast_def, ratCast_inj
    use (0:ℚ), (1:ℚ); norm_num
  mul_inv_cancel := by grind [inv_mul_self]
  inv_zero := by grind [inv_zero]
  ratCast_def := by
    intro q
    rw [div_eq, inv_natCast]

    have: (q.num:Real) = ((q.num:ℚ):Real) := rfl
    rw [this, Real.ratCast_mul, Real.ratCast_inj]
    grind [Rat.num_div_den]

  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by grind

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  by_contra h
  specialize h 1 2 0
  grind

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by

  rw [Sequence.equiv_def] at hab
  specialize hab 1 (by norm_num)
  have := Sequence.isBounded_of_eventuallyClose hab
  grind

/--
  Same as {name}`Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [←LIM.zero, LIM_eq_LIM Sequence.IsCauchy.harmonic' (Sequence.IsCauchy.const 0)]
  rw [Sequence.equiv_iff]
  intro ε hε
  simp
  set M := ⌈1 / ε⌉.toNat
  use M
  have: M ≥ ⌈1 / ε⌉ := by grind
  qify at this

  have: M ≥ 1 / ε := by grind [Int.le_ceil]
  field_simp at this

  intro n hn
  field_simp

  qify at hn

  calc |(n:ℚ) + 1| * ε = n * ε + ε := by grind
    _ ≥ n * ε := by grind
    _ ≥ M * ε := by grind [mul_le_mul_iff_of_pos_right]
    _ ≥ 1 := by grind

end Chapter5

import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of {lean}`ℕ` and {lean}`ℤ`.

- Equivalence with the Mathlib rationals {name}`_root_.Rat` (or {lean}`ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers {lean}`ℕ` and integers {lean}`ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by intro a; rfl
    symm := by intro a b h; exact h.symm
    trans := by
      intro a b c h1 h2
      have hb := b.nonzero
      apply mul_right_cancel₀ hb
      calc
        a.numerator * c.denominator * b.denominator = (a.numerator * b.denominator) * c.denominator := by ring
        _ = (b.numerator * a.denominator) * c.denominator := by rw [h1]
        _ = a.denominator * (b.numerator * c.denominator) := by ring
        _ = a.denominator * (c.numerator * b.denominator) := by rw [h2]
        _ = c.numerator * a.denominator * b.denominator := by ring
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv, hb, hd, Quotient.eq, PreRat.instSetoid]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

theorem Rat.one_not_zero : (1 : ℤ) ≠ 0 := by norm_num

/--
  Decidability of equality. Hint: modify the proof of {lean}`DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the {name}`Quotient` API.

-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b

  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ na, da, ha ⟩ ⟨ nb, db, hb ⟩
    rw [Quotient.eq]
    dsimp [Setoid.r, PreRat.instSetoid]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    linear_combination d * d' * h3 + b * b' * h4
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    grind
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ a', b', h1' ⟩ h
    simp [formalDiv, h1, h1']
    rw [Quotient.eq]
    simpa [neg_mul] using congrArg (-·) h
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

#check ((-1:ℤ):Rat)
-- #check (1:Rat)

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

#check (1:Rat)

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

theorem Rat.num_zero_eq_zero(a:ℤ) : 0 // a = 0 := by
  by_cases ha: a ≠ 0
  . rw [of_Nat_eq, eq _ _ ha one_not_zero]; grind
  . simp at ha
    rw [of_Nat_eq, formalDiv, Quotient.eq]
    simp [ha]

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  rw [coe_Nat_eq, coe_Nat_eq, of_Nat_eq, add_eq _ _ one_not_zero one_not_zero]
  simp

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq _ _ one_not_zero one_not_zero]
  simp

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq _ _ one_not_zero one_not_zero]
  simp

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b h
  simp at h
  rw [coe_Int_eq, coe_Int_eq, eq _ _ one_not_zero one_not_zero] at h
  simp at h
  exact h

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, h1 ⟩ ⟨ a', b', h1' ⟩ h
    simp_all

    by_cases ha : a = 0
    · have ha' : a' = 0 := by
        rw [ha, zero_mul] at h
        simp [h1] at h
        exact h
      simp [formalDiv, ha, ha']
    · push_neg at ha
      have ha' : a' ≠ 0 := by
        by_contra hzero
        rw [hzero, zero_mul] at h
        have hnz := mul_ne_zero ha h1'
        contradiction
      rw [eq _ _ ha ha']
      grind
  )

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    rw [of_Nat_eq, add_eq _ _ one_not_zero hb]
    simp)
 (by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    rw [neg_eq _ hb, add_eq _ _ hb hb, mul_comm b a, of_Nat_eq]
    simp
    have h2 := mul_ne_zero hb hb
    rw [eq _ _ h2 one_not_zero]
    simp
  )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    rw [add_eq _ _ hb hd, add_eq _ _ hd hb]
    rw [eq _ _ (Int.mul_ne_zero hb hd) (Int.mul_ne_zero hd hb)]
    ring

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    rw [mul_eq a c hb hd, mul_eq c a hd hb]
    rw [eq _ _ (Int.mul_ne_zero hb hd) (Int.mul_ne_zero hd hb)]
    ring
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [mul_eq a c hb hd, mul_eq (a*c) e (Int.mul_ne_zero hb hd) hf,
      mul_eq c e hd hf, mul_eq a (c*e) hb (Int.mul_ne_zero hd hf)]
    grind
  one_mul := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ one_not_zero hb]
    simp
  mul_one := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ hb one_not_zero]
    simp

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [add_eq c e hd hf, mul_eq a (c*f + d*e) hb (Int.mul_ne_zero hd hf),
      mul_eq a c hb hd, mul_eq a e hb hf,
      add_eq (a*c) (a*e) (Int.mul_ne_zero hb hd) (Int.mul_ne_zero hb hf)]
    rw [eq _ _ (Int.mul_ne_zero hb (Int.mul_ne_zero hd hf))
      (Int.mul_ne_zero (Int.mul_ne_zero hb hd) (Int.mul_ne_zero hb hf))]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [add_eq a c hb hd, mul_eq (a*d + b*c) e (Int.mul_ne_zero hb hd) hf,
      mul_eq a e hb hf, mul_eq c e hd hf,
      add_eq (a*e) (c*e) (Int.mul_ne_zero hb hf) (Int.mul_ne_zero hd hf)]
    rw [eq _ _ (Int.mul_ne_zero (Int.mul_ne_zero hb hd) hf)
      (Int.mul_ne_zero (Int.mul_ne_zero hb hf) (Int.mul_ne_zero hd hf))]
    ring
  zero_mul := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    calc
      (0 : Rat) * (a // b) = (0 // 1) * (a // b) := rfl
      _ = (0 * a) // (1 * b) := mul_eq (0 : ℤ) a (by norm_num) hb
      _ = 0 // (1 * b) := by grind
      _ = (0 : Rat) := by
        apply (eq (0 : ℤ) 0 (Int.mul_ne_zero (by norm_num) hb) (by norm_num)).mpr
        ring
  mul_zero := by
    intro x
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ hb one_not_zero]
    simp
    rw [eq _ _ hb one_not_zero]
    simp
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [mul_eq a c hb hd, mul_eq (a*c) e (Int.mul_ne_zero hb hd) hf,
      mul_eq c e hd hf, mul_eq a (c*e) hb (Int.mul_ne_zero hd hf)]
    grind
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem ratCast_eq (q : ℚ) : (q : Rat) = q.num // q.den := rfl

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro a b h
  simp at h
  have h1 : (a.den:ℤ) ≠ 0 := by exact_mod_cast a.den_nz
  have h2 : (b.den:ℤ) ≠ 0 := by exact_mod_cast b.den_nz

  rw [ratCast_eq, ratCast_eq, eq _ _ h1 h2] at h
  rw [←Rat.divInt_eq_divInt_iff h1 h2] at h
  simp at h
  exact h

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    have this := coe_Int_inj h
    norm_num at this
  mul_inv_cancel := by
    intro x hx
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    have ha : a ≠ 0 := by
      by_contra ha0
      rw [ha0] at hx
      have := num_zero_eq_zero b
      contradiction
    rw [inv_eq a hb, mul_eq a b hb ha, of_Nat_eq]
    rw [eq _ _ (mul_ne_zero hb ha) one_not_zero]
    grind
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq, Rat.inv_eq _ (by norm_num), Rat.mul_eq _ _ (by norm_num) (by norm_num)]
  simp
  rw [Rat.eq _ _ (by norm_num) (by norm_num)]
  norm_num

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := (intCast_add a b).symm
  map_mul' a b := (intCast_mul a b).symm

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

lemma formalDiv_eq_field_div (a b : ℤ) (hb : b ≠ 0) : a // b = (a : Rat) / (b : Rat) := by
  have h1 : (1 : ℤ) ≠ 0 := by norm_num
  calc
    a // b = (a * 1) // (1 * b) := by grind
    _ = (a // 1) * (1 // b) := (Rat.mul_eq a (1 : ℤ) h1 hb).symm
    _ = (a // 1) * ((b // 1)⁻¹) := by rw [Rat.inv_eq b h1]
    _ = (a : Rat) * ((b : Rat)⁻¹) := rfl
    _ = (a : Rat) / (b : Rat) := rfl

lemma formalDiv_eq_neg_neg (a b : ℤ) (hb : b ≠ 0) : a // b = (-a) // (-b) := by
  apply (Rat.eq a (-a) hb (neg_ne_zero.mpr hb)).mpr
  ring

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨a, b, hb, rfl⟩ := eq_diff x
  by_cases ha0 : a = 0
  · left
    rw [ha0]
    apply (Rat.eq (0 : ℤ) 0 (b := b) (d := 1) hb (by norm_num)).mpr
    ring
  · by_cases ha : a > 0
    · by_cases hbpos : b > 0
      · right; left
        refine ⟨a, b, ha, hbpos, formalDiv_eq_field_div a b hb⟩
      · have hbneg : b < 0 := by
          have hble0 : b ≤ 0 := by linarith
          exact lt_of_le_of_ne hble0 hb
        have hnbpos : -b > 0 := by linarith
        have h_r_pos : (a // (-b)).isPos :=
          ⟨a, -b, ha, hnbpos, formalDiv_eq_field_div a (-b) (neg_ne_zero.mpr hb)⟩
        have h_eq : a // b = -(a // (-b)) := by
          calc
            a // b = (-a) // (-b) := formalDiv_eq_neg_neg a b hb
            _ = -(a // (-b)) := by rw [Rat.neg_eq a (neg_ne_zero.mpr hb)]
        right; right
        exact ⟨a // (-b), h_r_pos, h_eq⟩
    · have haneg : a < 0 := by
        have hale0 : a ≤ 0 := by linarith
        exact lt_of_le_of_ne hale0 ha0
      by_cases hbpos : b > 0
      · have ha_neg' : -a > 0 := by linarith
        have h_r_pos : ((-a) // b).isPos :=
          ⟨-a, b, ha_neg', hbpos, formalDiv_eq_field_div (-a) b hb⟩
        have h_eq : a // b = -((-a) // b) := by
          calc
            a // b = (-(-a)) // b := by ring
            _ = -((-a) // b) := by rw [Rat.neg_eq (-a) hb]
        right; right
        exact ⟨(-a) // b, h_r_pos, h_eq⟩
      · have hbneg : b < 0 := by
          have hble0 : b ≤ 0 := by linarith
          exact lt_of_le_of_ne hble0 hb
        have hnbpos : -b > 0 := by linarith
        have ha_neg' : -a > 0 := by linarith
        right; left
        have h_div : a // b = (-a : Rat) / (-b : Rat) :=
          calc
            a // b = (-a) // (-b) := formalDiv_eq_neg_neg a b hb
            _ = (-a : Rat) / (-b : Rat) := formalDiv_eq_field_div (-a) (-b) (neg_ne_zero.mpr hb)
        exact ⟨-a, -b, ha_neg', hnbpos, h_div⟩

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  rintro ⟨hzero, hpos⟩
  rcases hpos with ⟨a, b, ha, hb, hq⟩
  rw [hzero] at hq
  have hb' : b ≠ 0 := by linarith
  have h_div : a // b = (a : Rat) / (b : Rat) := formalDiv_eq_field_div a b hb'
  have h_eq_zero : (0 : Rat) = a // b := by
    simpa [← h_div] using hq
  have hzero_int : (0 : ℤ) = a := by
    have h_eq' := (Rat.eq (0 : ℤ) a (by norm_num) hb').mp h_eq_zero
    simpa using h_eq'
  linarith

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  rintro ⟨hzero, hneg⟩
  rcases hneg with ⟨r, hrpos, hq⟩
  rw [hzero] at hq
  have hr_zero : r = 0 := neg_eq_zero.mp hq.symm
  exact not_zero_and_pos r ⟨hr_zero, hrpos⟩

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  rintro ⟨hpos, hneg⟩
  rcases hpos with ⟨a, b, ha, hb, hq⟩
  rcases hneg with ⟨r, hrpos, hq'⟩
  rcases hrpos with ⟨c, d, hc, hd, hr_eq⟩
  have hb' : b ≠ 0 := by linarith
  have hd' : d ≠ 0 := by linarith
  -- hq: x = a/b, hq': x = -r, hr_eq: r = c/d
  -- So a/b = -(c/d), i.e., a // b = -(c // d)
  have h_eq1 : a // b = (a : Rat) / (b : Rat) := formalDiv_eq_field_div a b hb'
  have h_eq2 : c // d = (c : Rat) / (d : Rat) := formalDiv_eq_field_div c d hd'
  rw [hq, hr_eq] at hq'
  rw [← h_eq1, ← h_eq2] at hq'
  have h_neg : a // b = -(c // d) := hq'
  rw [Rat.neg_eq c hd'] at h_neg
  -- h_neg: a // b = (-c) // d
  have h_cross := (Rat.eq a (-c) hb' hd').mp h_neg
  -- h_cross: a * d = (-c) * b
  -- LHS > 0 (a>0, d>0), RHS < 0 (-c<0, b>0)
  have hpos_prod : a * d > 0 := mul_pos ha hd
  have hneg_prod : (-c) * b < 0 := by
    have : -c < 0 := by linarith
    exact mul_neg_of_neg_of_pos this hb
  linarith

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.isNeg_neg_iff_isPos (q : Rat) : (-q).isNeg ↔ q.isPos := by
  constructor
  · rintro ⟨r, hr, hq⟩
    have hqr : q = r := neg_inj.mp hq
    rw [hqr]
    exact hr
  · intro hq
    exact ⟨q, hq, rfl⟩

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  have h : y - x = -(x - y) := by ring
  calc
    x > y ↔ (y - x).isNeg := by rfl
    _ ↔ (-(x - y)).isNeg := by rw [h]
    _ ↔ (x - y).isPos := isNeg_neg_iff_isPos (x - y)

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp [GE.ge, LE.le, eq_comm]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rcases trichotomous (x - y) with (h | h | h)
  · right; right; exact sub_eq_zero.mp h
  · left; rw [gt_iff]; exact h
  · right; left; rw [lt_iff]; exact h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rintro ⟨hgt, hlt⟩
  have hpos : (x - y).isPos := (gt_iff x y).mp hgt
  have hneg : (x - y).isNeg := hlt
  exact not_pos_and_neg (x - y) ⟨hpos, hneg⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rintro ⟨hgt, heq⟩
  have hpos : (x - y).isPos := (gt_iff x y).mp hgt
  rw [heq, sub_self] at hpos
  exact (not_zero_and_pos 0) ⟨rfl, hpos⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rintro ⟨hlt, heq⟩
  have hneg : (x - y).isNeg := hlt
  rw [heq, sub_self] at hneg
  exact (not_zero_and_neg 0) ⟨rfl, hneg⟩

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by rfl

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
lemma isPos_add {r s : Rat} (hr : r.isPos) (hs : s.isPos) : (r + s).isPos := by
  rcases hr with ⟨a, b, ha, hb, hr_eq⟩
  rcases hs with ⟨c, d, hc, hd, hs_eq⟩
  rw [hr_eq, hs_eq]
  have hb0 : b ≠ 0 := by linarith
  have hd0 : d ≠ 0 := by linarith
  have hbd0 : b * d ≠ 0 := mul_ne_zero hb0 hd0
  have hsum : a // b + c // d = ((a * d + b * c : ℤ) : Rat) / ((b * d : ℤ) : Rat) :=
    calc
      a // b + c // d = (a * d + b * c) // (b * d) := Rat.add_eq a c (b := b) (d := d) hb0 hd0
      _ = ((a * d + b * c : ℤ) : Rat) / ((b * d : ℤ) : Rat) :=
        formalDiv_eq_field_div (a * d + b * c) (b * d) hbd0
  rw [← formalDiv_eq_field_div a b hb0, ← formalDiv_eq_field_div c d hd0]
  rw [hsum]
  have hnum : a * d + b * c > 0 := by
    have h1 : a * d > 0 := mul_pos ha (by exact_mod_cast hd)
    have h2 : b * c > 0 := mul_pos (by exact_mod_cast hb) hc
    exact add_pos h1 h2
  have hden : b * d > 0 := mul_pos (by exact_mod_cast hb) (by exact_mod_cast hd)
  refine ⟨a * d + b * c, b * d, hnum, hden, ?_⟩
  rfl

lemma isPos_mul {r s : Rat} (hr : r.isPos) (hs : s.isPos) : (r * s).isPos := by
  rcases hr with ⟨a, b, ha, hb, hr_eq⟩
  rcases hs with ⟨c, d, hc, hd, hs_eq⟩
  rw [hr_eq, hs_eq]
  have hb0 : b ≠ 0 := by linarith
  have hd0 : d ≠ 0 := by linarith
  have hbd0 : b * d ≠ 0 := mul_ne_zero hb0 hd0
  have hprod : a // b * (c // d) = ((a * c : ℤ) : Rat) / ((b * d : ℤ) : Rat) :=
    calc
      a // b * (c // d) = (a * c) // (b * d) := Rat.mul_eq a c (b := b) (d := d) hb0 hd0
      _ = ((a * c : ℤ) : Rat) / ((b * d : ℤ) : Rat) :=
        formalDiv_eq_field_div (a * c) (b * d) hbd0
  rw [← formalDiv_eq_field_div a b hb0, ← formalDiv_eq_field_div c d hd0]
  rw [hprod]
  refine ⟨a * c, b * d, mul_pos ha hc, mul_pos (by exact_mod_cast hb) (by exact_mod_cast hd), ?_⟩
  rfl

lemma isNeg_iff (q : Rat) : q.isNeg ↔ ∃ r : Rat, r.isPos ∧ q = -r := by rfl

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  rcases hxy with ⟨r, hrpos, hxy_eq⟩
  rcases hyz with ⟨s, hspos, hyz_eq⟩
  -- hxy_eq: x-y = -r, hyz_eq: y-z = -s
  -- x-z = (x-y)+(y-z) = -r + (-s) = -(r+s)
  have hxz_eq : x - z = -(r + s) := by
    calc
      x - z = (x - y) + (y - z) := by ring
      _ = (-r) + (-s) := by rw [hxy_eq, hyz_eq]
      _ = -(r + s) := by ring
  have h_pos : (r + s).isPos := isPos_add hrpos hspos
  -- x < z ↔ (x-z).isNeg ↔ ∃ t, t.isPos ∧ (x-z) = -t
  -- Take t := r+s
  exact ⟨r + s, h_pos, hxz_eq⟩

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  have : (x + z) - (y + z) = x - y := by ring
  rw [lt_iff, this]; rw [lt_iff] at hxy; exact hxy

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rcases hxy with ⟨r, hrpos, hxy_eq⟩
  -- hxy_eq: x - y = -r
  have h_diff : x * z - y * z = -(r * z) := by
    calc
      x * z - y * z = (x - y) * z := by ring
      _ = (-r) * z := by rw [hxy_eq]
      _ = -(r * z) := by ring
  have h_pos : (r * z).isPos := isPos_mul hrpos hz
  exact ⟨r * z, h_pos, h_diff⟩

lemma zero_lt_iff_isPos (c : Rat) : 0 < c ↔ c.isPos := by
  constructor
  · intro h
    rcases h with ⟨r, hr, h_eq⟩
    have h_neg : -c = -r := by
      calc
        -c = 0 - c := by ring
        _ = -r := h_eq
    have hc_eq_r : c = r := neg_inj.mp h_neg
    rw [hc_eq_r]
    exact hr
  · intro hpos
    exact ⟨c, hpos, by ring⟩

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m

  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            -- apply isTrue

            -- have h1: b * d > 0 := by grind [mul_ne_zero]
            -- have h2: (1:ℚ) > 0 := by grind
            -- have h3: (1:ℚ) / (b*d) > 0 := by apply div_pos h2 (by exact_mod_cast h1)

            -- qify at h

            -- have h4: a * d * (1:ℚ) / (b*d) ≤ b * c * (1:ℚ) / (b*d) := by grind [Rat.mul_le_mul_of_nonneg_right]
            -- simp at h4
            -- rw [mul_div_mul_right, mul_div_mul_left] at h4
            -- norm_cast at h4
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with (hlt | heq)
    · rcases hyz with (hlt' | heq')
      · exact Or.inl (lt_trans hlt hlt')
      · subst heq'; exact Or.inl hlt
    · rcases hyz with (hlt' | heq')
      · subst heq; exact Or.inl hlt'
      · subst heq; subst heq'; exact Or.inr rfl
  lt_iff_le_not_ge x y := by
    constructor
    · intro hlt
      have hle : x ≤ y := Or.inl hlt
      have hnge : ¬ y ≤ x := by
        intro hge
        rcases hge with (hgt | heq)
        · exact not_gt_and_lt x y ⟨hgt, hlt⟩
        · exact not_lt_and_eq x y ⟨hlt, heq.symm⟩
      exact ⟨hle, hnge⟩
    · intro ⟨hle, hnge⟩
      rcases hle with (hlt | heq)
      · exact hlt
      · exfalso
        apply hnge
        exact Or.inr heq.symm
  le_antisymm x y hxy hyz := by
    rcases hxy with (hlt | heq)
    · rcases hyz with (hlt' | heq')
      · exfalso; exact not_gt_and_lt x y ⟨hlt', hlt⟩
      · exact heq'.symm
    · exact heq
  le_total x y := by
    rcases trichotomous' x y with (hgt | hlt | heq)
    · right; exact Or.inl hgt
    · left; exact Or.inl hlt
    · right; exact Or.inr heq.symm
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left a b h c := by
    rcases h with (hlt | heq)
    · exact Or.inl (add_lt_add_right c hlt)
    · rw [heq]
  add_le_add_right a b h c := by
    rcases h with (hlt | heq)
    · simpa [add_comm] using Or.inl (add_lt_add_right c hlt)
    · rw [heq]
  mul_lt_mul_of_pos_left a ha b c hbc := by
    have hapos : Rat.isPos a := (zero_lt_iff_isPos a).mp ha
    have h_mul := mul_lt_mul_right hbc hapos
    -- h_mul : b * a < c * a
    simpa [mul_comm, add_comm] using h_mul
  mul_lt_mul_of_pos_right c hc a b hab := by
    have hcpos : Rat.isPos c := (zero_lt_iff_isPos c).mp hc
    -- mul_lt_mul_right hab hcpos : a * c < b * c
    exact mul_lt_mul_right hab hcpos
  le_of_add_le_add_left a b c h := by
    rcases h with (hlt | heq)
    · rw [lt_iff] at hlt
      have : (a + b) - (a + c) = b - c := by ring
      rw [this] at hlt
      exact Or.inl hlt
    · exact Or.inr (add_left_cancel heq)
  zero_le_one := by
    have hpos : (1 : Rat).isPos := ⟨(1 : ℤ), (1 : ℤ), by norm_num, by norm_num, rfl⟩
    exact Or.inl ((zero_lt_iff_isPos (1 : Rat)).mpr hpos)

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  rcases hxy with ⟨r, hrpos, hxy_eq⟩
  rcases hz with ⟨s, hspos, hz_eq⟩
  have h_pos_diff : x * z - y * z = r * s := by
    calc
      x * z - y * z = -(y * z - x * z) := by ring
      _ = -((y - x) * z) := by ring
      _ = -((-(x - y)) * z) := by ring
      _ = -((-(-r)) * z) := by rw [hxy_eq]
      _ = -(r * z) := by ring
      _ = -(r * (-s)) := by rw [hz_eq]
      _ = r * s := by ring
  have h_pos : (r * s).isPos := isPos_mul hrpos hspos
  rw [gt_iff, h_pos_diff]
  exact h_pos


/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hbq' : (b' : ℚ) ≠ 0 := by exact_mod_cast hb'
    apply (div_eq_div_iff hbq hbq').mpr
    exact_mod_cast h)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := by
    obtain ⟨a, b, hb, rfl⟩ := eq_diff n
    set q := (a : ℚ) / (b : ℚ) with hq
    have hq_den_nz : q.den ≠ 0 := q.den_nz
    have hb_ℚ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hcrossℚ : (q.num : ℚ) * (b : ℚ) = (a : ℚ) * (q.den : ℚ) := by
      apply (div_eq_div_iff (by exact_mod_cast hq_den_nz) hb_ℚ).mp
      calc
        (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
        _ = (a : ℚ) / (b : ℚ) := rfl
    have hcrossℤ : (q.num : ℤ) * b = a * (q.den : ℤ) := by exact_mod_cast hcrossℚ
    have h_den_nz : (q.den : ℤ) ≠ 0 := by exact_mod_cast hq_den_nz
    apply Quotient.sound
    simp [formalDiv, hb, PreRat.instSetoid]
    simpa [mul_comm] using hcrossℤ
  right_inv n := by
    have h' : (n.den : ℤ) ≠ 0 := by exact_mod_cast n.den_nz
    have h_mk : (n : Rat) = Quotient.mk PreRat.instSetoid ⟨(n.num : ℤ), (n.den : ℤ), h'⟩ := by
      apply Quotient.sound
      simp
    dsimp
    rw [h_mk]
    simp [Rat.num_div_den n]

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' a b := by
    obtain ⟨a₁, b₁, hb₁, rfl⟩ := eq_diff a
    obtain ⟨a₂, b₂, hb₂, rfl⟩ := eq_diff b
    calc
      equivRat ((a₁ // b₁) + (a₂ // b₂)) = equivRat (((a₁ * b₂ + b₁ * a₂ : ℤ) // (b₁ * b₂ : ℤ))) := by
        rw [Rat.add_eq a₁ a₂ hb₁ hb₂]
      _ = ((a₁ * b₂ + b₁ * a₂ : ℤ) : ℚ) / ((b₁ * b₂ : ℤ) : ℚ) := by
        dsimp [formalDiv]; simp [mul_ne_zero hb₁ hb₂]
      _ = ((a₁ : ℤ) : ℚ) / ((b₁ : ℤ) : ℚ) + ((a₂ : ℤ) : ℚ) / ((b₂ : ℤ) : ℚ) := by
        have hb₁q : (b₁ : ℚ) ≠ 0 := by exact_mod_cast hb₁
        have hb₂q : (b₂ : ℚ) ≠ 0 := by exact_mod_cast hb₂
        field_simp [hb₁q, hb₂q]
        push_cast
        ring
      _ = equivRat (a₁ // b₁) + equivRat (a₂ // b₂) := by
        dsimp [formalDiv]; simp [hb₁, hb₂]
  map_mul' a b := by
    obtain ⟨a₁, b₁, hb₁, rfl⟩ := eq_diff a
    obtain ⟨a₂, b₂, hb₂, rfl⟩ := eq_diff b
    calc
      equivRat ((a₁ // b₁) * (a₂ // b₂)) = equivRat (((a₁ * a₂ : ℤ) // (b₁ * b₂ : ℤ))) := by
        rw [Rat.mul_eq a₁ a₂ hb₁ hb₂]
      _ = ((a₁ * a₂ : ℤ) : ℚ) / ((b₁ * b₂ : ℤ) : ℚ) := by
        dsimp [formalDiv]; simp [mul_ne_zero hb₁ hb₂]
      _ = (((a₁ : ℤ) : ℚ) / ((b₁ : ℤ) : ℚ)) * (((a₂ : ℤ) : ℚ) / ((b₂ : ℤ) : ℚ)) := by
        have hb₁q : (b₁ : ℚ) ≠ 0 := by exact_mod_cast hb₁
        have hb₂q : (b₂ : ℚ) ≠ 0 := by exact_mod_cast hb₂
        field_simp [hb₁q, hb₂q]
        push_cast
        ring
      _ = equivRat (a₁ // b₁) * equivRat (a₂ // b₂) := by
        dsimp [formalDiv]; simp [hb₁, hb₂]

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2

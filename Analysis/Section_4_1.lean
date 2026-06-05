import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of {lean}`ℕ`.

- Equivalence with the Mathlib integers {name}`_root_.Int` (or {lean}`ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro ⟨a, b⟩; rfl
    symm := by intro ⟨a, b⟩ ⟨c, d⟩ h; exact h.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

example : (3:ℕ) = 3 —— 0 := rfl

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

-- 隐式转换(coercion / cast)：将自然数变量转换为整数
theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

-- 自然数字面量的转换，如：(42: Int)
@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  rw [natCast_eq, ofNat_eq, Int.eq]
  simp

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp_all [Int.eq]
    grind)

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, hge, hn ⟩ ⟩
  simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  simp at hn
  grind

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩
  simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int := by
  apply AddGroup.ofLeftAxioms
  · intro x y z
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    obtain ⟨e, f, rfl⟩ := Int.eq_diff z
    simp_rw [Int.add_eq, Int.eq]
    abel
  · intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    rw [ofNat_eq, add_eq]
    simp
  · intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    rw [neg_eq, add_eq, ofNat_eq, Int.eq]
    abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro x y
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    simp [Int.add_eq, Int.eq]; abel

-- add_left_cancel and add_right_cancel are already provided by AddGroup
example (m n: Int): m = n ↔ m + a = n + a := by grind

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro x y
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    simp [mul_eq, eq]
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq, eq]
    ring
  one_mul := by
    intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    simp [ofNat_eq, mul_eq]
  mul_one := by
    intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    simp [ofNat_eq, mul_eq]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro x y z
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    obtain ⟨e, f, rfl⟩ := Int.eq_diff z
    simp [add_eq, mul_eq, add_eq, eq]
    ring
  right_distrib := by
    intro x y z
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    obtain ⟨e, f, rfl⟩ := Int.eq_diff z
    simp [add_eq, mul_eq, eq]
    ring
  zero_mul := by
    intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    simp [ofNat_eq, mul_eq]
  mul_zero := by
    intro x
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    simp [ofNat_eq, mul_eq]

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp [Int.sub_eq, Int.natCast_eq, Int.neg_eq, Int.add_eq]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  have hnz1 (x y: Int): x.IsPos ∧ y.IsPos → ¬(x * y = 0) := by
    rintro ⟨⟨a, ⟨ha1, ha2⟩⟩, ⟨b, ⟨hb1, hb2⟩⟩⟩
    have h1: x = a —— 0 := ha2
    have h2: y = b —— 0 := hb2
    rw [h1, h2, mul_eq, ofNat_eq, eq]
    simp
    grind

  have hnz2 (x y: Int): x.IsPos ∧ y.IsNeg → ¬(x * y = 0) := by
    rintro ⟨⟨a, ⟨ha1, ha2⟩⟩, ⟨b, ⟨hb1, hb2⟩⟩⟩
    have h1: x = a —— 0 := ha2
    have h2: y = 0 —— b := hb2
    rw [h1, h2, mul_eq, ofNat_eq, eq]
    simp
    grind

  have hnz3 (x y: Int): x.IsNeg ∧ y.IsNeg → ¬(x * y = 0) := by
    rintro ⟨⟨a, ⟨ha1, ha2⟩⟩, ⟨b, ⟨hb1, hb2⟩⟩⟩
    have h1: x = 0 —— a := ha2
    have h2: y = 0 —— b := hb2
    rw [h1, h2, mul_eq, ofNat_eq, eq]
    simp
    grind

  rcases trichotomous a with (ha0 | hpos | hneg)
  . grind
  . rcases trichotomous b with (hb0 | hbpos | hbneg)
    . grind
    . specialize hnz1 a b ⟨hpos, hbpos⟩; contradiction
    . specialize hnz2 a b ⟨hpos, hbneg⟩; contradiction
  . rcases trichotomous b with (hb0 | hbpos | hbneg)
    . grind
    . specialize hnz2 b a ⟨hbpos, hneg⟩
      rw [mul_comm] at h
      contradiction
    . specialize hnz3 a b ⟨hneg, hbneg⟩; contradiction

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have hsub : (a - b) * c = 0 := by
    rw [sub_mul, h, sub_self]
  rcases Int.mul_eq_zero hsub with (h_zero | hc_zero)
  · have : a + (-b) + b = 0 + b := by grind
    simpa
  · contradiction

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [Int.lt_iff]
  constructor
  · rintro ⟨⟨t, ht⟩, hne⟩
    have : t ≠ 0 := by
      by_contra h1
      rw [h1] at ht
      simp at ht
      rw [ht] at hne
      contradiction
    use t
  · rintro ⟨n, hnz, hn⟩
    have : a ≠ b := by
      by_contra h1
      rw [h1] at hn
      simp at hn
      rw [cast_eq_0_iff_eq_0] at hn
      contradiction
    simp [this]
    use n

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff] at h ⊢
  obtain ⟨⟨t, h1⟩, hne⟩ := h
  constructor
  . use t; grind
  . grind

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff] at hab hc ⊢

  obtain ⟨⟨t, h1⟩, hne⟩ := hab
  obtain ⟨⟨tc, h2⟩, hnec⟩ := hc

  constructor
  . have h3: b * c = (a + t) * c := by grind
    rw [add_mul] at h3
    use tc * t
    simp_all
    grind
  . by_contra hmeq
    have heq := mul_right_cancel₀ _ _ _ hmeq hnec.symm
    contradiction

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  obtain ⟨⟨t, ht⟩, hne⟩ := h
  rw [lt_iff]
  constructor
  . use t; grind
  . grind

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rcases h with ⟨t, ht⟩
  rw [le_iff]
  use t
  grind

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rcases hab with ⟨⟨t, ht⟩, hne1⟩
  rcases hbc with ⟨⟨s, hs⟩, hne2⟩

  have hst: c = a + t + s := by grind

  rw [lt_iff]
  constructor
  . use t + s
    grind
  . by_contra h1
    set t' := t + s
    rw [h1] at hst
    have h2: t' = (0:Int) := by grind
    rw [cast_eq_0_iff_eq_0] at h2
    have h3: t = 0 ∧ s = 0 := by grind
    simp [h3.1] at ht
    rw [ht] at hne1
    contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
  obtain ⟨b₁, b₂, rfl⟩ := Int.eq_diff b
  by_cases h : a₁ + b₂ ≤ b₁ + a₂
  · rcases Nat.le.dest h with ⟨t, ht⟩
    by_cases hzero : t = 0
    · subst t; simp at ht
      right; right; apply Quotient.sound; simp; omega
    · right; left
      refine ⟨⟨t, ?_⟩, ?_⟩
      · rw [Int.natCast_eq t, Int.add_eq a₁ a₂ t 0, Int.eq]; omega
      · intro heq; have := (Int.eq _ _ _ _).mp heq; simp at this; omega
  · push_neg at h
    have h' : b₁ + a₂ ≤ a₁ + b₂ := by omega
    rcases Nat.le.dest h' with ⟨t, ht⟩
    by_cases hzero : t = 0
    · subst t; simp at ht
      right; right; apply Quotient.sound; simp; omega
    · left
      refine ⟨⟨t, ?_⟩, ?_⟩
      · rw [Int.natCast_eq t, Int.add_eq b₁ b₂ t 0, Int.eq]; omega
      · intro heq; have := (Int.eq _ _ _ _).mp heq; simp at this; omega

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b) := by
  by_contra h
  have h1 := lt_trans h.1 h.2
  rw [lt_iff] at h1
  obtain ⟨_, hnb⟩ := h1
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b) := by
  rintro ⟨⟨_, hne⟩, heq⟩
  rw [heq] at hne
  contradiction

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b) := by
  rintro ⟨⟨_, hne⟩, heq⟩
  rw [heq] at hne
  contradiction

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        -- apply add_le_add_right 0
        rcases Nat.le.dest h with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [Int.natCast_eq t, Int.add_eq a b t 0, Int.eq]
        omega
      | isFalse h =>
        apply isFalse
        intro hle
        rcases hle with ⟨t, ht⟩
        rw [Int.natCast_eq t, Int.add_eq a b t 0, Int.eq] at ht
        apply h
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor
  · intro h
    have h0 := h 0
    simp at h0
    grind
  · intro h
    subst h
    simp

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by
    intro a; exact ⟨0, by simp⟩
  le_trans := by
    intro a b c h1 h2
    rcases h1 with ⟨t, ht⟩
    rcases h2 with ⟨s, hs⟩
    refine ⟨t + s, ?_⟩
    rw [hs, ht]; push_cast; ring
  lt_iff_le_not_ge := by
    intro a b
    rw [Int.lt_iff]
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨hle, ?_⟩
      rcases hle with ⟨t, ht⟩
      intro hge; rcases hge with ⟨s, hs⟩
      apply hne
      have hsum : a = a + ((t + s : ℕ) : Int) := by
        calc
          a = b + (s : Int) := hs
          _ = (a + (t : Int)) + (s : Int) := by rw [ht]
          _ = a + (((t + s : ℕ) : Int)) := by push_cast; ring
      have hzero_int : ((t + s : ℕ) : Int) = 0 := by
        apply add_left_cancel (a := a) (c := 0)
        simpa [add_zero] using hsum
      have hzero_nat : t + s = 0 := ((Int.natCast_inj (t + s) 0).mp hzero_int)
      have ht0 : t = 0 := by omega
      rw [ht0, Nat.cast_zero, add_zero] at ht
      exact ht.symm
    · rintro ⟨hle, hnge⟩
      refine ⟨hle, ?_⟩
      intro heq; apply hnge; rw [heq]; exact ⟨0, by simp⟩
  le_antisymm := by
    intro a b h1 h2
    rcases h1 with ⟨t, ht⟩
    rcases h2 with ⟨s, hs⟩
    have hsum : a = a + ((t + s : ℕ) : Int) := by
      calc
        a = b + (s : Int) := hs
        _ = (a + (t : Int)) + (s : Int) := by rw [ht]
        _ = a + (((t + s : ℕ) : Int)) := by push_cast; ring
    have hzero_int : ((t + s : ℕ) : Int) = 0 := by
      apply add_left_cancel (a := a) (c := 0)
      simpa [add_zero] using hsum
    have hzero_nat : t + s = 0 := ((Int.natCast_inj (t + s) 0).mp hzero_int)
    have ht0 : t = 0 := by omega
    rw [ht0, Nat.cast_zero, add_zero] at ht
    exact ht.symm
  le_total := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := Int.eq_diff b
    by_cases h : a₁ + b₂ ≤ b₁ + a₂
    · left; rcases Nat.le.dest h with ⟨t, ht⟩; refine ⟨t, ?_⟩
      rw [Int.natCast_eq t, Int.add_eq a₁ a₂ t 0, Int.eq]; omega
    · right; have h' : b₁ + a₂ ≤ a₁ + b₂ := by omega
      rcases Nat.le.dest h' with ⟨t, ht⟩; refine ⟨t, ?_⟩
      rw [Int.natCast_eq t, Int.add_eq b₁ b₂ t 0, Int.eq]; omega
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  have h1: -1 = 0 —— 1 := rfl
  obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
  rw [h1, mul_eq, neg_eq]
  simp

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  refine ⟨fun n => 0 ≤ n, ?_, ?_⟩
  · constructor
    · exact le_refl 0
    · intro n hn
      rcases hn with ⟨t, ht⟩
      refine ⟨t + 1, ?_⟩
      rw [ht]
      push_cast
      ring
  · intro h
    have hneg : 0 ≤ (-1 : Int) := h (-1)
    rcases hneg with ⟨t, ht⟩
    have h_eq := (Int.eq 0 1 t 0).mp (by
      simpa [Int.natCast_eq, Int.neg_eq, add_zero] using ht)
    omega

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  rcases h with ⟨a, ha⟩
  simp [natCast_eq] at ha
  rw [ha, mul_eq]
  simp
  rw [←natCast_eq]
  rw [le_iff]
  use a*a
  simp

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases Int.trichotomous n with (rfl | ⟨k, hk, hn⟩ | ⟨k, hk, hn⟩)
  · simp
  · rw [hn]
    have h0k : 0 ≤ ((k : ℕ) : Int) := ⟨k, by simp⟩
    exact Int.sq_nonneg_of_pos ((k : ℕ) : Int) h0k
  · rw [hn]
    have h0k : 0 ≤ ((k : ℕ) : Int) := ⟨k, by simp⟩
    have hsq : (-((k : ℕ) : Int)) * (-((k : ℕ) : Int)) = ((k : ℕ) : Int) * ((k : ℕ) : Int) := by ring
    rw [hsq]
    exact Int.sq_nonneg_of_pos ((k : ℕ) : Int) h0k

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h := Int.sq_nonneg n
  rcases h with ⟨m, hm⟩
  simp at hm
  use m

/--
  Not in textbook: create an equivalence between {name}`Int` and {lean}`ℤ`.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
def Int.toInt (x : Int) : ℤ :=
  Quotient.lift (fun ⟨a, b⟩ => (a : ℤ) - (b : ℤ)) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp at h
    push_cast
    omega) x

def Int.ofInt : ℤ → Int
  | .ofNat n => n —— 0
  | .negSucc n => 0 —— (n+1)

@[simp]
theorem Int.toInt_mk (a b : ℕ) : Int.toInt (a —— b) = (a : ℤ) - (b : ℤ) := rfl

@[simp]
theorem Int.ofInt_ofNat (n : ℕ) : Int.ofInt (.ofNat n) = n —— 0 := rfl

@[simp]
theorem Int.ofInt_negSucc (n : ℕ) : Int.ofInt (.negSucc n) = 0 —— (n+1) := rfl

abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Int.toInt
  invFun := Int.ofInt
  left_inv n := by
    obtain ⟨a, b, rfl⟩ := Int.eq_diff n
    simp [Int.toInt, Int.ofInt]
    by_cases h : a ≤ b
    · rcases Nat.le.dest h with ⟨k, hk⟩
      by_cases hk0 : k = 0
      · subst k
        have ha_eq_b : a = b := by omega
        subst ha_eq_b; simp [Int.eq]
      · have hsub : (a : ℤ) - (b : ℤ) = .negSucc (k - 1) := by
          have hk' : (b : ℤ) = (a : ℤ) + (k : ℤ) := by exact_mod_cast hk.symm
          rw [hk']
          cases k
          · exfalso; exact hk0 rfl
          · simp; omega
        rw [hsub]; simp [Int.eq]; omega
    · have h' : b ≤ a := Nat.le_of_lt (by omega)
      rcases Nat.le.dest h' with ⟨k, hk⟩
      by_cases hk0 : k = 0
      · subst k
        have ha_eq_b : a = b := by omega
        subst ha_eq_b; simp [Int.eq]
      · have hsub : (a : ℤ) - (b : ℤ) = .ofNat k := by
          have hk' : (a : ℤ) = (b : ℤ) + (k : ℤ) := by exact_mod_cast hk.symm
          rw [hk']
          simp
        rw [hsub]; simp [Int.eq]; omega
  right_inv
    | .ofNat n => rfl
    | .negSucc n => by
      show (Int.toInt (0 —— (n+1))) = .negSucc n
      rw [Int.toInt_mk]
      have : (0 : ℤ) - ((n+1 : ℕ) : ℤ) = .negSucc n := by
        push_cast
        rfl
      exact this

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    simp [Int.toInt, Int.add_eq]
    ring
  map_mul' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    simp [Int.toInt, Int.mul_eq]
    ring
  map_le_map_iff' := by
    intro x y
    obtain ⟨a, b, rfl⟩ := Int.eq_diff x
    obtain ⟨c, d, rfl⟩ := Int.eq_diff y
    rw [Int.le_iff]
    constructor
    · intro hle
      have hle' : (a : ℤ) - (b : ℤ) ≤ (c : ℤ) - (d : ℤ) := by
        simpa [Int.toInt, Int.toInt_mk] using hle
      have h_nat : a + d ≤ c + b := by
        have : (a : ℤ) + (d : ℤ) ≤ (c : ℤ) + (b : ℤ) := by
          have h := add_le_add_right hle' ((b : ℤ) + (d : ℤ))
          linarith
        exact_mod_cast this
      rcases Nat.le.dest h_nat with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      apply Quotient.sound
      simp
      simpa [add_comm, add_left_comm, add_assoc] using ht.symm
    · rintro ⟨t, ht⟩
      rw [show ((a —— b) + (t : Int)) = ((a + t) —— b) by
        simp [Int.natCast_eq, Int.add_eq]] at ht
      have h_eq := (Int.eq _ _ _ _).mp ht
      simp at h_eq
      have h_eq' : (c : ℤ) + (b : ℤ) = (a : ℤ) + (t : ℤ) + (d : ℤ) := by exact_mod_cast h_eq
      have h_nonneg : (0 : ℤ) ≤ (t : ℤ) := by exact_mod_cast Nat.zero_le t
      have h_sum : (a : ℤ) + (d : ℤ) ≤ (c : ℤ) + (b : ℤ) := by
        rw [h_eq']
        linarith
      -- Convert back to the Int.toInt form
      have hgoal : (a : ℤ) - (b : ℤ) ≤ (c : ℤ) - (d : ℤ) := by linarith
      simpa [Int.toInt, Int.toInt_mk] using hgoal

end Section_4_1

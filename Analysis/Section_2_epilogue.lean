import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  rw [succ_add, succ_toNat, succ_toNat, hn]
  grind

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  . rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  rw [succ_mul, map_add, succ_toNat, _root_.Nat.add_mul]
  grind

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  constructor
  . -- →
    induction' n with n hn
    . rw [show zero = 0 from rfl]
      grind [zero_le]
    rw [succ_toNat]
    intro h
    have: n.toNat ≤ m.toNat:= by grind
    specialize hn this
    rw [←lt_iff_succ_le]
    have : m ≠ n := by grind
    grind
  . -- ←
    intro h
    obtain ⟨a, ha⟩ := h
    rw [ha, map_add]
    grind

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m ih
  · grind
  · rw [pow_succ, map_mul, succ_toNat, _root_.Nat.pow_succ, ih]

/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  unfold Function.Injective
  intro a b h

  induction' a with a ih generalizing b
  · cases' b with b'
    · rfl
    · rw [natCast, natCast] at h
      have h1 := h.symm
      have h2 := P.succ_ne (P.natCast b')
      contradiction
  · cases' b with b'
    · rw [natCast, natCast] at h
      have h1 := P.succ_ne (P.natCast a)
      contradiction
    · have h1 := P.succ_cancel h
      have heq := ih h1
      grind

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  apply P.induction
  . use 0
  intro n ih
  obtain ⟨m, hm⟩ := ih
  use m + 1
  rw [natCast, hm]

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat   -- ≃ : exist bijection mapping F (P.Nat) -> Q.Nat
  equiv_zero : equiv P.zero = Q.zero  -- F (P.zero) = Q.zero
  -- F(P.succ n) = Q.succ F(n)
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (h: Equiv P Q) : Equiv Q P where
  equiv := h.equiv.symm  -- inverse of bijection mapping F, F'(Q.Nat) -> P.Nat
  equiv_zero := by
    -- F'(F(a)) = a
    have h1 : h.equiv.symm (h.equiv P.zero) = P.zero := by grind
    rwa [h.equiv_zero] at h1
  equiv_succ n := by
    apply h.equiv.injective
    rw [h.equiv_succ]
    simp

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (f1 : Equiv P Q) (f2 : Equiv Q R) : Equiv P R where
  equiv := f1.equiv.trans f2.equiv
  equiv_zero := by
    simp [f1.equiv_zero, f2.equiv_zero]
  equiv_succ n := by
    simp [f1.equiv_succ, f2.equiv_succ]

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P) -- P.natCast is surjective, so an inverse can be constructed
    -- invFun (toFun a) = a
    left_inv := by
      unfold Function.LeftInverse
      intro x
      apply (natCast_injective P)
      apply Function.surjInv_eq (natCast_surjective P)
    -- toFun (invFun a) = a
    right_inv := Function.surjInv_eq (natCast_surjective P)
  }
  equiv_zero := rfl
  equiv_succ n := rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q :=
  ((Equiv.fromNat P).symm.trans (Equiv.fromNat Q))

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  refine P.induction (fun m => equiv1 m = equiv2 m) ?_ ?_ n
  · simp [equiv_zero1, equiv_zero2]
  · intro n ih
    rw [equiv_succ1, equiv_succ2, ih]

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  let e := (Equiv.fromNat P).equiv
  have hzero_symm : e.symm P.zero = (0 : ℕ) := by
    apply e.injective
    calc
      e (e.symm P.zero) = P.zero := by simp
      _ = e (0 : ℕ) := by simpa using ((Equiv.fromNat P).equiv_zero).symm
  have hsucc_symm : ∀ n : P.Nat, e.symm (P.succ n) = Nat.succ (e.symm n) := by
    intro n
    apply e.injective
    calc
      e (e.symm (P.succ n)) = P.succ n := by simp
      _ = P.succ (e (e.symm n)) := by simp
      _ = e (Nat.succ (e.symm n)) := ((Equiv.fromNat P).equiv_succ (e.symm n)).symm
  let a_ℕ : ℕ → ℕ := Nat.rec (e.symm c) (fun k r => e.symm (f (e k) (e r)))
  let a : P.Nat → P.Nat := fun n => e (a_ℕ (e.symm n))
  have ha_zero : a P.zero = c := by
    calc
      a P.zero = e (a_ℕ (e.symm P.zero)) := rfl
      _ = e (a_ℕ 0) := by rw [hzero_symm]
      _ = e (e.symm c) := rfl
      _ = c := by simp
  have ha_succ : ∀ n, a (P.succ n) = f n (a n) := by
    intro n
    calc
      a (P.succ n) = e (a_ℕ (e.symm (P.succ n))) := rfl
      _ = e (a_ℕ (Nat.succ (e.symm n))) := by rw [hsucc_symm]
      _ = e (e.symm (f (e (e.symm n)) (e (a_ℕ (e.symm n))))) := rfl
      _ = f (e (e.symm n)) (e (a_ℕ (e.symm n))) := by simp
      _ = f n (a n) := by simp [a]
  refine ⟨a, ⟨ha_zero, ha_succ⟩, ?_⟩
  intro b ⟨hb_zero, hb_succ⟩
  ext n
  refine P.induction (fun m => b m = a m) ?_ ?_ n
  · simp [ha_zero, hb_zero]
  · intro m ih
    rw [ha_succ, hb_succ, ih]

end PeanoAxioms

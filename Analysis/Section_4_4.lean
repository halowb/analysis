import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  apply existsUnique_of_exists_of_unique
  . -- exist
    rw [←Rat.num_div_den x]

    have h := Int.mul_ediv_add_emod (x.num) (x.den)

    have : x.den > 0 := by grind [x.den_nz]

    have hmod_lt := Int.emod_lt (x.num) (show (x.den:ℤ) ≠ 0 by grind)
    simp at hmod_lt

    have hmod_nz:= Int.emod_nonneg x.num (show (x.den:ℤ) ≠ 0 by grind [x.den_nz])

    set d := x.den
    set q := (x.num / ↑x.den)
    set r := x.num % x.den
    use q
    constructor
    . rw [←h]; field_simp; norm_cast; rw [mul_comm]; simp;
      linarith
    . rw [←h]; field_simp; norm_cast; rw [mul_add]; simp;
      linarith
  . -- unique
    intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    rcases lt_trichotomy a b with hlt | heq | hgt
    . have h1: a + 1 ≤ b := by linarith
      have h2: (b:ℚ) < (a:ℚ) + 1 := by linarith
      norm_cast at h2
      linarith
    . exact heq
    . have h1: b + 1 ≤ a := by linarith
      have h2: (a:ℚ) < (b:ℚ) + 1 := by linarith
      norm_cast at h2
      linarith

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  rcases lt_trichotomy x 0 with hlt | hz | hgt
  . use 1; linarith
  . use 1; rw [hz]; norm_num;
  . rw [←Rat.num_div_den x] at hgt
    have : x.den > 0 := by grind [x.den_nz]
    qify at this
    have h1:= mul_lt_mul_of_pos_left hgt this
    field_simp at h1
    have h2: (x.num:ℚ) > 0 := by grind
    norm_cast at h2
    let n: ℕ := x.num.toNat
    have: n = x.num := by grind
    use n + 1
    rw [←Rat.num_div_den x, ←this]
    field_simp
    norm_cast
    have : x.den > 0 := by grind [x.den_nz]
    have : 1 ≤ x.den := by grind
    have := mul_le_mul_right (n + 1) this
    linarith

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  by_contra h
  obtain ⟨f, hf⟩ := h
  let x := f 0

  have h1 (n:ℕ): f (n) < x + 1 - n := by
    induction' n with n ih
    . simp; grind
    . have h2 := hf n
      have h3 : f n ≤ x + 1 - (n + 1) := by grind
      linarith

  have h3:= h1 (x + 1)
  simp at h3

/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  let f : ℕ → ℤ := fun n => -n
  use f
  intro n
  simp [f]

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  let f : ℕ → {x: ℚ // 0 < x} := fun n => ⟨1/(n+1), by positivity⟩
  use f
  intro n
  simp [f]
  field_simp
  grind

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  rw [Even, Odd]
  induction' n with n ih
  . left; use 0;
  . rcases ih with (h1 | h2)
    . obtain ⟨r, hr⟩ := h1
      right; use r; rw [hr]; grind
    . obtain ⟨k, hk⟩ := h2
      left; use k + 1; rw [hk]; grind

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  by_contra h
  rw [Even, Odd] at h
  obtain ⟨r, hr⟩ := h.1
  obtain ⟨k, hk⟩ := h.2
  rw [hr] at hk
  grind

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx; grind
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . have: k > 0 := by grind
        have: k^2 > 0 := by positivity
        have: 2 * k ^ 2 < 4 * k ^ 2 := by grind
        have: q^2 < (2*k)^2 := by grind
        grind [sq_lt_sq₀ (show q ≥ 0 by grind)]
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      choose q hq using hp
      have: p^2 = 4 * q^2 + 4 * q + 1 := by grind
      rw [odd_iff_exists_bit1]
      use 2*q^2 + 2*q
      grind
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num

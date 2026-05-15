import Mathlib.NumberTheory.Real.Irrational


def hello := "world"

-- A function computes values
def factorial (n : ℕ) : ℕ :=
    match n with
    | 0 => 1
    | n' + 1 => (n' + 1) * factorial n'

-- A theorem proves properties
theorem factorial_pos (n : ℕ) : 0 < factorial n := by
    induction n with
    | zero => simp [factorial]
    -- n becomes n' + 1
    -- ih is a proof of 0 < factorial n'
    | succ n' ih =>
      simp [factorial];
      -- The goal is now 0 < factorial n'
      exact ih

theorem Square_root_irrational : Irrational (√2) := by
    rw[irrational_iff_ne_rational]
    intro a b hb_ne_zero
    by_contra hP
    let c := a / Int.gcd a b
    let d := b / Int.gcd a b
    have hsqrt2_eq_cd : √2 = c / d := by
        dsimp[c,d]
        apply?


example (a b : ℕ) (h : b ≠ 0) : (a / (Int.gcd a b)) / (b / (Int.gcd a b)) = a / b := by
    apply?

example (a b : ℕ)

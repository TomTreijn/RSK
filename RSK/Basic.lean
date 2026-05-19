import Mathlib.NumberTheory.Real.Irrational


def hello := "world"

def factorial (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | n' + 1 => (n' + 1) * factorial n'

#eval factorial 3 -- evaluates to 6



theorem factorial_pos (n : Nat) : 0 < factorial n := by
    induction n with
    | zero => simp [factorial]
    -- n becomes n' + 1
    -- ih is a proof of 0 < factorial n'
    | succ n' ih =>
      simp [factorial];
      -- The goal is now 0 < factorial n'
      exact ih

theorem factorial_pos₂ : ∀ (n : Nat), 0 < factorial n := factorial_pos
theorem factorial_pos₃ : (n : Nat) → 0 < factorial n := factorial_pos

example (a b : ℕ) (h : b ≠ 0) : (a / (Int.gcd a b)) / (b / (Int.gcd a b)) = a / b := by
    apply?


#eval (fun (a b : Nat) ↦ a ≤ b) 1 2

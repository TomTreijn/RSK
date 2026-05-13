def hello := "world"

-- A function computes values
def factorial : Nat → Nat
    | 0 => 1
    | n + 1 => (n + 1) * factorial n

-- A theorem proves properties
theorem factorial_pos : ∀ (n : Nat), 0 < factorial n := by
    intro n
    induction n with
    | zero => simp [factorial]
    -- n becomes n' + 1
    -- ih is a proof of 0 < factorial n'
    | succ n' ih =>
      simp [factorial];
      -- The goal is now 0 < factorial n'
      exact ih

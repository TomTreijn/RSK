/-- option_r desribes a relation on two Optional variables, being true if either is none.

  For example, replacing a number k' with k at index i in a weakly increasing list l is valid if
    l[i-1] ≤ l[i] ≤ l[i+1], but only if these neighbours exist. So with these functions, this can be desribed as
    option_r l[i-1]? l[i]? ∧ option_r l[i]? l[i+1]?
  -/

def option_r {α : Type} (r : α → α → Prop) (a b : Option α) :=
  match a, b with
  | some a, some b => r a b
  | _, _ => True

def op_lt (a b : Option Nat) := option_r (· < ·) a b
def op_le (a b : Option Nat) := option_r (· ≤ ·) a b
def op_ge (a b : Option Nat) := option_r (· ≥ ·) a b

@[simp]
theorem option_r_some : option_r r (some a) (some b) = (r a b) := by rfl
@[simp]
theorem op_le_some : op_le (some a) (some b) = (a ≤ b) := by rfl
@[simp]
theorem op_lt_some : op_lt (some a) (some b) = (a < b) := by rfl
@[simp]
theorem op_ge_some : op_ge (some a) (some b) = (a ≥ b) := by rfl

@[simp]
theorem option_r_left_none r : option_r r (none) (b) := by simp only [option_r.eq_def]
@[simp]
theorem op_le_none_l : op_le none a := option_r_left_none (· ≤ ·)
@[simp]
theorem op_lt_none_l : op_lt none a := option_r_left_none (· < ·)
@[simp]
theorem op_ge_none_l : op_ge none a := option_r_left_none (· ≥ ·)

@[simp]
theorem option_r_right_none r : option_r r (a) (none) := by simp only [option_r.eq_def]
@[simp]
theorem op_le_none_r : op_le a none := option_r_right_none (· ≤ ·)
@[simp]
theorem op_lt_none_r : op_lt a none := option_r_right_none (· < ·)
@[simp]
theorem op_ge_none_r : op_ge a none := option_r_right_none (· ≥ ·)

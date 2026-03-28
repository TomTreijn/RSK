
set_option relaxedAutoImplicit true

def option_r (r : Nat → Nat → Prop) (a b : Option Nat) :=
  match a, b with
  | some a, some b => r a b
  | _, _ => True

def op_lt (a b : Option Nat) := option_r (· < ·) a b
def op_le (a b : Option Nat) := option_r (· ≤ ·) a b
def op_ge (a b : Option Nat) := option_r (· ≥ ·) a b

theorem option_r_some : option_r r (some a) (some b) = (r a b) := by rfl
theorem op_le_some : op_le (some a) (some b) = (a ≤ b) := by rfl
theorem op_lt_some : op_lt (some a) (some b) = (a < b) := by rfl
theorem op_ge_some : op_ge (some a) (some b) = (a ≥ b) := by rfl

theorem option_r_left_none r : option_r r (none) (b) := by simp only [option_r.eq_def]
theorem op_le_none_l : op_le none a := option_r_left_none (· ≤ ·)
theorem op_lt_none_l : op_lt none a := option_r_left_none (· < ·)
theorem op_ge_none_l : op_ge none a := option_r_left_none (· ≥ ·)

theorem option_r_right_none r : option_r r (a) (none) := by simp only [option_r.eq_def]
theorem op_le_none_r : op_le a none := option_r_right_none (· ≤ ·)
theorem op_lt_none_r : op_lt a none := option_r_right_none (· < ·)
theorem op_ge_none_r : op_ge a none := option_r_right_none (· ≥ ·)

def IsMonotone (r : Nat → Nat → Prop) (list : List Nat) : Prop :=
  match list with
  | [] => True
  | [_] => True
  | a :: b :: tail => r a b ∧ IsMonotone r (b :: tail)

def IsWeakInc (list : List Nat) : Prop := IsMonotone (· ≤ ·) list
def IsStrictInc (list : List Nat) : Prop := IsMonotone (· < ·) list
def IsWeakDec (list : List Nat) : Prop := IsMonotone (· ≥ ·) list

theorem monotone_tail_monotone (h : IsMonotone r (a :: tail)) : IsMonotone r tail := by
  cases tail with
  | nil => exact h
  | cons b tail2 =>
    exact h.right

theorem wkinc_tail_wkinc (h : IsWeakInc (a :: tail)) : IsWeakInc (tail) := monotone_tail_monotone h
theorem stinc_tail_stinc (h : IsStrictInc (a :: tail)) : IsStrictInc (tail) := monotone_tail_monotone h
theorem wkdec_tail_wkdec (h : IsWeakDec (a :: tail)) : IsWeakDec (tail) := monotone_tail_monotone h

def IsMonotone2 (r : Nat → Nat → Prop) (list : List Nat) : Prop :=
  ∀i j : Nat, (i_lt_j : i < j) → (j_le_l : j < list.length) → r (list[i]'(Nat.lt_trans i_lt_j j_le_l)) (list[j]'j_le_l)

def IsWeakInc2 (list : List Nat) : Prop := IsMonotone2 (· ≤ ·) list
def IsStrictInc2 (list : List Nat) : Prop := IsMonotone2 (· < ·) list
def IsWeakDec2 (list : List Nat) : Prop := IsMonotone2 (· ≥ ·) list

theorem monotone2_tail_monotone2 (h_ord : IsMonotone2 r (a :: tail)) : IsMonotone2 r tail := by
  intro i j i_lt_j j_le_l
  have i_lt_j_succ := Nat.add_lt_add_right i_lt_j 1
  have j_le_l_succ : j + 1 < (a :: tail).length := Nat.add_lt_of_lt_sub j_le_l
  have hi := h_ord (i+1) (j+1) i_lt_j_succ j_le_l_succ
  have h₁ := List.getElem_cons_succ a (tail) i (Nat.lt_trans i_lt_j_succ j_le_l_succ)
  have h₂ := List.getElem_cons_succ a (tail) j j_le_l_succ
  rw[←h₁, ←h₂]
  exact hi

theorem monotone_monotone2 r (trans : ∀{a b c : Nat}, r a b → r b c → r a c) {list}
   : IsMonotone r list ↔ IsMonotone2 r list := by
  constructor
  · intro h_ord i j i_lt_j j_le_l
    have i_le_l : i < list.length := Nat.lt_trans i_lt_j j_le_l
    match list with
    | [] => contradiction
    | a :: [] =>
      repeat rw [List.length] at j_le_l
      have j_zero : j = 0 := Nat.lt_one_iff.mp j_le_l
      rw [j_zero] at i_lt_j
      contradiction
    | a :: b :: tail =>
      match i with
      | 0 =>
        match hj : j with
        | 0 => contradiction
        | 1 => simp only [List.getElem_cons_zero, List.getElem_cons_succ, h_ord.left]
        | k + 2 =>
          have h_ord_tail := monotone_tail_monotone h_ord
          have hi : IsMonotone2 r (b :: tail) := (monotone_monotone2 r trans).mp h_ord_tail
          have k_lt_l := Nat.succ_lt_succ_iff.mp j_le_l
          have hi₂ := hi 0 (k+1) (Nat.zero_lt_succ k) k_lt_l
          have h₁ : (b :: tail)[k+1] = (a :: b :: tail)[k+2] := List.getElem_cons_succ b tail k k_lt_l
          have h₂ : (b :: tail)[0] = (a :: b :: tail)[1] := List.getElem_cons_succ a (b::tail) 0 (Nat.lt_of_le_of_lt i_lt_j j_le_l)
          rw[h₂] at hi₂
          rw [←h₁]
          exact trans h_ord.left hi₂
      | k + 1 =>
        match j with
        | 0 => contradiction
        | q + 1 =>
          have h_ord_tail := monotone_tail_monotone h_ord
          have hi := (monotone_monotone2 r trans).mp h_ord_tail
          have hq_lt_l : q < (b::tail).length := Nat.succ_lt_succ_iff.mp j_le_l
          have hk_le_q : k < q := Nat.succ_lt_succ_iff.mp i_lt_j
          have hi₂ := hi k q hk_le_q hq_lt_l
          have h₁ : (b :: tail)[k] = (a :: b :: tail)[k+1] := List.getElem_cons_succ a (b::tail) k i_le_l
          have h₂ : (b :: tail)[q] = (a :: b :: tail)[q+1] := List.getElem_cons_succ a (b::tail) q j_le_l
          rw [←h₁, ←h₂]
          exact hi₂
  · intro h_ord
    match list with
    | [] => trivial
    | [a] => trivial
    | a :: b :: tail =>
      have h_ord_sub := monotone2_tail_monotone2 h_ord
      have hi := (monotone_monotone2 r trans).mpr h_ord_sub
      have a_le_b := h_ord 0 1 Nat.one_pos (Nat.one_lt_succ_succ tail.length)
      rw[IsMonotone]
      exact ⟨a_le_b, hi⟩

theorem wkinc_wkinc2 {list : List Nat} : IsWeakInc list ↔ IsWeakInc2 list :=
  monotone_monotone2 (· ≤ ·) Nat.le_trans
theorem stinc_stinc2 {list : List Nat} : IsStrictInc list ↔ IsStrictInc2 list :=
  monotone_monotone2 (· < ·) Nat.lt_trans
theorem wkdec_wkdec2 {list : List Nat} : IsWeakDec list ↔ IsWeakDec2 list :=
  monotone_monotone2 (· ≥ ·) (fun a b ↦ Nat.le_trans b a)

theorem montone_front_monotone r (h : IsMonotone r list) : IsMonotone r list.dropLast := by
  match list with
  | [] => simp[IsMonotone]
  | a :: [] => simp[IsMonotone]
  | a :: b :: [] => simp[IsMonotone]
  | a :: b :: c :: tail =>
    have ih₂ := montone_front_monotone r (monotone_tail_monotone h)
    exact ⟨h.left, ih₂⟩

theorem wkinc_front_wkinc (h : IsWeakInc list) : IsWeakInc list.dropLast := montone_front_monotone (· ≤ ·) h

theorem monotone_append_monotone (h_ord : IsMonotone r list) (n : Nat) (h_r : option_r r list.getLast? n) :
  IsMonotone r (list ++ [n]) := by
  match h_list : list with
  | [] => simp only [List.nil_append, IsMonotone]
  | a :: [] =>
    simp only [List.getLast?_singleton] at h_r
    rw[option_r_some] at h_r
    simp only [List.cons_append, List.nil_append, IsMonotone, and_true, h_r]
  | a :: b :: tail =>
    rw[List.getLast?_cons_cons] at h_r
    have hi := monotone_append_monotone (monotone_tail_monotone h_ord) n h_r
    simp only [List.cons_append, IsMonotone]
    constructor
    · exact h_ord.left
    · exact hi

theorem wkinc_append_wkinc (h_ord : IsWeakInc list) (n : Nat) (h_le : op_le list.getLast? n) :
  IsWeakInc (list ++ [n]) := monotone_append_monotone h_ord n h_le

theorem monotone_set_monotone r (h_ord : IsMonotone r list) (k i : Nat)
  (h_r : ((i=0) ∨ (option_r r list[i-1]? k)) ∧ (option_r r k list[i+1]?)) :
  IsMonotone r (list.set i k) := by
  match list with
  | [] => trivial
  | a :: [] =>
    match i with
    | 0 => trivial
    | i+1 => trivial
  | a :: b :: [] =>
    match i with
    | 0 =>
      have hkb : r k b := by
        simp [option_r] at h_r
        exact h_r
      trivial
    | 1 =>
      have hak : r a k := by
        simp [option_r] at h_r
        exact h_r
      trivial
    | i + 2 =>
      simp only [List.set_cons_succ, List.set_nil]
      exact h_ord
  | a :: b :: c :: tail =>
    match i with
    | 0 =>
      rw[List.set]
      simp [option_r] at h_r
      exact ⟨h_r, monotone_tail_monotone h_ord⟩
    | 1 =>
      repeat rw[List.set]
      simp [option_r] at h_r
      repeat rw[IsMonotone]
      rw[←and_assoc]
      exact ⟨h_r, monotone_tail_monotone (monotone_tail_monotone h_ord)⟩
    | i + 2 =>
      have h_r' : ((i+1= 0) ∨ option_r r (b :: c :: tail)[(i+1)-1]? k) ∧ (option_r r k (b :: c :: tail)[(i+1)+1]?) := by
        simp at h_r
        simp[h_r]
      have ih := monotone_set_monotone r (monotone_tail_monotone h_ord) k (i+1) h_r'
      repeat rw[List.set]
      rw[List.set] at ih
      rw[IsMonotone]
      exact⟨h_ord.left, ih⟩

theorem wkinc_set_wkinc (h_ord : IsWeakInc list) (k i : Nat)
  (h_le : ((i=0) ∨ (op_le list[i-1]? k)) ∧ (op_le k list[i+1]?)) :
  IsWeakInc (list.set i k) :=
  monotone_set_monotone (· ≤ ·) h_ord k i h_le

theorem wkdec_set_wkdec (h_ord : IsWeakDec list) (k i : Nat)
  (h_ge : ((i=0) ∨ (op_ge list[i-1]? k)) ∧ (op_ge k list[i+1]?)) :
  IsWeakDec (list.set i k) :=
  monotone_set_monotone (· ≥ ·) h_ord k i h_ge

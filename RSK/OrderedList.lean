
set_option relaxedAutoImplicit true

def op_lt (a b : Option Nat) :=
  match a, b with
  | some a, some b => a < b
  | _, _ => True

theorem op_lt_some : op_lt (some a) (some b) = (a < b) := by rfl

theorem op_lt_none_l : op_lt (none) (b) := by simp only [op_lt.eq_def]

theorem op_lt_none_r : op_lt (a) (none) := by simp only [op_lt.eq_def]

def op_le (a b : Option Nat) :=
  match a, b with
  | some a, some b => a ≤ b
  | _, _ => True

theorem op_le_some : op_le (some a) (some b) = (a ≤ b) := by rfl

theorem op_le_none_l : op_le (none) (b) := by simp only [op_le.eq_def]

theorem op_le_none_r : op_le (a) (none) := by simp only [op_le.eq_def]

def IsOrderedList (list : List Nat) : Prop :=
  match list with
  | [] => True
  | _ :: [] => True
  | a :: b :: tail => a ≤ b ∧ IsOrderedList (b :: tail)

theorem ord_tail_ord (h : IsOrderedList (a :: tail)) : IsOrderedList (tail) := by
  cases tail with
  | nil => exact h
  | cons b tail2 =>
    exact h.right

def IsOrderedList2 (list : List Nat) : Prop :=
  ∀i j : Nat, (i_lt_j : i < j) → (j_le_l : j < list.length) → list[i]'(Nat.lt_trans i_lt_j j_le_l) ≤ list[j]'j_le_l

theorem ord2_tail_ord2 (h_ord : IsOrderedList2 (a :: tail)) : IsOrderedList2 (tail) := by
  intro i j i_lt_j j_le_l
  have i_lt_j_succ := Nat.add_lt_add_right i_lt_j 1
  have j_le_l_succ : j + 1 < (a :: tail).length := Nat.add_lt_of_lt_sub j_le_l
  have hi := h_ord (i+1) (j+1) i_lt_j_succ j_le_l_succ
  have h₁ := List.getElem_cons_succ a (tail) i (Nat.lt_trans i_lt_j_succ j_le_l_succ)
  have h₂ := List.getElem_cons_succ a (tail) j j_le_l_succ
  rw[←h₁, ←h₂]
  exact hi

theorem ord_ord {list : List Nat} :
  IsOrderedList list ↔
  ∀i j : Nat, (i_lt_j : i < j) → (j_le_l : j < list.length) → list[i]'(Nat.lt_trans i_lt_j j_le_l) ≤ list[j]'j_le_l := by
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
          have h_ord_tail := ord_tail_ord h_ord
          have hi := ord_ord.mp h_ord_tail
          have k_lt_l := Nat.succ_lt_succ_iff.mp j_le_l
          have hi₂ := hi 0 (k+1) (Nat.zero_lt_succ k) k_lt_l
          have h₁ : (b :: tail)[k+1] = (a :: b :: tail)[k+2] := List.getElem_cons_succ b tail k k_lt_l
          have h₂ : (b :: tail)[0] = (a :: b :: tail)[1] := List.getElem_cons_succ a (b::tail) 0 (Nat.lt_of_le_of_lt i_lt_j j_le_l)
          rw[h₂] at hi₂
          rw [←h₁]
          exact Nat.le_trans h_ord.left hi₂
      | k + 1 =>
        match j with
        | 0 => contradiction
        | q + 1 =>
          have h_ord_tail := ord_tail_ord h_ord
          have hi := ord_ord.mp h_ord_tail
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
      have h_ord_sub := ord2_tail_ord2 h_ord
      have hi := ord_ord.mpr h_ord_sub
      have a_le_b : a ≤ b := h_ord 0 1 Nat.one_pos (Nat.one_lt_succ_succ tail.length)
      rw[IsOrderedList]
      exact ⟨a_le_b, hi⟩

theorem ord_some_ord (h_ord : IsOrderedList list) :
  ∀ (i j : Nat) (_ : i < j), op_le list[i]? list[j]? := by
  intro i j h_i_lt_j
  have h_ord2 := ord_ord.mp h_ord
  if hj : j < list.length then
    have h_ord2_i_j := h_ord2 i j h_i_lt_j hj
    rw[←op_le_some] at h_ord2_i_j
    repeat rw[←List.getElem?_eq_getElem] at h_ord2_i_j
    exact h_ord2_i_j
  else
    have hlist_j_none : list[j]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hj)
    rw[hlist_j_none]
    exact op_le_none_r

theorem ord_next_ord (h_ord : IsOrderedList list) :
  ∀ i : Nat, (op_le list[i]? list[i+1]?) := by
  have h_ord2 := ord_ord.mp h_ord
  intro i
  if hi : i ≥ list.length - 1 then
    have hsucc_i : i + 1 ≥ list.length := Nat.le_add_of_sub_le hi
    have list_succ_i_none : list[i + 1]? = none := getElem?_neg list (i+1) (Nat.not_lt.mpr hsucc_i)
    simp[list_succ_i_none, op_le]
  else
    have h_i_lt_si : i < i + 1 := Nat.lt_add_one i
    have h_si_lt_l : i + 1 < list.length := by omega
    have h_i_lt_l : i < list.length := Nat.lt_trans h_i_lt_si h_si_lt_l
    have hl := h_ord2 i (i+1) h_i_lt_si h_si_lt_l
    rw[op_le.eq_def]
    rw[List.getElem?_eq_getElem h_i_lt_l]
    rw[List.getElem?_eq_getElem h_si_lt_l]
    simp only [hl]

theorem ord_next_both_ord (h_ord : IsOrderedList list) :
  ∀ i : Nat, (op_le list[i-1]? list[i]?) ∧ (op_le list[i]? list[i+1]?) := by
  intro i
  constructor
  · match i with
    | 0 =>
      match list with
      | [] => trivial
      | a :: tail => simp [op_le]
    | j + 1 =>
      rw [Nat.add_one_sub_one]
      exact ord_next_ord h_ord j
  · exact ord_next_ord h_ord i

theorem ord_front_ord (h : IsOrderedList list) : IsOrderedList list.dropLast := by
  match list with
  | [] => simp[IsOrderedList]
  | a :: [] => simp[IsOrderedList]
  | a :: b :: [] => simp[IsOrderedList]
  | a :: b :: c :: tail =>
    have ih₂ := ord_front_ord (ord_tail_ord h)
    exact And.imp_right (fun a ↦ ih₂) h

theorem ord_append_ord (h_ord : IsOrderedList list) (n : Nat) (h_lt : list.getLast? ≤ n) :
  IsOrderedList (list ++ [n]) := by
  match h_list : list with
  | [] => simp[IsOrderedList]
  | a :: [] =>
    simp only [List.getLast?_singleton] at h_lt
    simp only [List.cons_append, List.nil_append, IsOrderedList, and_true, ge_iff_le]
    exact h_lt
  | a :: b :: tail2 =>
    have h_lt₂ : (b :: tail2).getLast? ≤ n := by
      exact le_of_eq_of_le rfl h_lt
    have hi := ord_append_ord (ord_tail_ord h_ord) n h_lt₂
    simp only [List.cons_append, IsOrderedList]
    constructor
    · exact h_ord.left
    · exact hi

theorem ord_ins_ord (h_ord : IsOrderedList list) (k i : Nat)
  (h_le : ((i=0) ∨ (op_le list[i-1]? k)) ∧ (op_le k list[i+1]?)) :
  IsOrderedList (list.set i k) := by
  match list with
  | [] => trivial
  | a :: [] =>
    match i with
    | 0 => trivial
    | i+1 => trivial
  | a :: b :: [] =>
    match i with
    | 0 =>
      have hkb : k ≤ b := by
        simp [op_le] at h_le
        exact h_le
      trivial
    | 1 =>
      have hak : a ≤ k := by
        simp [op_le] at h_le
        exact h_le
      trivial
    | i + 2 =>
      simp only [List.set_cons_succ, List.set_nil]
      exact h_ord
  | a :: b :: c :: tail =>
    match i with
    | 0 =>
      rw[List.set]
      simp [op_le] at h_le
      exact ⟨h_le, ord_tail_ord h_ord⟩
    | 1 =>
      repeat rw[List.set]
      simp [op_le] at h_le
      rw[IsOrderedList]
      rw[IsOrderedList]
      rw[←and_assoc]
      exact ⟨h_le, ord_tail_ord (ord_tail_ord h_ord)⟩
    | i + 2 =>
      have op_le' : ((i+1= 0) ∨ op_le (b :: c :: tail)[(i+1)-1]? k) ∧ (op_le k (b :: c :: tail)[(i+1)+1]?) := by
        simp at h_le
        simp[h_le]
      have ih := ord_ins_ord (ord_tail_ord h_ord) k (i+1) op_le'
      repeat rw[List.set]
      rw[List.set] at ih
      rw[IsOrderedList]
      exact⟨h_ord.left, ih⟩

theorem ord_front_le_last (h_ord : IsOrderedList (a::tail)) : a ≤ (a::tail).getLast (List.cons_ne_nil a tail) := by
  match tail with
  | [] =>
    rw [List.getLast]
    exact Nat.le_refl a
  | b :: tail =>
    rw [List.getLast]
    exact Nat.le_trans h_ord.left (ord_front_le_last (ord_tail_ord h_ord))

theorem ord_last_ge (h: IsOrderedList (a :: tail)) : a ≤ (a::tail).getLast (List.cons_ne_nil a tail) := by
  cases tail with
  | nil => simp
  | cons b tail =>
    have hi := ord_last_ge (ord_tail_ord h)
    grind[h.left]

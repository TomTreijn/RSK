
set_option relaxedAutoImplicit true

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

def ord_ord (list : List Nat) : IsOrderedList list ↔ IsOrderedList2 list := by
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
          have hi := (ord_ord (b::tail)).mp h_ord_tail
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
          have hi := (ord_ord (b::tail)).mp h_ord_tail
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
      have hi := (ord_ord (b::tail)).mpr h_ord_sub
      have a_le_b : a ≤ b := h_ord 0 1 Nat.one_pos (Nat.one_lt_succ_succ tail.length)
      rw[IsOrderedList]
      exact ⟨a_le_b, hi⟩

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


theorem ord_last_ge (h: IsOrderedList (a :: tail)) : a ≤ (a::tail).getLast (List.cons_ne_nil a tail) := by
  cases tail with
  | nil => simp
  | cons b tail =>
    have hi := ord_last_ge (ord_tail_ord h)
    grind[h.left]

theorem drop_last_lt (list : List Nat) (h_notnil : list ≠ []) : list.dropLast.length < list.length := by
  match list with
  | [] => contradiction
  | a :: [] => simp
  | a :: b :: tail =>
    have ih := drop_last_lt (b :: tail) (by exact List.cons_ne_nil b tail)
    rw[List.dropLast, List.length, List.length]
    · omega
    · intro h
      contradiction

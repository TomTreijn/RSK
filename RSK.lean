import Mathlib.Logic.Function.Basic
import Mathlib.Data.SetLike.Basic
import RSK.Basic

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

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

theorem ord_last_ge (h: IsOrderedList (a :: tail)) : a ≤ (a::tail).getLast (by exact List.cons_ne_nil a tail) := by
  cases tail with
  | nil => simp
  | cons b tail =>
    have hi := ord_last_ge (ord_tail_ord h)
    grind[h.left]

structure OrderedList where
  l : List Nat
  lord : IsOrderedList l

def bmpshft_row (row : List Nat) (n : Nat) : List Nat × Option Nat :=
  match row with
  | .nil => ([n], none)
  | a :: tail =>
    if n < a then
      (n :: tail, some a)
    else
      let (btail, bumped) := bmpshft_row tail n
      (a :: btail, bumped)


theorem ord_bmpshft_row (hlist_ord : IsOrderedList list) (n : Nat)
  : IsOrderedList (bmpshft_row list n).1 := by
  cases list with
  | nil => exact hlist_ord
  | cons a tail =>
    cases tail with
    | nil =>
      grind[IsOrderedList, bmpshft_row]
    | cons b tail2 =>
      have tail_n_ord := ord_bmpshft_row (ord_tail_ord hlist_ord) n
      grind[bmpshft_row, IsOrderedList]


-- def bmpshft_row (row : OrderedList) (n : Nat)
--  : OrderedList × Option Nat :=
--   ⟨⟨(bmpshft_row_h row.l n).fst, ord_bmpshft_row row.lord n⟩,
--    (bmpshft_row_h row.l n).snd⟩


theorem bmpshft_row_neq_nil (list : List Nat) (n : Nat)
  : (bmpshft_row list n).fst ≠ [] := by
  cases h: list with
  | nil => simp[bmpshft_row, bmpshft_row]
  | cons a tail => grind[bmpshft_row]


-- theorem max_bmpshft_row (row : List Nat) (h_ord : IsOrderedList row) (n : Nat)
--   : n ≤ (bmpshft_row ⟨row, h_ord⟩ n).fst.l.getLast (bmpshft_row_neq_nil ⟨row, h_ord⟩ n) := by
--   induction row with
--   | nil => simp[bmpshft_row, bmpshft_row_h]
--   | cons a tail ih =>
--     if hn_lq_a : n < a then
--       simp[bmpshft_row, bmpshft_row_h, hn_lq_a]
--       have h₂ := last_ge h_ord
--       grind
--     else
--       simp[bmpshft_row, bmpshft_row_h, hn_lq_a]
--       have htail_ord := ord_tail_ord h_ord
--       grind[bmpshft_row]

theorem bmpshft_row_bmp_gt (row : List Nat) (n : Nat) :
  match (bmpshft_row row n).2 with
  | none => true
  | some a => n < a := by
  induction row with
  | nil =>
    simp[bmpshft_row]
  | cons a tail ih =>
    if hn_lt_a : n < a then
      simp[bmpshft_row, hn_lt_a]
    else
      simp only [bmpshft_row, hn_lt_a, ↓reduceIte]
      simp only at ih
      exact ih


theorem bmpshft_row_fst_lt (row : List Nat) (n : Nat) :
  match (bmpshft_row row n).2 with
  | none => true
  | some a => ((bmpshft_row row n).1.head (bmpshft_row_neq_nil row n)) < a := by
  match h_row : row with
  | [] => simp[bmpshft_row]
  | head :: tail =>
    if hn_lt_a : n < head then
      simp[bmpshft_row, hn_lt_a]
    else
      have ha_lq_n : head ≤ n := by exact Nat.le_of_not_lt hn_lt_a
      simp only [bmpshft_row, hn_lt_a, ↓reduceIte, List.head_cons]
      have h₀ := bmpshft_row_bmp_gt tail n
      match h_tail : (bmpshft_row tail n).snd with
      | none => simp
      | some a =>
        rw [h_tail] at h₀
        exact Nat.lt_of_le_of_lt ha_lq_n h₀

theorem dropLastSmall (list : List Nat) (h_notnil : list ≠ []) : list.dropLast.length < list.length := by
  match list with
  | [] => contradiction
  | a :: [] => simp
  | a :: b :: tail =>
    have ih := dropLastSmall (b :: tail) (by exact List.cons_ne_nil b tail)
    rw[List.dropLast, List.length, List.length]
    · omega
    · intro h
      contradiction


def bmpshft_inv (h_ord : IsOrderedList row) (a : Option Nat) (h_notnil : row ≠ []) (h_leq : nat_lt_option (row.head h_notnil) a) : List Nat × Nat :=
  match a with
  | none => ⟨row.dropLast, row.getLast h_notnil⟩
  | some a =>
    if hn_lt_a : row.getLast h_notnil < a then
      ⟨row.dropLast ++ [a], row.getLast h_notnil⟩
    else
      have h_ord₂ := ord_front_ord h_ord
      have h_notnil₂ : row.dropLast ≠ [] := by
        match h_row : row with
        | [] => exact h_notnil.elim
        | n :: [] =>
          rw [nat_lt_option, List.head] at h_leq
          rw [Not, List.getLast] at hn_lt_a
          contradiction
        | b :: c :: tail =>
          exact List.getLast?_isSome.mp rfl
      have h_leq₂ : nat_lt_option (row.dropLast.head h_notnil₂) a := by grind
      have ⟨nrow, n⟩ := bmpshft_inv h_ord₂ a h_notnil₂ h_leq₂
      ⟨nrow ++ [row.getLast h_notnil], n⟩
  termination_by row.length decreasing_by
    exact dropLastSmall row h_notnil

theorem helper₁ (h_ord : IsOrderedList row) : row.dropLast.getLast? ≤ row.getLast? := by
  match h_row: row with
  | [] => simp
  | a :: [] => simp
  | a :: b :: [] => exact h_ord.left
  | a :: b :: c :: tail =>
    have hi := helper₁ (ord_tail_ord h_ord)
    grind


theorem ord_bmpshft_inv (h_ord : IsOrderedList row) (a : Option Nat) (h_notnil : row ≠ []) (h_leq : (row.head h_notnil) < a) :
  IsOrderedList (bmpshft_inv h_ord a h_notnil h_leq).1 := by
  match a with
  | none =>
    rw[bmpshft_inv]
    simp[ord_front_ord h_ord]
  | some a =>
    if hn_lt_a : row.getLast h_notnil < a then
      rw[bmpshft_inv]
      simp[hn_lt_a]
      exact ord_append_ord (ord_front_ord h_ord) a (by
        have h₀ := helper₁ h_ord

        rw [option_lq_nat.eq_def]


      sorry)
    else





def bmpshft (syt : Grid) (n : Nat) : Grid × Nat :=
  match syt with
  | .nil => ([[n]], 0)
  | row :: tail =>
    let (new_row, bumped) := bmpshft_row row n
    match bumped with
    | none => (new_row :: tail, 0)
    | some a =>
      let (new_grid, row_bumped) := bmpshft tail a
      (new_row :: new_grid, row_bumped + 1)

#eval bmpshft [[1, 3, 4], [5, 6]] 2

def RSK (σ : List Nat) : Grid × Grid :=
  match σ with
  | .nil => ([], [])
  | n :: σ_tail =>
    let (P, Q) := RSK σ_tail
    let (P_new, i) := bmpshft P n
    let trash := Q.flatten.length
    let Q_new := match Q[i]?  with
      | none => Q ++ [[trash]]
      | some row => Q.set i (row ++ [trash])
    (P_new, Q_new)

#eval RSK [2, 7, 1, 8, 11, 10, 4, 5, 0, 9, 3, 6].reverse =
  ([[0, 3, 5, 6],
    [1, 4, 8, 9],
    [2, 7, 10],
    [11]],
   [[0, 1, 3, 4],
    [2, 5, 7, 9],
    [6, 10, 11],
    [8]])

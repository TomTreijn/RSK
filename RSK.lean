import Mathlib.Logic.Function.Basic
import Mathlib.Data.SetLike.Basic
import RSK.Basic
import RSK.OrderedList

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

-- insert into a row
def bmpshft_row (row : List Nat) (k : Nat) : List Nat × Option Nat :=
  match row with
  | [] => ([k], none)
  | a :: tail =>
    if k < a then
      (k :: tail, some a)
    else
      let (btail, bumped) := bmpshft_row tail k
      (a :: btail, bumped)

-- insertion into a row is ordered
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

-- row is not nil after insertion
theorem bmpshft_row_neq_nil (list : List Nat) (n : Nat)
  : (bmpshft_row list n).fst ≠ [] := by
  cases h: list with
  | nil => simp[bmpshft_row, bmpshft_row]
  | cons a tail => grind[bmpshft_row]

-- The bumped out k' is larger than the inserted number
theorem bmpshft_row_bmp_gt (row : List Nat) (n : Nat) :
  op_lt (some n) (bmpshft_row row n).2 := by
  induction row with
  | nil =>
    simp[bmpshft_row, op_lt]
  | cons a tail ih =>
    if hn_lt_a : n < a then
      simp[bmpshft_row, op_lt, hn_lt_a]
    else
      simp only [bmpshft_row, hn_lt_a, ↓reduceIte]
      simp only at ih
      exact ih

-- The bumped out k' is larger than the first number in the row
theorem bmpshft_row_fst_lt (row : List Nat) (n : Nat) :
  op_lt ((bmpshft_row row n).1.head (bmpshft_row_neq_nil row n)) (bmpshft_row row n).2 := by
  match h_row : row with
  | [] => trivial
  | head :: tail =>
    if hn_lt_a : n < head then
      simp[op_lt, bmpshft_row, hn_lt_a]
    else
      have ha_lq_n : head ≤ n := by exact Nat.le_of_not_lt hn_lt_a
      simp only [bmpshft_row, hn_lt_a, ↓reduceIte, List.head_cons]
      have h₀ := bmpshft_row_bmp_gt tail n
      match h_tail : (bmpshft_row tail n).snd with
      | none => trivial
      | some a =>
        rw [h_tail] at h₀
        exact Nat.lt_of_le_of_lt ha_lq_n h₀

theorem helper₁ (h_ord : IsOrderedList row) : row.dropLast.getLast? ≤ row.getLast? := by
  match h_row: row with
  | [] => trivial
  | a :: [] => trivial
  | a :: b :: [] => exact h_ord.left
  | a :: b :: c :: tail =>
    have hi := helper₁ (ord_tail_ord h_ord)
    grind

structure bmpshft_row_in where
  row : List Nat
  h_ord : IsOrderedList row
  k : Nat

structure bmpshft_row_out where
  row : List Nat
  h_ord : IsOrderedList row
  k' : Option Nat
  h_notnil : row ≠ []
  h_leq : op_lt (row.head h_notnil) k'

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

-- An inversion of bmpshft
def bmpshft_row_inv (h_ord : IsOrderedList row) (h_notnil : row ≠ []) (k' : Option Nat) (h_leq : op_lt (row.head h_notnil) k') : List Nat × Nat :=
  let last := row.getLast h_notnil
  match k' with
  -- If noting was bumped out, the last element is k
  | none => ⟨row.dropLast, last⟩
  | some k' =>
    if hl_lt_k' : last < k' then
      -- If the last number is smaller than k', it must be k
      ⟨row.dropLast ++ [k'], last⟩
    else
      -- Now for the induction part.
      -- We first obtain the theorems for induction
      have h_ord₂ := ord_front_ord h_ord
      have h_notnil₂ : row.dropLast ≠ [] := by
        dsimp only [last] at hl_lt_k'
        match h_row : row with
        | [] => exact h_notnil.elim
        | n :: [] =>
          contradiction
        | b :: c :: tail =>
          exact List.getLast?_isSome.mp rfl
      have h_leq₂ : op_lt (row.dropLast.head h_notnil₂) k' := by
        grind
      have ⟨nrow, k⟩ := bmpshft_row_inv h_ord₂ h_notnil₂ k' h_leq₂
      ⟨nrow ++ [last], k⟩
  termination_by row.length decreasing_by
    exact drop_last_lt row h_notnil

-- If we reinsert an element k'. The last element of the new list can become no bigger than k'
def bmpshft_row_inv_last (h_ord : IsOrderedList row) (h_notnil : row ≠ []) (k' : Nat) (h_leq : op_lt (row.head h_notnil) k') :
  (bmpshft_row_inv h_ord h_notnil (some k') h_leq).fst.getLast? ≤ max (row.getLast h_notnil) k' := by
  let last := row.getLast h_notnil
  if hl_lt_k' : last < k' then
    rw[bmpshft_row_inv.eq_def]
    simp[hl_lt_k', last]
  else
    rw[bmpshft_row_inv.eq_def]
    simp[hl_lt_k', last]

theorem option_le_trans {a b c : Option Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  match a, b, c with
  | none, _, _ => exact Option.none_le
  | some a, none, _ => contradiction
  | some a, some b, none => contradiction
  | some a, some b, some c =>
    refine Option.some_le_some.mpr ?_
    exact Nat.le_trans h₁ h₂

theorem ord_bmpshft_row_inv (h_ord : IsOrderedList row) (h_notnil : row ≠ []) (k' : Option Nat) (h_leq : op_lt (row.head h_notnil) k') :
  IsOrderedList (bmpshft_row_inv h_ord h_notnil k' h_leq).1 := by
  let last := row.getLast h_notnil
  match k' with
  | none =>
    rw[bmpshft_row_inv.eq_def]
    simp[ord_front_ord h_ord]
  | some k' =>
    if hl_lt_k' : last < k' then
      rw[bmpshft_row_inv]
      simp only [hl_lt_k', ↓reduceDIte, last]
      dsimp only [last] at hl_lt_k'
      exact ord_append_ord (ord_front_ord h_ord) k' (by grind[helper₁])
    else
      rw[bmpshft_row_inv]
      simp only [hl_lt_k', ↓reduceDIte, last]
      apply ord_append_ord
      · apply ord_bmpshft_row_inv
      · -- Note that this is a copy of the code in bmpshft_row_inv and should be refactored.
        have h_ord₂ := ord_front_ord h_ord
        have h_notnil₂ : row.dropLast ≠ [] := by
          dsimp only [last] at hl_lt_k'
          match h_row : row with
          | [] => exact h_notnil.elim
          | n :: [] =>
            contradiction
          | b :: c :: tail =>
            exact List.getLast?_isSome.mp rfl
        have h_leq₂ : op_lt (row.dropLast.head h_notnil₂) k' := by
          grind
        apply option_le_trans
        · exact bmpshft_row_inv_last h_ord₂ h_notnil₂ k' h_leq₂
        · refine Option.some_le_some.mpr ?_
          refine Nat.max_le_of_le_of_le ?_ ?_
          · have h₁ := helper₁ h_ord
            grind
          · grind
  termination_by row.length decreasing_by
    exact drop_last_lt row h_notnil

def bmpshft_row' (var : bmpshft_row_in) : bmpshft_row_out :=
  let ⟨row, h_ord, k⟩ := var
  ⟨(bmpshft_row row k).fst,
    ord_bmpshft_row h_ord k,
    (bmpshft_row row k).snd,
    bmpshft_row_neq_nil row k,
    bmpshft_row_fst_lt row k⟩

def bmpshft_row_inv' (var : bmpshft_row_out) : bmpshft_row_in :=
  let ⟨_, h_ord, h_notnil, k', h_leq⟩ := var
  ⟨(bmpshft_row_inv h_ord k' h_notnil h_leq).fst,
   ord_bmpshft_row_inv  h_ord k' h_notnil h_leq,
   (bmpshft_row_inv h_ord k' h_notnil h_leq).snd⟩

theorem bmpshft_row_bi : Function.Bijective bmpshft_row' := by
  apply Function.bijective_iff_has_inverse.mpr
  have is_inv : Function.LeftInverse bmpshft_row_inv' bmpshft_row' ∧
        Function.RightInverse bmpshft_row_inv' bmpshft_row' := by
    constructor
    · refine Function.leftInverse_iff_comp.mpr ?_
      refine Eq.symm (funext ?_)
      intro var
      let ⟨row, h_ord, k⟩ := var
      dsimp only [id_eq, Function.comp_apply]
      rw[bmpshft_row']
      simp[bmpshft_row, bmpshft_row_inv', bmpshft_row_inv]
      match row with
      | [] => simp[bmpshft_row, bmpshft_row_inv', bmpshft_row_inv]
      | a :: [] => grind[bmpshft_row, bmpshft_row_inv', bmpshft_row_inv]
      | a :: b :: tail =>
        if hk_lt_a : k < a then
          simp[bmpshft_row, bmpshft_row_inv', bmpshft_row_inv]
          simp[hk_lt_a]
          rw[bmpshft_row_inv]
          simp[hk_lt_a]
          have ha_le_last := Nat.le_trans h_ord.left (ord_front_le_last (ord_tail_ord h_ord))
          have hlast_lq_a := Nat.not_lt.mpr ha_le_last
          simp[hlast_lq_a]






  exact Exists.intro bmpshft_row_inv' is_inv

def bmpshft (syt : Grid) (k : Nat) : Grid × Nat :=
  match syt with
  | .nil => ([[k]], 0)
  | row :: tail =>
    let (new_row, bumped) := bmpshft_row row k
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

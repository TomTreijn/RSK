import Mathlib.Combinatorics.Young.SemistandardTableau
import RSK.Basic

abbrev Grid := List (List Nat)


def row_strict (μ : YoungDiagram) (entry : ℕ → ℕ → ℕ) : Prop :=
  ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 < entry i j2


def bump_and_shift_row (row : List Nat) (n : Nat) : List Nat × Option Nat :=
  match row with
  | .nil => ([n], none)
  | a :: tail =>
    if n < a then
      (n :: tail, some a)
    else
      let (btail, bumped) := bump_and_shift_row tail n
      (a :: btail, bumped)


def bump_and_shift (syt : Grid) (n : Nat) : Grid × Nat :=
  match syt with
  | .nil => ([[n]], 0)
  | row :: tail =>
    let (new_row, bumped) := bump_and_shift_row row n
    match bumped with
    | none => (new_row :: tail, 0)
    | some a =>
      let (new_grid, row_bumped) := bump_and_shift tail a
      (new_row :: new_grid, row_bumped + 1)

#eval bump_and_shift [[1, 3, 4], [5, 6]] 2

def RSK (σ : List Nat) : Grid × Grid :=
  match σ with
  | .nil => ([], [])
  | n :: σ_tail =>
    let (P, Q) := RSK σ_tail
    let (P_new, i) := bump_and_shift P n
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

import Mathlib.Logic.Function.Basic
import Mathlib.Data.SetLike.Basic
import RSK.Basic
import Mathlib.Tactic
import RSK.OrderedList

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

structure bmpshft_row_in where
  row : List Nat
  h_ord : IsOrderedList row
  k : Nat

theorem bmpshft_row_in_eq {in₁ in₂ : bmpshft_row_in} : (in₁.row = in₂.row ∧ in₁.k = in₂.k) ↔ in₁ = in₂ := by
  grind[bmpshft_row_in]

structure bmpshft_row_out where
  row : List Nat
  h_ord : IsOrderedList row
  k' : Option Nat
  h_notnil : row ≠ []
  h_leq : op_lt (row.head h_notnil) k'



-- insert into a row
def bmpshft_row (var : bmpshft_row_in) : bmpshft_row_out :=
  let ⟨row, h_ord, k⟩ := var
  let f_gt_k := fun (j : Nat) ↦ j > k
  let i := row.findIdx? (· > k)
  have i_eq : i = row.findIdx? (· > k) := by rfl
  match hi : i with
  | none =>
    -- Add to the end
    let row' := row ++ [k]
    let k' := none
    have h_ord' : IsOrderedList row' := by
      dsimp only [row']
      apply ord_append_ord
      · exact h_ord
      · match hrl : row.getLast? with
        | none => exact Option.none_le
        | some a =>
          have left_le := List.findIdx?_eq_none_iff.mp (i_eq.symm)
          have ha_in : a ∈ row := List.mem_of_getLast? hrl
          have ha_leq := left_le a ha_in
          rw[decide_eq_false_iff_not, Not] at ha_leq
          exact Option.some_le_some.mpr (Nat.le_of_not_lt ha_leq)
    have h_notnil' : row' ≠ [] := List.concat_ne_nil k row
    have h_leq' : op_lt (row'.head h_notnil') k' := by
      dsimp only [op_lt, k']
    ⟨row', h_ord', k', h_notnil', h_leq'⟩
  | some j =>
    have h_eq_some := List.findIdx?_eq_some_iff_getElem.mp hi
    have h_j_lt_len := h_eq_some.choose
    let row' := row.set j k
    let k' := row[j]
    have h_notnil : row ≠ [] := by
      by_contra hP
      have h₀ : [].findIdx? (f_gt_k: ℕ → Bool) = none := List.findIdx?_nil
      dsimp only [i] at hi
      rw [←hP] at h₀
      rw [hi] at h₀
      contradiction
    have h_len_lt_zero : 0 < row.length := List.length_pos_iff.mpr h_notnil
    have h_notnil' : row' ≠ [] := by
      dsimp [row']
      rw [←ne_eq]
      have row'len : (row.set (↑j) k).length = row.length := List.length_set
      have row'len_not_zero : (row.set (↑j) k).length > 0 := by rw[row'len]; exact h_len_lt_zero
      exact List.ne_nil_of_length_pos row'len_not_zero
    have hk' : k' = row[j] := by rfl
    have h_ord' : IsOrderedList row' := by
      rcases h_eq_some with ⟨_, hk_lt_k', h_left_lt_k⟩
      dsimp only [row']
      apply ord_ins_ord
      · exact h_ord
      · dsimp only [i] at hi
        simp only [gt_iff_lt, decide_eq_true_eq] at hk_lt_k'
        rw [←hk'] at hk_lt_k'
        constructor
        · if hj : j = 0 then
            exact Or.inl hj
          else
            apply Or.inr
            have hsubj_lt_j : j-1 < j := Nat.sub_one_lt hj
            rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt h_j_lt_len)]
            simp only [op_le, ge_iff_le]
            have hleft_one_lt_k := h_left_lt_k (j-1) hsubj_lt_j
            rw[Not, decide_eq_true_eq] at hleft_one_lt_k
            exact Nat.le_of_not_lt hleft_one_lt_k
        · if hsuccj : j + 1 ≥ row.length then
            rw [List.getElem?_eq_none hsuccj]
            exact op_le_none_r
          else
            apply Nat.lt_of_not_le at hsuccj
            rw[List.getElem?_eq_getElem hsuccj]
            rw[op_le_some]
            have hrow_j_lt_succj : row[j] ≤ row[j+1] := ord_ord.mp h_ord j (j+1) (lt_add_one j) hsuccj
            rw[←hk'] at hrow_j_lt_succj
            sorry
    have h_leq' : op_lt (row'.head h_notnil') k' := sorry
    ⟨row', h_ord', k', h_notnil', h_leq'⟩

#eval! bmpshft_row ⟨[1, 2, 4, 5], (by simp[IsOrderedList]), 3⟩
#eval! bmpshft_row ⟨[1, 2, 4, 5], (by simp[IsOrderedList]), 6⟩

def bmpshft_row_inv (var : bmpshft_row_out) : bmpshft_row_in :=
  let ⟨row', h_ord', k', h_notnil', h_leq'⟩ := var
  match k' with
  | none => ⟨row'.dropLast, ord_front_ord h_ord', row'.getLast h_notnil'⟩
  | some k' =>
    let i := row'.findIdx (· > k') - 1
    have hi : i = row'.findIdx (· > k') - 1 := by rfl
    have hi_lt_len : i < row'.length := by
      grind
    let row := row'.set i k'
    let k := row'[i]
    have h_ord : IsOrderedList row := by
      apply ord_ins_ord
      · exact h_ord'
      · sorry
    ⟨row, h_ord, k⟩

theorem bmpshft_row_bi : Function.Bijective bmpshft_row := by
  apply Function.bijective_iff_has_inverse.mpr
  have is_inv : Function.LeftInverse bmpshft_row_inv bmpshft_row ∧
        Function.RightInverse bmpshft_row_inv bmpshft_row := by
    constructor
    · refine Function.leftInverse_iff_comp.mpr ?_
      refine Eq.symm (funext ?_)
      intro var
      let ⟨row, h_ord, k⟩ := var
      dsimp only [id_eq, Function.comp_apply]
      rw[bmpshft_row]
      split
      · case h_1 hi =>
          rw[bmpshft_row_inv]
          grind
      · case h_2 j hi =>
          rw[bmpshft_row_inv]
          have h_eq_some := List.findIdx?_eq_some_iff_getElem.mp hi
          have h_j_lt_len := h_eq_some.choose
          have equality : (List.findIdx (fun x ↦ decide (x > row[j])) (row.set j k) - 1) = k := by
            sorry
          simp_rw[equality]
          sorry

    · refine Function.leftInverse_iff_comp.mpr ?_
      refine Eq.symm (funext ?_)
      intro var
      let ⟨row', h_ord', k', h_notnil', h_leq'⟩ := var
      dsimp only [id_eq, Function.comp_apply]
      rw[bmpshft_row_inv.eq_def]
      simp only [gt_iff_lt]
      split
      · case h_1 =>
          -- k' = none. So proof that k is larger than all other numbers in row.
          rw [bmpshft_row]
          sorry
      · case h_2 =>
          rw [bmpshft_row]
          sorry


  exact ⟨bmpshft_row_inv, is_inv⟩


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

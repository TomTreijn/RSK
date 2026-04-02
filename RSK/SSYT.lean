import RSK.OrderedList
import Mathlib.Tactic

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)


def row_comp (row₁ row₂ : List Nat) : Prop :=
  ∃(h_diagram : row₂.length ≤ row₁.length), ∀(i : Nat) (hi : i < row₂.length), row₁[i] < row₂[i]

theorem row_comp_trans (h₁ : row_comp row₁ row₂) (h₂ : row_comp row₂ row₃) :
  row_comp row₁ row₃ := by
  have ⟨h_diagram₁, h_inc₁⟩ := h₁
  have ⟨h_diagram₂, h_inc₂⟩ := h₂
  have h_diagram := Nat.le_trans h_diagram₂ h_diagram₁
  have h_inc : ∀(i : Nat) (hi : i < row₃.length), row₁[i] < row₃[i] := by
    intro i hi
    exact Nat.lt_trans (h_inc₁ i (Nat.lt_of_lt_of_le hi h_diagram₂)) (h_inc₂ i hi)
  exact ⟨h_diagram, h_inc⟩

def op_lst (a b : Option (List Nat)) := option_r (row_comp · ·) a b
theorem op_lst_some : op_lst (some a) (some b) = (row_comp a b) := by rfl
theorem op_lst_none_l : op_lst none a := option_r_left_none row_comp
theorem op_lst_none_r : op_lst a none := option_r_right_none row_comp

def IsRowInc (cells : Grid) := IsMonotone row_comp cells
def IsRowInc2 (cells : Grid) := IsMonotone2 row_comp cells

def rowinc_rowinc2 {cells : Grid} : IsRowInc cells ↔ IsRowInc2 cells
 := monotone_monotone2 row_comp row_comp_trans

theorem rowinc_append_rowinc (h_ord : IsRowInc list) (n : List Nat)
  (h_le : op_lst list.getLast? n) : IsRowInc (list ++ [n]) := monotone_append_monotone h_ord n h_le

theorem rowinc_set_rowinc (h_ord : IsRowInc cells) (k : List Nat) (i : Nat)
  (h_le : ((i = 0) ∨ (op_lst cells[i - 1]? k)) ∧ (op_lst k cells[i + 1]?)) :
  IsRowInc (cells.set i k) :=
  monotone_set_monotone row_comp h_ord k i h_le

theorem rowinc_front_rowinc (h : IsRowInc cells) : IsRowInc cells.dropLast :=
  montone_front_monotone row_comp h

def IsSSYT (cells : Grid) : Prop :=
  (∀ (j : Nat) (h : j < cells.length), IsWeakInc cells[j] ∧ cells[j] ≠ []) ∧
  IsRowInc cells

theorem diagram_decreasing (hSSYT : IsSSYT cells)
  (j₁ j₂ : Nat) (hj₁_lt_j₂ : j₁ < j₂) (hj₂_lt_len : j₂ < cells.length) :
  cells[j₁].length ≥ cells[j₂].length := by
  have ⟨h_diagram, _⟩ := rowinc_rowinc2.mp hSSYT.right j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  exact h_diagram

theorem SSYT_col_increasing (hSSYT : IsSSYT cells)
  (i j₁ j₂ : Nat) (hj₁_lt_j₂ : j₁ < j₂)
  (hj₂_lt_len : j₂ < cells.length) (hi_lt_len : i < cells[j₂].length) :
  have := diagram_decreasing hSSYT j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  cells[j₁][i] < cells[j₂][i] := by
  have ⟨_, inc⟩ := rowinc_rowinc2.mp hSSYT.right j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  exact inc i hi_lt_len

theorem SSYT_append_row (hSSYT : IsSSYT cells) (k : Nat)
  (h_col_above :
    if hcells : cells.length = 0 then
      True
    else
      have iji : 0 < cells[cells.length - 1].length := by
        have := (hSSYT.left (cells.length - 1) (Nat.sub_one_lt hcells)).right
        exact List.length_pos_iff.mpr this
      cells[cells.length - 1][0] < k
  ) : IsSSYT (cells ++ [[k]]) := by
    constructor
    · intro j hj_le_len
      if hj : j = cells.length then
        rw[List.getElem_append_right (Nat.le_of_eq (Eq.symm hj))]
        rw[List.getElem_singleton]
        constructor
        · trivial
        · exact List.cons_ne_nil k []
      else
        rw [List.length_append, List.length_singleton] at hj_le_len
        have hj_lt_len : j < cells.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj_le_len) hj
        rw [List.getElem_append_left hj_lt_len]
        exact hSSYT.left j hj_lt_len
    · apply rowinc_append_rowinc hSSYT.right
      · match cells with
        | [] =>
          rw[List.getLast?_nil]
          exact op_lst_none_l
        | c :: cs =>
          rw[List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil c cs)]
          simp_rw[op_lst_some, row_comp, List.getLast_eq_getElem,
            List.length_singleton, Nat.lt_one_iff]
          have neq_nil := (hSSYT.left cs.length (Nat.lt_add_one cs.length)).right
          exact ⟨List.length_pos_iff.mpr neq_nil, by
            intro i hi
            simp_rw[hi]
            exact h_col_above
          ⟩

theorem SSYT_append (hSSYT : IsSSYT cells) (j : Nat) (k : Nat)
  (hj_lt_len : j < cells.length)
  (hst_dec : j = 0 ∨ cells[j].length < cells[j - 1].length)
  (h_row : IsWeakInc (cells[j] ++ [k]))
  (h_col_above :
    if hj : j = 0 then
      True
    else
      have := Or.resolve_left hst_dec hj
      have := Nat.sub_lt_of_lt hj_lt_len
      k > cells[j - 1][cells[j].length]
  ) :
  IsSSYT (cells.set j (cells[j] ++ [k])) := by
  rw[IsSSYT]
  constructor
  · intro j₂ hj₂_lt_len
    if hj_eq_j₂ : j = j₂ then
      simp_rw[←hj_eq_j₂, List.getElem_set_self]
      constructor
      · exact h_row
      · exact List.concat_ne_nil k cells[j]
    else
      rw[List.getElem_set_ne hj_eq_j₂]
      rw[List.length_set] at hj₂_lt_len
      exact hSSYT.left j₂ hj₂_lt_len
  · apply rowinc_set_rowinc hSSYT.right
    · constructor
      · if hj : j = 0 then
          simp_rw [hj, zero_tsub, true_or]
        else
          simp only [hj, false_or] at hst_dec
          simp only [hj, ↓reduceDIte] at h_col_above
          apply Or.intro_right
          rw[List.getElem?_eq_getElem, op_lst_some, row_comp]
          · simp_rw[List.length_append, List.length_singleton]
            have hdiagram := Order.add_one_le_iff.mpr hst_dec
            exact ⟨hdiagram, by
              intro i hi_lt_len
              if hi : i = cells[j].length then
                simp_rw[List.getElem_append_right (Nat.le_of_eq (Eq.symm hi)),
                  hi, List.getElem_singleton]
                exact h_col_above
              else
                have iji : i < cells[j].length := by omega
                rw[List.getElem_append_left iji]
                exact SSYT_col_increasing hSSYT i (j - 1) j (Nat.sub_one_lt hj) hj_lt_len iji
            ⟩
      · if hsuccj : cells.length = j + 1 then
          rw[List.getElem?_eq_none (Nat.le_of_eq hsuccj)]
          exact op_lst_none_r
        else
          have hsuccj_lt : j + 1 < cells.length := by omega
          rw[List.getElem?_eq_getElem hsuccj_lt, op_lst_some, row_comp]
          have len_dec := diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hsuccj_lt
          simp_rw[List.length_append, List.length_singleton]
          exact ⟨Nat.le_add_right_of_le len_dec, by
            intro i hi
            have i_lt : i < cells[j].length := Nat.lt_of_lt_of_le hi len_dec
            rw[List.getElem_append_left i_lt]
            exact SSYT_col_increasing hSSYT i j (j + 1) (lt_add_one j) hsuccj_lt hi
          ⟩

theorem SSYT_set (hSSYT : IsSSYT cells) (j i : Nat) (k : Nat)
  (hj_lt_len : j < cells.length)
  (hi_lt_len : i < cells[j].length)
  (h_row : IsWeakInc (cells[j].set i k))
  (h_col_above :
    if hj : j = 0 then
      True
    else
      have := Nat.sub_lt_of_lt hj_lt_len
      have subj_ge_j := diagram_decreasing
        hdiagram (j - 1) j (Nat.sub_one_lt hj) (Nat.lt_of_succ_le hj_lt_len)
      have := Nat.lt_of_lt_of_le hi_lt_len subj_ge_j
      k > cells[j - 1][i])
  (h_col_under :
    if hj : j + 1 < cells.length then
      if hi : i < cells[j + 1].length then
        k < cells[j + 1][i]
      else
        True
    else
      True
  ) : IsSSYT (cells.set j (cells[j].set i k)) := by
    constructor
    · intro j₂ hj₂_lt_len
      if hj : j = j₂ then
        simp_rw[←hj, List.getElem_set_self]
        constructor
        · exact h_row
        · have neq_nil := (hSSYT.left j hj_lt_len).right
          apply List.ne_nil_iff_length_pos.mpr
          rw[List.length_set]
          exact List.length_pos_iff.mpr neq_nil
      else
        rw[List.getElem_set_ne hj]
        rw[List.length_set] at hj₂_lt_len
        exact hSSYT.left j₂ hj₂_lt_len
    · apply rowinc_set_rowinc hSSYT.right
      · constructor
        · if hj : j = 0 then
            apply Or.intro_left
            exact hj
          else
            apply Or.intro_right
            simp_rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt hj_lt_len),
              op_lst_some, row_comp, List.length_set]
            have len_lt := diagram_decreasing hSSYT (j - 1) j (Nat.sub_one_lt hj) hj_lt_len
            exact ⟨len_lt, by
              intro i₂ hi₂_lt_len
              if hi₂_eq_i : i = i₂ then
                simp_rw[←hi₂_eq_i, List.getElem_set_self]
                simp only [hj, ↓reduceDIte] at h_col_above
                exact h_col_above
              else
                simp_rw[List.getElem_set_ne hi₂_eq_i]
                exact SSYT_col_increasing hSSYT i₂ (j - 1) j
                  (Nat.sub_one_lt hj) hj_lt_len hi₂_lt_len
            ⟩
        · if hsuccj : cells.length = j + 1 then
            rw[List.getElem?_eq_none (Nat.le_of_eq hsuccj)]
            exact op_lst_none_r
          else
            have hsuccj_lt_len : j + 1 < cells.length := by omega
            simp_rw[List.getElem?_eq_getElem hsuccj_lt_len, op_lst_some, row_comp, List.length_set]
            have len_lt := diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hsuccj_lt_len
            exact ⟨len_lt, by
              intro i₂ hi₂_lt_len
              if hi₂_eq_i : i = i₂ then
                rw[←hi₂_eq_i] at hi₂_lt_len
                simp only [hsuccj_lt_len, ↓reduceDIte, hi₂_lt_len] at h_col_under
                simp_rw[←hi₂_eq_i, List.getElem_set_self]
                exact h_col_under
              else
                rw[List.getElem_set_ne hi₂_eq_i]
                exact SSYT_col_increasing hSSYT i₂ j (j + 1) (lt_add_one j) hsuccj_lt_len hi₂_lt_len
            ⟩

theorem SSYT_remove (hSSYT : IsSSYT cells) (j : Nat)
  (hj_lt_len : j < cells.length)
  (hst_dec :
    if hsuccj_len : j + 1 < cells.length then
      cells[j].length > cells[j + 1].length
    else
      True
  ) :
  if cells[j].length > 1 then
    IsSSYT (cells.set j (cells[j].dropLast))
  else
    IsSSYT cells.dropLast := by
  split
  · case isTrue hj_len =>
      constructor
      · intro j₂ hj₂_lt_len
        if hj₂_eq_j : j = j₂ then
          simp_rw[←hj₂_eq_j, List.getElem_set_self]
          have left_j := hSSYT.left j hj_lt_len
          constructor
          · exact wkinc_front_wkinc left_j.left
          · apply List.ne_nil_iff_length_pos.mpr
            rw[List.length_dropLast]
            omega
        else
          rw[List.getElem_set_ne hj₂_eq_j]
          rw[List.length_set] at hj₂_lt_len
          exact hSSYT.left j₂ hj₂_lt_len
      · apply rowinc_set_rowinc hSSYT.right
        constructor
        · if hj : j = 0 then
            simp[hj]
          else
            apply Or.intro_right
            rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt hj_lt_len), op_lst_some, row_comp]
            simp_rw [List.length_dropLast]
            have hdiag := diagram_decreasing hSSYT (j - 1) j (Nat.sub_one_lt hj) hj_lt_len
            exact ⟨by omega, by
              intro i hi_lt_len
              rw[List.getElem_dropLast]
              have hcol_inc : cells[j - 1][i] < cells[j][i] :=
                SSYT_col_increasing hSSYT i (j - 1) j
                  (Nat.sub_one_lt hj) hj_lt_len (Nat.lt_of_lt_pred hi_lt_len)
              simp [hcol_inc]
            ⟩
        · if hsuccj_lt : j + 1 < cells.length then
            simp_rw[List.getElem?_eq_getElem hsuccj_lt, op_lst_some, row_comp, List.length_dropLast,
              List.getElem_dropLast]
            simp only [hsuccj_lt, ↓reduceDIte,] at hst_dec
            exact ⟨by omega, by
              intro i hi_lt_len
              exact SSYT_col_increasing hSSYT i j (j + 1) (lt_add_one j) hsuccj_lt hi_lt_len
            ⟩
          else
            rw[List.getElem?_eq_none (Nat.le_of_not_lt hsuccj_lt)]
            exact op_lst_none_r
  · case isFalse a =>
    constructor
    · simp_rw[List.getElem_dropLast, List.length_dropLast]
      intro j hj_lt_len
      exact hSSYT.left j (Nat.lt_of_lt_pred hj_lt_len)
    · exact rowinc_front_rowinc hSSYT.right

example (a : Nat) : [a].length = 1 := by exact List.length_singleton
example (a b : Nat) (h : a < b) : (a - 1 < b) := by exact Nat.sub_lt_of_lt h
example (a b : Nat) (h : a ≤ b) : (a - 1 ≤ b) := by omega

example (a b : Nat) (h : a < b) (h2 : a + 1 ≠ b) : (a + 1 < b) := Nat.lt_of_le_of_ne h h2
example (l : List Nat) (p : Nat → Bool) : (∀ e ∈ l.takeWhile p, p e) := by
  have ijij := List.all_takeWhile (l:=l) (p:=p)
  grind
example (a b : Nat) (h : b = a) : a ≤ b := by exact Nat.le_of_eq (id (Eq.symm h))
example (a : Nat) (h : a ≠ 0) : a - 1 < a := by exact Nat.sub_one_lt h

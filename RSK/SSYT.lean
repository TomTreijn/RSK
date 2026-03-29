import RSK.OrderedList
import Mathlib.Tactic

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

def isDiagram (cells : Grid) : Prop :=
  IsWeakDec (cells.map (·.length)) ∧
  ∀ (i : Nat) (h : i < cells.length), cells[i].length > 0

def isSSYT (cells : Grid) (hdiagram : isDiagram cells) : Prop :=
  (∀ (j : Nat) (h : j < cells.length), IsWeakInc cells[j]) ∧
  ∀ (j₁ j₂ i : Nat)
    (hj₁_lt_j₂ : j₁ < j₂)
    (hj₂_lt_len : j₂ < cells.length)
    (hi_lt_len : i < cells[j₂].length),
    have hj₁_lt_len : j₁ < cells.length := Nat.lt_trans hj₁_lt_j₂ hj₂_lt_len
    have hlenj₂_le_lenj₁ : cells[j₂].length ≤ cells[j₁].length := by
      have map_le := wkdec_wkdec2.mp hdiagram.left j₁ j₂ hj₁_lt_j₂ (by rw[List.length_map]; exact hj₂_lt_len)
      simp only [List.getElem_map, ge_iff_le] at map_le
      exact map_le
    cells[j₁][i] < cells[j₂][i]

def isSSYT2 (cells : Grid) (hdiagram : isDiagram cells) : Prop :=
  (∀ (i : Nat) (h : i < cells.length), IsWeakInc cells[i]) ∧
  if hempty : cells = [] then
    True
  else
    have hzero_lt_len : 0 < cells.length := List.length_pos_iff.mpr hempty
    ∀ (i : Nat),
      let rows := cells.takeWhile (i < ·.length)
      let col := rows.mapFinIdx (fun j _ hi_lt ↦ rows[j][i]'(by
        have all :=  List.all_takeWhile (l:=cells) (p:=(i < ·.length))
        have lt := List.all_eq_true.mp all rows[j] (List.getElem_mem hi_lt)
        grind
      ))
      IsStrictInc col

theorem Diagram_append (hdiagram : isDiagram cells) (j : Nat) (k : Nat)
  (hi_lt_len : j < cells.length)
  (hst_dec : j = 0 ∨ cells[j].length < cells[j - 1].length) :
  isDiagram (cells.set j (cells[j] ++ [k])) := by
  constructor
  · have switch_map_set : (cells.set j (cells[j] ++ [k])).map (·.length) =
      (cells.map (·.length)).set j (cells[j].length + 1) := by
      have lengths_eq : ((cells.set j (cells[j] ++ [k])).map (·.length)).length =
        ((cells.map (·.length)).set j (cells[j].length + 1)).length := by simp
      apply List.map_eq_iff.mpr
      grind
    rw[switch_map_set]
    apply wkdec_set_wkdec
    · exact hdiagram.left
    · constructor
      · have subj_lt_len : j - 1 < (cells.map (·.length)).length := by
          rw[List.length_map]
          exact Nat.sub_lt_of_lt hi_lt_len
        rw[List.getElem?_eq_getElem subj_lt_len, op_ge_some, List.getElem_map]
        if hj : j = 0 then
          apply Or.intro_left
          exact hj
        else
          apply Or.intro_right
          have := Or.resolve_left hst_dec hj
          omega
      · if hsuccj_lt_len : j + 1 < (cells.map (·.length)).length then
          rw[List.getElem?_eq_getElem hsuccj_lt_len, op_ge_some, List.getElem_map]
          have from_diagram := wkdec_wkdec2.mp hdiagram.left j (j+1) (Nat.lt_add_one j) hsuccj_lt_len
          repeat rw [List.getElem_map] at from_diagram
          omega
        else
          rw[List.getElem?_eq_none (Nat.le_of_not_lt hsuccj_lt_len)]
          exact op_ge_none_r
  · intro i h
    if hij : j = i then
      simp_rw[←hij]
      rw[List.getElem_set_self, List.length_append, List.length_singleton]
      exact Nat.zero_lt_succ cells[j].length
    else
      rw[List.getElem_set_ne (hij)]
      rw[List.length_set] at h
      exact hdiagram.right i h

theorem length_append_neq_nil (cells : Grid) (j : Nat) (k : Nat)
  (hi_lt_len : j < cells.length)
  : List.set cells j (cells[j] ++ [k]) ≠ [] := by
  by_contra hP
  have length_nil : ([] : Grid).length = 0 := List.length_nil
  rw [←hP] at length_nil
  rw[List.length_set] at length_nil
  rw [length_nil] at hi_lt_len
  contradiction

theorem SSYT_append (hSSYT : isSSYT cells hdiagram) (j : Nat) (k : Nat)
  (hi_lt_len : j < cells.length)
  (hst_dec : j = 0 ∨ cells[j].length < cells[j - 1].length)
  (h_row : IsWeakInc (cells[j] ++ [k]))
  (h_col_above :
    if hi : j = 0 then
      True
    else
      have := Or.resolve_left hst_dec hi
      have := Nat.sub_lt_of_lt hi_lt_len
      k > (cells[j - 1])[cells[j].length]
  ) :
  isSSYT (cells.set j (cells[j] ++ [k])) (Diagram_append hdiagram j k hi_lt_len hst_dec) := by
  rw[isSSYT]
  constructor
  · intro j₂ hj₂_lt_len
    rw[List.length_set] at hj₂_lt_len
    if hj₂ : j = j₂ then
      simp_rw[←hj₂, List.getElem_set_self]
      exact h_row
    else
      rw [List.getElem_set_ne hj₂]
      exact hSSYT.left j₂ hj₂_lt_len
  · intro j₁ j₂ i hj₁_lt_j₂ hj₂_lt_len hi_lt_len
    rw [List.length_set] at hj₂_lt_len
    simp only
    if hj₁ : j = j₁ then
      rw[←hj₁] at hj₁_lt_j₂
      have hj₂_neq_j : j ≠ j₂ := Nat.ne_of_lt hj₁_lt_j₂
      simp_rw[←hj₁, List.getElem_set_self, List.getElem_set_ne hj₂_neq_j]
      rw[List.getElem_set_ne hj₂_neq_j] at hi_lt_len
      have hi : i < cells[j].length := by
        have hlen_j_gt_j₂ := wkdec_wkdec2.mp hdiagram.left
          j j₂ hj₁_lt_j₂ (by rw[List.length_map]; exact hj₂_lt_len)
        repeat rw[List.getElem_map] at hlen_j_gt_j₂
        exact Nat.lt_of_lt_of_le hi_lt_len hlen_j_gt_j₂
      rw[List.getElem_append_left hi]
      exact hSSYT.right j j₂ i hj₁_lt_j₂ hj₂_lt_len hi_lt_len
    else
      simp_rw[List.getElem_set_ne hj₁]
      if hj₂ : j = j₂ then
        rw[←hj₂] at hj₁_lt_j₂
        rw[←hj₂] at hj₂_lt_len
        simp_rw[←hj₂, List.getElem_set_self, List.length_append, List.length_singleton] at hi_lt_len
        simp_rw[←hj₂, List.getElem_set_self]
        if hi : i = cells[j].length then
          have j_neq_zero : j ≠ 0 := Nat.ne_zero_of_lt hj₁_lt_j₂
          have hst_dec := Or.resolve_left hst_dec j_neq_zero
          rw [List.getElem_append_right (Nat.le_of_eq (Eq.symm hi))]
          simp_rw [hi, Nat.sub_self, List.getElem_singleton]
          simp only [j_neq_zero, ↓reduceDIte, gt_iff_lt] at h_col_above
          if hj₁_eq_sub_j : j₁ = j - 1 then
            simp_rw[hj₁_eq_sub_j]
            exact h_col_above
          else
            have j₁_lt_sub_j : j₁ < j - 1 := by omega
            have from_SSYT := hSSYT.right
              j₁ (j - 1) (cells[j].length) j₁_lt_sub_j (Nat.sub_lt_of_lt hj₂_lt_len) (hst_dec)
            simp only at from_SSYT
            exact Nat.lt_trans from_SSYT h_col_above
        else
          have i_lt_len : i < cells[j].length := by omega
          rw[List.getElem_append_left i_lt_len]
          exact hSSYT.right j₁ j i hj₁_lt_j₂ hj₂_lt_len i_lt_len
      else
        rw [List.getElem_set_ne hj₂] at hi_lt_len
        simp_rw [List.getElem_set_ne hj₂]
        exact hSSYT.right j₁ j₂ i hj₁_lt_j₂ hj₂_lt_len hi_lt_len





example (a : Nat) : [a].length = 1 := by exact List.length_singleton
example (a b : Nat) (h : a < b) : (a - 1 < b) := by exact Nat.sub_lt_of_lt h
example (a b : Nat) (h : a < b) (h2 : a + 1 ≠ b) : (a + 1 < b) := Nat.lt_of_le_of_ne h h2
example (l : List Nat) (p : Nat → Bool) : (∀ e ∈ l.takeWhile p, p e) := by
  have ijij := List.all_takeWhile (l:=l) (p:=p)
  grind
example (a b : Nat) (h : b = a) : a ≤ b := by exact Nat.le_of_eq (id (Eq.symm h))

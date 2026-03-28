import RSK.OrderedList
import Mathlib.Tactic

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

def isDiagram (cells : Grid) : Prop :=
  IsWeakDec (cells.map (·.length)) ∧
  ∀ (i : Nat) (h : i < cells.length), cells[i].length > 0

def isSSYT (cells : Grid) (hdiagram : isDiagram cells) : Prop :=
  ∀ (i : Nat) (h : i < cells.length), IsWeakInc cells[i] ∧
  ∀ (i₁ i₂ j : Nat)
    (hi₁_le_i₂ : i₁ < i₂)
    (hi₂_le_len : i₂ < cells.length)
    (hj_le_len : j < cells[i₂].length),
    have hi₁_lt_len : i₁ < cells.length := Nat.lt_trans hi₁_le_i₂ hi₂_le_len
    have hleni₂_le_leni₁ : cells[i₂].length ≤ cells[i₁].length := by
      have map_le := wkdec_wkdec2.mp hdiagram.left i₁ i₂ hi₁_le_i₂ (by rw[List.length_map]; exact hi₂_le_len)
      simp only [List.getElem_map, ge_iff_le] at map_le
      exact map_le
    cells[i₁][j] < cells[i₂][j]

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

  sorry


example (a : Nat) : [a].length = 1 := by exact List.length_singleton
example (a b : Nat) (h : a < b) : (a - 1 < b) := by exact Nat.sub_lt_of_lt h
example (a b : Nat) (h : a < b) (h2 : a + 1 ≠ b) : (a + 1 < b) := Nat.lt_of_le_of_ne h h2

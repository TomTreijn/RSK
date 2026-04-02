import RSK.OrderedList
import Mathlib.Tactic

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

def IsDiagram (cells : Grid) : Prop :=
  IsWeakDec (cells.map (·.length)) ∧
  ∀ (i : Nat) (h : i < cells.length), cells[i].length > 0

theorem diagram_decreasing (hdiagram : IsDiagram cells)
  (j₁ j₂ : Nat) (hj₁_lt_j₂ : j₁ < j₂) (hj₂_lt_len : j₂ < cells.length) :
  cells[j₁].length ≥ cells[j₂].length := by
  have almost := wkdec_wkdec2.mp hdiagram.left
    j₁ j₂ hj₁_lt_j₂ (by rw[List.length_map]; exact hj₂_lt_len)
  repeat rw[List.getElem_map] at almost
  exact almost

def IsSSYT (cells : Grid) (hdiagram : IsDiagram cells) : Prop :=
  (∀ (j : Nat) (h : j < cells.length), IsWeakInc cells[j]) ∧
  -- Could be turned into pairwise comparison to make proving the increasing columns easier.
  ∀ (j₁ j₂ i : Nat)
    (hj₁_lt_j₂ : j₁ < j₂)
    (hj₂_lt_len : j₂ < cells.length)
    (hi_lt_len : i < cells[j₂].length),
    have hlenj₂_le_lenj₁ : cells[j₂].length ≤ cells[j₁].length :=
      diagram_decreasing hdiagram j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
    cells[j₁][i] < cells[j₂][i]

theorem Diagram_append (hdiagram : IsDiagram cells) (j : Nat) (k : Nat)
  (hj_lt_len : j < cells.length)
  (hst_dec : j = 0 ∨ cells[j].length < cells[j - 1].length) :
  IsDiagram (cells.set j (cells[j] ++ [k])) := by
  constructor
  · rw[List.map_set, List.length_append, List.length_singleton]
    apply wkdec_set_wkdec
    · exact hdiagram.left
    · constructor
      · have subj_lt_len : j - 1 < (cells.map (·.length)).length := by
          rw[List.length_map]
          exact Nat.sub_lt_of_lt hj_lt_len
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
          rw[List.length_map] at hsuccj_lt_len
          have from_diagram := diagram_decreasing hdiagram j (j+1) (lt_add_one j) (hsuccj_lt_len)
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
  (hj_lt_len : j < cells.length)
  : List.set cells j (cells[j] ++ [k]) ≠ [] := by
  by_contra hP
  have length_nil : ([] : Grid).length = 0 := List.length_nil
  rw [←hP] at length_nil
  rw[List.length_set] at length_nil
  rw [length_nil] at hj_lt_len
  contradiction

example (i : Nat) : i ≥ 0 := by sorry

theorem SSYT_append (hSSYT : IsSSYT cells hdiagram) (j : Nat) (k : Nat)
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
  IsSSYT (cells.set j (cells[j] ++ [k])) (Diagram_append hdiagram j k hj_lt_len hst_dec) := by
  rw[IsSSYT]
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
        have len_j_ge_j₂ := diagram_decreasing hdiagram j j₂ hj₁_lt_j₂ hj₂_lt_len
        exact Nat.lt_of_lt_of_le hi_lt_len len_j_ge_j₂
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

theorem Diagram_set(h_diagram : IsDiagram cells)
  (j i k : Nat) (hj : j < cells.length) :
  IsDiagram (cells.set j (cells[j].set i k)) := by
  have iji : cells.map (·.length) = (cells.set j (cells[j].set i k)).map (·.length) := by
    apply List.map_eq_iff.mpr
    intro j₂
    if hj₂_gt : j₂ < cells.length then
      repeat rw[List.getElem?_eq_getElem]
      · simp
        if hj₂_eq : j = j₂ then
          simp_rw [hj₂_eq, List.getElem_set_self]
        else
          rw [List.getElem_set_ne hj₂_eq]
          simp only [List.getElem_map]
      · exact hj₂_gt
      · rw[List.length_map, List.length_set]
        exact hj₂_gt
    else
      have j₂_ge_len : j₂ ≥ cells.length := Nat.le_of_not_lt hj₂_gt
      repeat rw[List.getElem?_eq_none]
      · simp only [Option.map_none]
      · exact j₂_ge_len
      · rw[List.length_map, List.length_set]
        exact j₂_ge_len
  constructor
  · rw[←iji]
    exact h_diagram.left
  · intro j₂ h_len
    repeat rw[List.length_set] at h_len
    if hj₂_eq : j = j₂ then
      simp_rw [hj₂_eq, List.getElem_set_self, List.length_set]
      exact h_diagram.right j₂ h_len
    else
      simp_rw [List.getElem_set_ne hj₂_eq]
      exact h_diagram.right j₂ h_len

theorem SSYT_set (hSSYT : IsSSYT cells hdiagram) (j i : Nat) (k : Nat)
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
  ) : IsSSYT (cells.set j (cells[j].set i k)) (Diagram_set hdiagram j i k hj_lt_len) := by
    constructor
    · intro j₂ hj₂_lt_len
      rw [List.length_set] at hj₂_lt_len
      if hj₂ : j = j₂ then
        simp_rw [←hj₂, List.getElem_set_self]
        exact h_row
      else
        rw [List.getElem_set_ne hj₂]
        exact hSSYT.left j₂ hj₂_lt_len
    · intro j₁ j₂ i₂ hj₁_lt_j₂ hj₂_lt_len hi₂_lt_len
      simp only
      rw [List.length_set] at hj₂_lt_len
      if hj₁_eq_j : j = j₁ then
        rw [←hj₁_eq_j] at hj₁_lt_j₂
        have hj₂_neq_j : j ≠ j₂ := Nat.ne_of_lt hj₁_lt_j₂
        simp_rw[←hj₁_eq_j, List.getElem_set_self, List.getElem_set_ne hj₂_neq_j]
        simp_rw [List.getElem_set_ne hj₂_neq_j] at hi₂_lt_len
        if hi₂_eq_i : i = i₂ then
          simp_rw[←hi₂_eq_i, List.getElem_set_self]
          rw [←hi₂_eq_i] at hi₂_lt_len
          have hsuccj_lt_len : j + 1 < cells.length := Nat.lt_of_le_of_lt hj₁_lt_j₂ hj₂_lt_len
          if hj₂_eq_succ_j : j₂ = j + 1 then
            simp_rw [hj₂_eq_succ_j]
            simp_rw [hj₂_eq_succ_j] at hi₂_lt_len
            simp only [hsuccj_lt_len, ↓reduceDIte, hi₂_lt_len] at h_col_under
            exact h_col_under
          else
            have hsuccj_lt_j₂ : j + 1 < j₂ := Nat.lt_of_le_of_ne hj₁_lt_j₂ (Ne.symm hj₂_eq_succ_j)
            have len_succj_gt_j₂ := diagram_decreasing hdiagram (j+1) j₂ hsuccj_lt_j₂ hj₂_lt_len
            have hi₂_lt_len_succj : i < cells[j+1].length :=
              Nat.lt_of_lt_of_le hi₂_lt_len len_succj_gt_j₂
            simp only [hsuccj_lt_len, ↓reduceDIte, hi₂_lt_len_succj] at h_col_under
            have inc := hSSYT.right (j + 1) j₂ i hsuccj_lt_j₂ hj₂_lt_len hi₂_lt_len
            exact Nat.lt_trans h_col_under inc
        else
          rw [List.getElem_set_ne hi₂_eq_i]
          exact hSSYT.right j j₂ i₂ hj₁_lt_j₂ hj₂_lt_len hi₂_lt_len
      else
        simp_rw[List.getElem_set_ne hj₁_eq_j]
        if hj₂_eq_j : j = j₂ then
          rw [←hj₂_eq_j] at hj₁_lt_j₂
          simp_rw[←hj₂_eq_j, List.getElem_set_self]
          simp_rw [←hj₂_eq_j, List.getElem_set_self, List.length_set] at hi₂_lt_len
          rw [←hj₂_eq_j] at hj₂_lt_len
          have hj_gt_zero : j ≠ 0 := Nat.ne_zero_of_lt hj₁_lt_j₂
          simp only [hj_gt_zero, ↓reduceDIte] at h_col_above
          if hi₂_eq_i : i = i₂ then
            simp_rw [←hi₂_eq_i, List.getElem_set_self]
            rw [←hi₂_eq_i] at hi₂_lt_len
            if hj₁_eq_sub_j : j₁ = j - 1 then
              simp_rw [hj₁_eq_sub_j]
              exact h_col_above
            else
              have hj₁_lt_sub_j : j₁ < j - 1 := by omega
              have hsub_j_lt_len : j - 1 < cells.length := Nat.sub_lt_of_lt hj_lt_len
              have hi_lt_sub_j_len : i < cells[j - 1].length := by
                have := diagram_decreasing hdiagram (j - 1) j (Nat.sub_one_lt hj_gt_zero) hj₂_lt_len
                exact Nat.lt_of_lt_of_le hi₂_lt_len this
              have inc := hSSYT.right j₁ (j - 1) i hj₁_lt_sub_j hsub_j_lt_len hi_lt_sub_j_len
              exact Nat.lt_trans inc h_col_above
          else
            rw [List.getElem_set_ne hi₂_eq_i]
            exact hSSYT.right j₁ j i₂ hj₁_lt_j₂ hj₂_lt_len hi₂_lt_len
        else
          simp_rw [List.getElem_set_ne hj₂_eq_j]
          simp_rw [List.getElem_set_ne hj₂_eq_j] at hi₂_lt_len
          exact hSSYT.right j₁ j₂ i₂ hj₁_lt_j₂ hj₂_lt_len hi₂_lt_len

theorem Diagram_remove (hdiagram : IsDiagram cells) (j : Nat)
  (hj_lt_len : j < cells.length)
  (hst_dec :
    if hsuccj_len : j + 1 < cells.length then
      cells[j].length > cells[j + 1].length
    else
      True
  ) :
  if cells[j].length > 1 then
    IsDiagram (cells.set j (cells[j].dropLast))
  else
    IsDiagram cells.dropLast := by
  split
  · case isTrue hlenj =>
      constructor
      · rw[List.map_set, List.length_dropLast]
        apply wkdec_set_wkdec
        · exact hdiagram.left
        · constructor
          · if hj : j = 0 then
              apply Or.intro_left
              exact hj
            else
              apply Or.intro_right
              have hsubj_lt_len : j - 1 < cells.length := Nat.sub_lt_of_lt hj_lt_len
              rw[List.getElem?_eq_getElem (by rw[List.length_map]; exact hsubj_lt_len)]
              have subj_lt_j : j -1 < j := Nat.sub_one_lt hj
              rw[op_ge_some, List.getElem_map]
              have := diagram_decreasing hdiagram (j-1) j subj_lt_j hj_lt_len
              omega
          · if hsuccj : j + 1 < cells.length then
              simp only [hsuccj, ↓reduceDIte] at hst_dec
              rw[List.getElem?_eq_getElem (by rw[List.length_map]; exact Nat.lt_of_succ_le hsuccj)]
              rw[op_ge_some, List.getElem_map]
              exact Nat.le_sub_one_of_lt hst_dec
            else
              rw[List.getElem?_eq_none (by rw[List.length_map]; exact Nat.le_of_not_lt hsuccj)]
              exact op_ge_none_r
      · intro i hi_lt_len
        rw [List.length_set] at hi_lt_len
        if hi_eq_j : j = i then
          simp_rw[←hi_eq_j, List.getElem_set_self, List.length_dropLast]
          omega
        else
          rw[List.getElem_set_ne hi_eq_j]
          exact hdiagram.right i hi_lt_len
  · case isFalse hlenj =>
    -- have hlenj_eq_one : cells[j].length = 1 := by
    --   have := hdiagram.right j hj_lt_len
    --   omega
    -- have hlen_eq_succ_j : cells.length = j + 1 := by
    --   by_contra hP
    --   have hsuccj_lt_len : j + 1 < cells.length := Nat.lt_of_le_of_ne hj_lt_len (Ne.symm hP)
    --   simp[hsuccj_lt_len, hlenj_eq_one] at hst_dec
    --   have hlen_succj_gt_zero := hdiagram.right (j + 1) hsuccj_lt_len
    --   rw [hst_dec] at hlen_succj_gt_zero
    --   contradiction
    constructor
    · rw[List.map_dropLast]
      exact wkdec_front_wkdec hdiagram.left
    · intro i hi_lt_sub_len
      rw [List.getElem_dropLast]
      rw [List.length_dropLast] at hi_lt_sub_len
      have hi_lt_len : i < cells.length := Nat.lt_of_lt_pred hi_lt_sub_len
      exact hdiagram.right i hi_lt_len

example (a : Nat) : [a].length = 1 := by exact List.length_singleton
example (a b : Nat) (h : a < b) : (a - 1 < b) := by exact Nat.sub_lt_of_lt h
example (a b : Nat) (h : a ≤ b) : (a - 1 ≤ b) := by omega

example (a b : Nat) (h : a < b) (h2 : a + 1 ≠ b) : (a + 1 < b) := Nat.lt_of_le_of_ne h h2
example (l : List Nat) (p : Nat → Bool) : (∀ e ∈ l.takeWhile p, p e) := by
  have ijij := List.all_takeWhile (l:=l) (p:=p)
  grind
example (a b : Nat) (h : b = a) : a ≤ b := by exact Nat.le_of_eq (id (Eq.symm h))
example (a b : Nat) (h : a ≠ 0) : a - 1 < a := by exact Nat.sub_one_lt h

import RSK.OrderedList

abbrev Grid := List (List Nat)

def isDiagram (cells : Grid) : Prop := IsWeakDec (cells.map (·.length))

def isSSYT (cells : Grid) (hdiagram : isDiagram cells) : Prop :=
  ∀ (i : Nat) (h : i < cells.length), IsWeakInc cells[i] ∧
  ∀ (i₁ i₂ j : Nat)
    (hi₁_le_i₂ : i₁ < i₂)
    (hi₂_le_len : i₂ < cells.length)
    (hj_le_len : j < cells[i₂].length),
    have hi₁_lt_len : i₁ < cells.length := Nat.lt_trans hi₁_le_i₂ hi₂_le_len
    have hleni₂_le_leni₁ : cells[i₂].length ≤ cells[i₁].length := by
      have map_le := wkdec_wkdec2.mp hdiagram i₁ i₂ hi₁_le_i₂ (by rw[List.length_map]; exact hi₂_le_len)
      simp at map_le
      exact map_le
    cells[i₁][j] < cells[i₂][j]

structure SSYT where
  cells : List (List Nat)
  hdiagram : IsWeakDec (cells.map (·.length))
  hrow_ord : ∀ (i : Nat) (h : i < cells.length), IsWeakInc cells[i]
  hcol_ord : ∀ (i₁ i₂ j : Nat)
    (hi₁_le_i₂ : i₁ < i₂)
    (hi₂_le_len : i₂ < cells.length)
    (hj_le_len : j < cells[i₂].length),
    have hi₁_lt_len : i₁ < cells.length := Nat.lt_trans hi₁_le_i₂ hi₂_le_len
    have hleni₂_le_leni₁ : cells[i₂].length ≤ cells[i₁].length := by
      have map_le := wkdec_wkdec2.mp hdiagram i₁ i₂ hi₁_le_i₂ (by rw[List.length_map]; exact hi₂_le_len)
      simp at map_le
      exact map_le
    cells[i₁][j] < cells[i₂][j]

theorem SSYT_append (ssyt : SSYT) (k : Nat) (i : Nat)
  (hi_lt_len : i < ssyt.cells.length)
  (h_diagram : i = 0 ∨ ssyt.cells[i].length < ssyt.cells[i - 1].length)
  (h_row : IsWeakInc ssyt.cells[i] ++ [k])
  (h_col_above : i = 0 ∨ k < ssyt.cells[i - 1][ssyt.cells[i].length])
  (h_col_under : op_le ssyt.cells[i+1]?[2] k) :

  := by sorry

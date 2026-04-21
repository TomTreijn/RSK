import RSK.OrderedList
import RSK.SSYT
import Mathlib.Tactic

set_option relaxedAutoImplicit true

def entries (cells : Grid) : List Nat :=
  cells.flatten

def shape (cells : Grid) : List Nat :=
  cells.map (·.length)

def size (cells : Grid) : Nat :=
  (shape cells).sum

theorem size_eq_entries_len (cells : Grid) :
  (entries cells).length = size cells := by
  rw[entries]
  apply List.length_flatten

theorem shape_length_eq_length {cells : Grid} : (shape cells).length = cells.length := by
  rw[shape, List.length_map]

theorem memEntry_of_memRow (cells : Grid) (j k : Nat)
  (hj : j < cells.length) (hrow : k ∈ cells[j]) :
  k ∈ entries cells := by
  have hj_mem := List.getElem_mem hj
  exact List.mem_flatten.mpr ⟨cells[j], ⟨hj_mem, hrow⟩⟩

theorem getElem_entry (cells : Grid) (i j : Nat)
  (hj : j < cells.length) (hi : i < cells[j].length) :
  cells[j][i] ∈ entries cells := by
  have hi_mem := List.getElem_mem hi
  exact memEntry_of_memRow cells j cells[j][i] hj hi_mem

theorem entry_getElem (cells : Grid) (k : Nat) (hk : k ∈ entries cells) :
  ∃(j i : Nat) (hj_lt_len : j < cells.length) (hi_lt_len : i < cells[j].length), k = cells[j][i]
   := by
  rw[entries] at hk
  have ⟨row, ⟨row_in_cell, k_in_row⟩⟩ := List.mem_flatten.mp hk
  have ⟨j, ⟨hj, jrow⟩⟩:= List.getElem_of_mem row_in_cell
  rw[←jrow] at k_in_row
  have ⟨i, ⟨hi, krow⟩⟩:= List.getElem_of_mem k_in_row
  exact ⟨j, ⟨i, ⟨hj, ⟨hi, Eq.symm krow⟩⟩⟩⟩

structure location (cells : Grid) (k : Nat) where
  i : Nat
  j : Nat
  hj_lt_len : j < cells.length
  hi_lt_len : i < cells[j].length
  eq : k = cells[j][i]

def entry_location (cells : Grid) (k : Nat) (hk : k ∈ entries cells) : location cells k
   :=
  let j := cells.findIdx (k ∈ ·)
  have hj_eq : j = cells.findIdx (k ∈ ·) := by rfl
  have hj_lt_len : j < cells.length := by
    apply List.findIdx_lt_length.mpr
    simp[List.mem_flatten.mp hk]
  have hk_in : k ∈ cells[j] := by
    simp only [hj_eq]
    simp (config := { singlePass := true }) only [← decide_eq_true_eq, Bool.decide_eq_true]
    exact List.findIdx_getElem (w:=hj_lt_len)
  let i := cells[j].findIdx (k = ·)
  have hi_eq : i = cells[j].findIdx (k = ·) := by rfl
  have hi_lt_len : i < cells[j].length := by
    apply List.findIdx_lt_length.mpr
    simp[hk_in]
  have hk_eq : k = cells[j][i] := by
    simp only [hi_eq]
    simp (config := { singlePass := true }) only [← decide_eq_true_eq, Bool.decide_eq_true]
    exact List.findIdx_getElem (w:=hi_lt_len)
  ⟨i, j, hj_lt_len, hi_lt_len, hk_eq⟩

theorem count_set (cells : Grid) (j a : Nat) (l : List Nat) (hj_lt_len : j < cells.length) :
  (cells.set j l).flatten.count a = cells.flatten.count a + l.count a - cells[j].count a := by
  rw[List.count_flatten]
  rw[List.map_set, List.sum_set]
  simp only [List.length_map, hj_lt_len, ↓reduceIte]
  apply Eq.symm
  calc
    cells.flatten.count a + l.count a - cells[j].count a =
    (cells.map (·.count a)).sum + l.count a - cells[j].count a := by simp[List.count_flatten]
    _ = ((cells.map (·.count a)).take (j+1)).sum +
        ((cells.map (·.count a)).drop (j+1)).sum +
        l.count a - cells[j].count a :=
          by simp[List.sum_take_add_sum_drop]
    _ = ((cells.map (·.count a)).take j).sum + cells[j].count a +
        ((cells.map (·.count a)).drop (j + 1)).sum +
        l.count a - cells[j].count a := by
      rw[List.sum_take_succ]
      · rw[List.getElem_map]
      · rw[List.length_map]
        exact hj_lt_len
    _ = _ := by
      have triv : List.map (·.count a) cells = List.map (fun x ↦ List.count a x) cells := by rfl
      rw[triv]
      omega

theorem entries_add (cells : Grid) (k j : Nat)
  (hj_lt_len : j < cells.length) :
  List.Perm (entries (cells.set j (cells[j] ++ [k]))) (k::(entries cells)) := by
  repeat rw[entries]
  apply List.perm_iff_count.mpr
  intro a
  rw[count_set (hj_lt_len:=hj_lt_len)]
  nth_rewrite 2 [←List.singleton_append]
  repeat rw[List.count_append]
  omega

theorem count_dropLast (l : List Nat) (hnot_nil : l ≠ []) :
  (l.dropLast.count k = l.count k - if l.getLast hnot_nil = k then 1 else 0) := by
  match hl : l with
  | [] => contradiction
  | [a] =>
    if h_a_eq_k : a = k then
      simp [h_a_eq_k]
    else
      simp [h_a_eq_k]
  | a :: b :: as =>
    have hsub_notnil : b :: as ≠ [] := by simp
    rw[List.dropLast, List.getLast, List.count_cons, List.count_cons]
    · rw[count_dropLast (b :: as) hsub_notnil]
      if hk_last : k = (b :: as).getLast hsub_notnil then
        have poij : (b :: as).count ((b :: as).getLast hsub_notnil) > 0 := by
          apply List.count_pos_iff.mpr
          have mem := List.getLast_mem hsub_notnil
          exact mem
        simp only [hk_last, ↓reduceIte, beq_iff_eq]
        omega
      else
        simp[Ne.symm hk_last]
    · exact hsub_notnil

theorem entries_remove (cells : Grid) (j : Nat)
  (hj_lt_len : j < cells.length) (hnot_nil : cells[j] ≠ []) :
  List.Perm (entries (cells.set j (cells[j].dropLast)))
  ((entries cells).erase (cells[j].getLast hnot_nil)) := by
  repeat rw[entries]
  apply List.perm_iff_count.mpr
  intro a
  rw[count_set (hj_lt_len := hj_lt_len), count_dropLast (hnot_nil := hnot_nil), List.count_erase]
  simp only [beq_iff_eq]
  if hlast_a : cells[j].getLast hnot_nil = a then
    have count_pos : cells[j].count a > 0 := by
      apply List.count_pos_iff.mpr
      rw[←hlast_a]
      exact List.getLast_mem hnot_nil
    simp only [hlast_a, ↓reduceIte]
    omega
  else
    simp[hlast_a]

example (a : Nat) (l : List Nat) (h : a ∈ l) : a ≤ l.sum := by exact List.le_sum_of_mem h

theorem sum_dropLast (l : List Nat) (hnotnil : l ≠ []) :
  l.sum - l.getLast hnotnil = l.dropLast.sum := by
  match l with
  | [] => contradiction
  | [a] => simp
  | a :: b :: as =>
    have hbas_not_nil : b :: as ≠ [] := by exact List.cons_ne_nil b as
    rw[List.dropLast, List.getLast, List.sum_cons]
    · nth_rewrite 2 [List.sum_cons]
      have := sum_dropLast (b :: as) hbas_not_nil
      rw[←this]
      rw[Nat.add_sub_assoc]
      exact List.le_sum_of_mem (List.getLast_mem hbas_not_nil)
    · exact hbas_not_nil

theorem entries_dropLastRow {a} (cells : Grid) (hnot_nil : cells ≠ [])
  (singleton : cells.getLast hnot_nil = [a]) :
  List.Perm (entries cells.dropLast) ((entries cells).erase a) := by
  repeat rw[entries]
  apply List.perm_iff_count.mpr
  intro b
  rw[List.count_flatten, List.map_dropLast, ←sum_dropLast, List.count_erase,
    List.getLast_eq_getElem, List.getElem_map]
  · simp_rw[List.length_map]
    rw[←List.getLast_eq_getElem, singleton, ←List.count_flatten]
    · if hab : a = b then
        simp[hab]
      else
        simp[hab]
    · exact hnot_nil
  · apply List.length_pos_iff.mp
    rw[List.length_map]
    apply List.length_pos_iff.mpr
    exact hnot_nil

theorem shape_add (cells : Grid) (k j : Nat)
  (hj_lt_len : j < cells.length) :
  shape (cells.set j (cells[j] ++ [k])) = (shape cells).modify j (· + 1) := by
  repeat rw [shape]
  apply List.ext_getElem
  · simp
  · intro i hi_lt_len
    if hi_eq_j : j = i then
      simp[hi_eq_j]
    else
      simp[hi_eq_j]

theorem shape_remove (cells : Grid) (j : Nat)
  (hj_lt_len : j < cells.length) :
  (shape (cells.set j (cells[j].dropLast))) = (shape cells).modify j (· - 1) := by
  repeat rw [shape]
  apply List.ext_getElem
  · simp
  · intro i hi_lt_len
    if hi_eq_j : j = i then
      simp[hi_eq_j]
    else
      simp[hi_eq_j]

theorem size_add (cells : Grid) (k j : Nat)
  (hj_lt_len : j < cells.length) :
  size (cells.set j (cells[j] ++ [k])) = size cells + 1 := by
  rw[←size_eq_entries_len]
  have entries_add_rw : (entries (cells.set j (cells[j] ++ [k]))).length =
    (k::(entries cells)).length := by
      apply List.Perm.length_eq
      exact entries_add cells k j hj_lt_len
  rw[entries_add_rw, List.length_cons]
  rw[size_eq_entries_len]

theorem size_remove (cells : Grid) (j : Nat)
  (hj_lt_len : j < cells.length) (hnot_nil : cells[j] ≠ []) :
  size (cells.set j (cells[j].dropLast)) = size cells - 1 := by
  rw[←size_eq_entries_len]
  have entries_remove_rw : (entries (cells.set j (cells[j].dropLast))).length =
    ((entries cells).erase (cells[j].getLast hnot_nil)).length := by
      apply List.Perm.length_eq
      exact entries_remove cells j hj_lt_len hnot_nil
  have last_in_entries : cells[j].getLast hnot_nil ∈ entries cells := by
    have in_row : cells[j].getLast hnot_nil ∈ cells[j] := List.getLast_mem hnot_nil
    exact memEntry_of_memRow cells j (cells[j].getLast hnot_nil) hj_lt_len in_row
  rw [entries_remove_rw, List.length_erase_of_mem last_in_entries]
  rw [size_eq_entries_len]

-- variable (cells : Grid)

def IsSYT (cells : Grid) : Prop :=
  List.Perm (entries cells) (List.range (size cells))
  ∧
  IsSSYT cells

example : IsSYT [[0, 1, 3], [2], [4]] := by
  simp only [IsSYT]
  constructor
  · apply List.isPerm_iff.mp
    decide
  · grind[IsSYT, IsMonotone, IsSSYT, IsWeakInc, IsRowInc, IsMonotone, row_comp]


theorem SYT_SSYT (hSYT : IsSYT cells) : IsSSYT cells := hSYT.right

theorem SYT_le_mem (hSYT : IsSYT cells) (k : Nat) (hk : k < size cells) :
  k ∈ entries cells := by
  have hk_in_range : k ∈ List.range (size cells) := List.mem_range.mpr hk
  exact (List.Perm.mem_iff (List.Perm.symm hSYT.left)).mp hk_in_range

theorem SYT_size_mem (hSYT : IsSYT cells) (hnot_nil : size cells ≠ 0) :
  size cells - 1 ∈ entries cells := by
  exact SYT_le_mem hSYT (size cells - 1) (by exact Nat.sub_one_lt hnot_nil)

theorem SYT_mem_le (hSYT : IsSYT cells) (i j : Nat)
  (hj : j < cells.length) (hi : i < cells[j].length) :
  cells[j][i] < size cells := by
  have hji_mem := getElem_entry cells i j hj hi
  have hji_mem_range := (List.Perm.mem_iff hSYT.left).mp hji_mem
  exact List.mem_range.mp hji_mem_range

def SYT_size_location (hSYT : IsSYT cells) (hnot_nil : size cells ≠ 0) :
  location cells (size cells - 1) :=
  entry_location cells (size cells - 1) (SYT_size_mem hSYT hnot_nil)

example (a b : Nat) (l : List Nat) : (a :: l) = ([a] ++ l) := by exact Eq.symm List.singleton_append

theorem SYT_add (hSYT : IsSYT cells) (j : Nat)
  (hj_lt_len : j < cells.length)
  (h_col : j = 0 ∨ cells[j].length < cells[j - 1].length) :
  IsSYT (cells.set j (cells[j] ++ [size cells])) := by
  constructor
  · rw[size_add]
    apply (List.Perm.congr_left (entries_add cells (size cells) j hj_lt_len) _).mpr
    rw[List.range_succ]
    nth_rewrite 1 [←List.singleton_append]
    apply (List.Perm.congr_right List.perm_append_comm _).mp
    apply List.Perm.append
    · trivial
    · exact hSYT.left
  · apply SSYT_append (SYT_SSYT hSYT) j ((size cells))
    · apply wkinc_append_wkinc (SSYT_row_weak (SYT_SSYT hSYT) j hj_lt_len) _
      rw[List.getLast?_eq_some_getLast (SSYT_row_not_nil (SYT_SSYT hSYT) _ _)]
      rw[op_le_some, List.getLast_eq_getElem]
      exact Nat.le_of_succ_le (SYT_mem_le hSYT _ _ _ _)
    · split
      · trivial
      · exact (SYT_mem_le hSYT _ _ _ _)
    · exact h_col

@[simp]
def SYT_remove_cells (hSYT : IsSYT cells) (hnot_nil : size cells ≠ 0) : Grid :=
  let j := (SYT_size_location hSYT hnot_nil).j
  have hj := (SYT_size_location hSYT hnot_nil).hj_lt_len
  if cells[j].length > 1 then
    cells.set j cells[j].dropLast
  else
    cells.dropLast

theorem SYT_remove (hSYT : IsSYT cells) (hnot_nil : size cells ≠ 0) :
  IsSYT (SYT_remove_cells hSYT hnot_nil) := by
  simp only [SYT_remove_cells]
  let location := SYT_size_location hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location hSYT hnot_nil := by rfl
  simp_rw[←hlocation_eq]
  rw[IsSYT]
  constructor
  · sorry
  · rw[apply_ite IsSSYT]
    apply SSYT_remove (SYT_SSYT hSYT)
    split
    · case _ hnot_last_row =>
      by_contra hP
      rw[Nat.not_lt] at hP
      have hi_lt_len := location.hi_lt_len
      have hi_lt_lensuccj : location.i < cells[location.j + 1].length := by omega
      have hlower_ge := SSYT_col_increasing (SYT_SSYT hSYT) location.i location.j (location.j + 1)
        (lt_add_one location.j) hnot_last_row hi_lt_lensuccj
      simp only at hlower_ge
      rw[←location.eq] at hlower_ge
      have := SYT_mem_le hSYT location.i (location.j + 1) hnot_last_row hi_lt_lensuccj
      omega
    · case _ => trivial


example (a b : Nat) (h : a < b) : a ≤ b := by exact Nat.le_of_succ_le h

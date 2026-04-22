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

theorem sum_dropLast (l : List Nat) (hnot_nil : l ≠ []) :
  l.sum - l.getLast hnot_nil = l.dropLast.sum := by
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

theorem size_dropLast (cells : Grid) (hnot_nil : cells ≠ [])
  (hsingleton : (cells.getLast hnot_nil).length = 1) :
  size (cells.dropLast) = size cells - 1 := by
  repeat rw[←size_eq_entries_len, entries]
  match cells with
  | [] => contradiction
  | [row] =>
    rw [List.getLast_singleton] at hsingleton
    rw[List.dropLast, List.flatten_nil, List.flatten_singleton, List.length_nil]
    omega
  | row₁ :: row₂ :: rest =>
    have sub_ne_nil := List.cons_ne_nil row₂ rest
    rw[List.dropLast, List.flatten_cons, List.flatten_cons]
    repeat rw[List.length_append]
    · rw[List.getLast] at hsingleton
      have ih := size_dropLast (row₂ :: rest) sub_ne_nil hsingleton
      repeat rw[←size_eq_entries_len, entries] at ih
      rw[ih]
      refine Eq.symm (Nat.add_sub_assoc ?_ row₁.length)
      rw[List.length_flatten, ←List.dropLast_concat_getLast sub_ne_nil]
      simp[hsingleton]
    · simp[sub_ne_nil]

theorem SSYT_size_zero_nil (hSSYT : IsSSYT cells) : size cells = 0 ↔ cells = [] := by
  constructor
  · intro hzero
    rw[size, shape] at hzero
    by_contra hP
    have hlen_pos : 0 < cells.length := List.length_pos_iff.mpr hP
    have hrow_len_pos : cells[0].length > 0 :=
      List.length_pos_iff.mpr (SSYT_row_not_nil hSSYT 0 hlen_pos)
    rw[←List.cons_head_tail hP, List.map, List.sum_cons, List.head_eq_getElem] at hzero
    omega
  · intro hnil
    simp[size, shape, hnil]

example (a b : Prop) (h : a ↔ b) : (¬a ↔ ¬b) := by exact not_congr h
example (a : Nat) : (a ≠ 0) ↔ (a > 0) := by exact Nat.ne_zero_iff_zero_lt

theorem SSYT_size_nzero_nnil (hSSYT : IsSSYT cells) : 0 < size cells ↔ cells ≠ [] := by
  rw[←Nat.ne_zero_iff_zero_lt]
  exact not_congr (SSYT_size_zero_nil hSSYT)

example (a : Nat) (h : 0 < a) : (1 ≤ a) := by exact Nat.one_le_of_lt h
example (a : Nat) (l : List Nat) : (a :: l = (a :: l).dropLast ++ [(a :: l).getLast (List.cons_ne_nil a l)])
  := by exact Eq.symm (List.dropLast_concat_getLast (List.cons_ne_nil a l))

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

theorem SYT_size_mem (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  size cells - 1 ∈ entries cells := by
  have size_pos : size cells > 0 := (SSYT_size_nzero_nnil (SYT_SSYT hSYT)).mpr hnot_nil
  exact SYT_le_mem hSYT (size cells - 1) (Nat.sub_one_lt_of_lt size_pos)

theorem SYT_mem_le (hSYT : IsSYT cells) (i j : Nat)
  (hj : j < cells.length) (hi : i < cells[j].length) :
  cells[j][i] < size cells := by
  have hji_mem := getElem_entry cells i j hj hi
  have hji_mem_range := (List.Perm.mem_iff hSYT.left).mp hji_mem
  exact List.mem_range.mp hji_mem_range

theorem SYT_entries_Nodup (hSYT : IsSYT cells) : (entries cells).Nodup := by
  have unique := hSYT.left
  exact List.Perm.nodup (List.Perm.symm unique) (List.nodup_range)

theorem nodup_iff_getElem_ne_getElem {l : List Nat} (hnodup : l.Nodup) (i j : Nat)
 (hi_ne_j : i ≠ j) (hi_lt_len : i < l.length) (hj_lt_len : j < l.length) :
  l[i] ≠ l[j] := by
  if hi_lt_j : i < j then
    have li_ne_lj := List.nodup_iff_getElem?_ne_getElem?.mp hnodup i j hi_lt_j hj_lt_len
    simp only [hi_lt_len, getElem?_pos, hj_lt_len, ne_eq, Option.some.injEq] at li_ne_lj
    exact li_ne_lj
  else
    have hj_lt_i : j < i := by omega
    have li_ne_lj := List.nodup_iff_getElem?_ne_getElem?.mp hnodup j i hj_lt_i hi_lt_len
    simp only [hj_lt_len, getElem?_pos, hi_lt_len, ne_eq, Option.some.injEq] at li_ne_lj
    exact Ne.symm li_ne_lj

theorem SYT_Nodup (hSYT : IsSYT cells) (j₁ j₂ i₁ i₂ : Nat)
  (hj₁_lt_len : j₁ < cells.length)
  (hj₂_lt_len : j₂ < cells.length)
  (hi₁_lt_len : i₁ < cells[j₁].length)
  (hi₂_lt_len : i₂ < cells[j₂].length)
  (hdiff : (j₁, i₁) ≠ (j₂, i₂)) :
  (cells[j₁][i₁] ≠ cells[j₂][i₂]) := by
  have entries_unique := SYT_entries_Nodup hSYT
  rw[entries] at entries_unique
  have nodup_flatten := List.nodup_flatten.mp entries_unique
  if hj_eq : j₁ = j₂ then
    simp_rw[←hj_eq]
    have nodup := nodup_flatten.left cells[j₁] (List.getElem_mem hj₁_lt_len)
    simp_rw[←hj_eq] at hi₂_lt_len
    have hi₁_ne_i₂ : i₁ ≠ i₂ := by
      simp only [hj_eq, ne_eq, Prod.mk.injEq, true_and] at hdiff
      exact hdiff
    exact nodup_iff_getElem_ne_getElem nodup i₁ i₂ hi₁_ne_i₂ hi₁_lt_len hi₂_lt_len
  else
    if hj₁_lt_j₂ : j₁ < j₂ then
      have disjoint := List.pairwise_iff_getElem.mp nodup_flatten.right
        j₁ j₂ hj₁_lt_len hj₂_lt_len hj₁_lt_j₂
      have hdiff := List.disjoint_iff_ne.mp disjoint
      exact hdiff cells[j₁][i₁] (List.getElem_mem hi₁_lt_len)
        cells[j₂][i₂] (List.getElem_mem hi₂_lt_len)
    else
      have hj₂_lt_j₁ : j₂ < j₁ := by omega
      have disjoint:= List.pairwise_iff_getElem.mp nodup_flatten.right
        j₂ j₁ hj₂_lt_len hj₁_lt_len hj₂_lt_j₁
      have hdiff := List.disjoint_iff_ne.mp disjoint
      exact Ne.symm (hdiff cells[j₂][i₂] (List.getElem_mem hi₂_lt_len)
        cells[j₁][i₁] (List.getElem_mem hi₁_lt_len)
)

theorem SYT_row_increasing (hSYT : IsSYT cells)
  (i₁ i₂ j : Nat) (hj_lt_len : j < cells.length) (hi₁_lt_i₂ : i₁ < i₂)
  (hi₂_lt_len : i₂ < cells[j].length) :
  cells[j][i₁] < cells[j][i₂] := by
  have := SSYT_row_increasing (SYT_SSYT hSYT) i₁ i₂ j hj_lt_len hi₁_lt_i₂ hi₂_lt_len
  have neq : (j, i₁) ≠ (j, i₂) := by
    simp only [ne_eq, Prod.mk.injEq, true_and]
    exact Nat.ne_of_lt hi₁_lt_i₂
  have := SYT_Nodup hSYT j j i₁ i₂ hj_lt_len hj_lt_len (by omega) hi₂_lt_len neq
  omega

def SYT_size_location (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  location cells (size cells - 1) :=
  entry_location cells (size cells - 1) (SYT_size_mem hSYT hnot_nil)

def SYT_size_location_col (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  let location := SYT_size_location hSYT hnot_nil
  have := location.hj_lt_len
  location.i = cells[location.j].length - 1 := by
  let location := SYT_size_location hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location hSYT hnot_nil := by rfl
  simp only
  rw[←hlocation_eq]
  by_contra hP
  have hj_lt_len := location.hj_lt_len
  have hi_lt_len := location.hi_lt_len
  have hsub_i_lt_len : location.i < cells[location.j].length - 1 := by omega
  have hsublen_lt_len : cells[location.j].length - 1 < cells[location.j].length := by omega
  have hrow_inc := SYT_row_increasing hSYT location.i (cells[location.j].length -1) location.j hj_lt_len hsub_i_lt_len hsublen_lt_len
  rw[←location.eq] at hrow_inc
  have := SYT_mem_le hSYT (cells[location.j].length - 1) location.j hj_lt_len hsublen_lt_len
  omega

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
def SYT_remove_cells (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) : Grid :=
  let j := (SYT_size_location hSYT hnot_nil).j
  have hj := (SYT_size_location hSYT hnot_nil).hj_lt_len
  if cells[j].length > 1 then
    cells.set j cells[j].dropLast
  else
    cells.dropLast

example (a : Nat) (h : a > 1) : a > 0 := by exact Nat.zero_lt_of_lt h
example (a : Nat) (h : a > 0) : a > a - 1 := by exact Nat.sub_one_lt_of_lt h


theorem SYT_remove (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  IsSYT (SYT_remove_cells hSYT hnot_nil) := by
  have hSSYT := SYT_SSYT hSYT
  have size_pos := (SSYT_size_nzero_nnil (hSSYT)).mpr hnot_nil
  have len_pos := List.length_pos_iff.mpr hnot_nil
  simp only [SYT_remove_cells]
  let location := SYT_size_location hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location hSYT hnot_nil := by rfl
  simp_rw[←hlocation_eq]
  have hj_lt_len := location.hj_lt_len
  have hi_lt_len := location.hi_lt_len
  have hji_eq := location.eq
  have hi_eq_right := SYT_size_location_col hSYT hnot_nil
  simp only at hi_eq_right
  rw[←hlocation_eq] at hi_eq_right
  rw[hi_eq_right] at hi_lt_len
  simp_rw[hi_eq_right] at hji_eq
  rw[IsSYT]
  constructor
  · if hsingleton : cells[location.j].length > 1 then
      simp only [gt_iff_lt, hsingleton, ↓reduceIte]
      apply (List.Perm.congr_left (entries_remove cells location.j hj_lt_len (SSYT_row_not_nil (hSSYT) location.j hj_lt_len)) _).mpr
      rw[List.getLast_eq_getElem]
      simp_rw[←hi_eq_right]
      simp_rw[←location.eq]
      rw[size_remove]
      · have := hSYT.left
        apply List.perm_iff_count.mpr
        intro a
        rw[List.count_erase]
        rw[List.perm_iff_count.mp this a]
        repeat rw[List.count_range]
        if ha_lt_subsize : a < size cells - 1 then
          have ha_neq_size : size cells - 1 ≠ a := by omega
          have ha_lt_size : a < size cells := by omega
          simp[ha_lt_subsize, ha_neq_size, ha_lt_size]
        else if ha_eq_sub_size : a = size cells - 1 then
          have hnot_nil₂ : 0 < size cells := by omega
          simp[ha_eq_sub_size, hnot_nil₂]
        else
          have ha_ge_size : a ≥ size cells := by omega
          have hna_lt_size : ¬a < size cells := by omega
          have hsize_le_succ_a : size cells ≤ a + 1 := by omega
          simp[hna_lt_size, hsize_le_succ_a]
      · exact SSYT_row_not_nil (hSSYT) location.j hj_lt_len
    else
      have hrow_len_one : cells[location.j].length = 1 := by omega
      rw[hrow_len_one, Nat.sub_self] at hi_eq_right
      simp_rw[hrow_len_one, Nat.sub_self] at hji_eq
      have hsublen_lt_len := Nat.sub_one_lt_of_lt hj_lt_len
      have hj_eq_len : location.j = cells.length - 1 := by
        by_contra hP
        have lowest_notnil := SSYT_row_not_nil hSSYT (cells.length - 1) hsublen_lt_len
        have hzero_lt_len_lowest := List.length_pos_iff.mpr lowest_notnil
        have := SSYT_col_increasing hSSYT 0 location.j (cells.length - 1) (by omega) hsublen_lt_len hzero_lt_len_lowest
        simp only [←hji_eq] at this
        have := SYT_mem_le hSYT 0 (cells.length - 1) hsublen_lt_len hzero_lt_len_lowest
        have := SYT_Nodup hSYT location.j (cells.length - 1) 0 0 hj_lt_len hsublen_lt_len (Nat.zero_lt_of_lt hi_lt_len) hzero_lt_len_lowest (by simp[hP])
        omega
      have hlast_subsize : cells.getLast hnot_nil = [size cells - 1] := by
        simp_rw[List.getLast_eq_getElem, ←hj_eq_len]
        apply List.ext_getElem
        · rw[hrow_len_one, List.length_singleton]
        · intro i _ h₂
          have hi_zero : i = 0 := by
            rw[List.length_singleton] at h₂
            omega
          simp_rw[hi_zero, ←hji_eq, List.getElem_singleton]
      simp[hsingleton]
      rw[size_dropLast cells hnot_nil]
      · rw[(List.Perm.congr_left (entries_dropLastRow cells hnot_nil hlast_subsize))]
        -- code dublication
        have := hSYT.left
        apply List.perm_iff_count.mpr
        intro a
        rw[List.count_erase]
        rw[List.perm_iff_count.mp this a]
        repeat rw[List.count_range]
        if ha_lt_subsize : a < size cells - 1 then
          have ha_neq_size : size cells - 1 ≠ a := by omega
          have ha_lt_size : a < size cells := by omega
          simp[ha_lt_subsize, ha_neq_size, ha_lt_size]
        else if ha_eq_sub_size : a = size cells - 1 then
          have hnot_nil₂ : 0 < size cells := by omega
          simp[ha_eq_sub_size, hnot_nil₂]
        else
          have ha_ge_size : a ≥ size cells := by omega
          have hna_lt_size : ¬a < size cells := by omega
          have hsize_le_succ_a : size cells ≤ a + 1 := by omega
          simp[hna_lt_size, hsize_le_succ_a]
      · simp_rw[List.getLast_eq_getElem, ←hj_eq_len, hrow_len_one]
  · rw[apply_ite IsSSYT]
    apply SSYT_remove (hSSYT)
    split
    · case _ hnot_last_row =>
      by_contra hP
      rw[Nat.not_lt] at hP
      have hi_lt_lensuccj : location.i < cells[location.j + 1].length := by omega
      have hlower_ge := SSYT_col_increasing (hSSYT) location.i location.j (location.j + 1)
        (lt_add_one location.j) hnot_last_row hi_lt_lensuccj
      simp only at hlower_ge
      rw[←location.eq] at hlower_ge
      have := SYT_mem_le hSYT location.i (location.j + 1) hnot_last_row hi_lt_lensuccj
      omega
    · case _ => trivial


example (a b : Nat) (h : a < b) : a ≤ b := by exact Nat.le_of_succ_le h

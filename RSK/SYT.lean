import RSK.OrderedList
import RSK.SSYT
import RSK.Basic
import Mathlib.Tactic


set_option relaxedAutoImplicit true




def IsSYT (cells : Grid) : Prop :=
  -- The entries are 1, 2, ..., n-1 where n is the size
  (entries cells).Perm (List.range (size cells))
  ∧
  IsSSYT cells

instance instDecidableIsSYT (cells : Grid) : Decidable (IsSYT cells) := instDecidableAnd
example : IsSYT [[0, 1, 3], [2], [4]] := by decide

theorem SYT_SSYT (hSYT : IsSYT cells) : IsSSYT cells := hSYT.right

theorem SYT_le_mem (hSYT : IsSYT cells) (k : Nat) (hk : k < size cells) :
  k ∈ entries cells := by
  have hk_in_range : k ∈ List.range (size cells) := List.mem_range.mpr hk
  exact (List.Perm.mem_iff (List.Perm.symm hSYT.left)).mp hk_in_range

theorem SYT_size_mem (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  size cells - 1 ∈ entries cells := by
  have size_pos : size cells > 0 := (SSYT_size_nzero_nnil (SYT_SSYT hSYT)).mpr hnot_nil
  exact SYT_le_mem hSYT (size cells - 1) (Nat.sub_one_lt_of_lt size_pos)

theorem SYT_getElem_le (hSYT : IsSYT cells) (i j : Nat)
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

def SYT_size_location (cells : Grid) (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  location cells (size cells - 1) :=
  entry_location cells (size cells - 1) (SYT_size_mem hSYT hnot_nil)

theorem SYT_size_location_col (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  let location := SYT_size_location cells hSYT hnot_nil
  have := location.hj_lt_len
  location.i = cells[location.j].length - 1 := by
  let location := SYT_size_location cells hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location cells hSYT hnot_nil := by rfl
  simp only
  rw[←hlocation_eq]
  by_contra hP
  have hj_lt_len := location.hj_lt_len
  have hi_lt_len := location.hi_lt_len
  have hsub_i_lt_len : location.i < cells[location.j].length - 1 := by omega
  have hsublen_lt_len : cells[location.j].length - 1 < cells[location.j].length := by omega
  have hrow_inc := SYT_row_increasing hSYT location.i (cells[location.j].length -1)
    location.j hj_lt_len hsub_i_lt_len hsublen_lt_len
  rw[←location.eq] at hrow_inc
  have := SYT_getElem_le hSYT (cells[location.j].length - 1) location.j hj_lt_len hsublen_lt_len
  omega

theorem SYT_size_location_hcol (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  let location := SYT_size_location cells hSYT hnot_nil
  if hsuccj_len : location.j + 1 < List.length cells then
    cells[location.j].length > cells[location.j + 1].length
  else
    True := by
  let location := SYT_size_location cells hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location cells hSYT hnot_nil := by rfl
  simp_rw[←hlocation_eq]
  split
  · case _ hnot_last_row =>
    by_contra hP
    rw[Nat.not_lt] at hP
    have hi_lt_lensuccj : location.i < cells[location.j + 1].length :=
      Nat.lt_of_lt_of_le location.hi_lt_len hP
    have hlower_ge := SSYT_col_increasing (SYT_SSYT hSYT) location.i location.j (location.j + 1)
      (lt_add_one location.j) hnot_last_row hi_lt_lensuccj
    simp only at hlower_ge
    rw[←location.eq] at hlower_ge
    have := SYT_getElem_le hSYT location.i (location.j + 1) hnot_last_row hi_lt_lensuccj
    omega
  · case _ => trivial

@[simp]
def SYT_add_cells (cells : Grid) (j : Nat) : Grid :=
  if hj_le_len : j < cells.length then
    cells.set j (cells[j] ++ [size cells])
  else
    cells ++ [[size cells]]

theorem SYT_add_cells_not_nil :
  SYT_add_cells cells j ≠ [] := by
  rw[SYT_add_cells]
  split
  · case _ hj_lt_len =>
    apply List.length_pos_iff.mp
    rw[List.length_set]
    exact Nat.zero_lt_of_lt hj_lt_len
  · case _ =>
    exact List.concat_ne_nil [size cells] cells

theorem SYT_add (hSYT : IsSYT cells) (j : Nat)
  (h_col :
    if hzero_lt_j_lt_len : 0 < j ∧ j < cells.length then
      cells[j].length < cells[j - 1].length
    else
      True) :
  IsSYT (SYT_add_cells cells j) := by
  have hSSYT := SYT_SSYT hSYT
  rw[SYT_add_cells]
  split
  · case _ hj_lt_len =>
    constructor
    · rw[size_add]
      apply (List.Perm.congr_left (entries_add cells (size cells) j hj_lt_len) _).mpr
      rw[List.range_succ]
      nth_rewrite 1 [←List.singleton_append]
      apply (List.Perm.congr_right List.perm_append_comm _).mp
      apply List.Perm.append
      · trivial
      · exact hSYT.left
    · apply SSYT_append hSSYT j ((size cells))
      · apply wkinc_append_wkinc (SSYT_row_weak hSSYT j hj_lt_len) _
        rw[List.getLast?_eq_some_getLast (SSYT_row_not_nil hSSYT _ _)]
        rw[op_le_some, List.getLast_eq_getElem]
        exact Nat.le_of_succ_le (SYT_getElem_le hSYT _ _ _ _)
      · split
        · trivial
        · exact (SYT_getElem_le hSYT _ _ _ _)
      · if hj : j = 0 then
          exact Or.inl hj
        else
          simp only [Nat.zero_lt_of_ne_zero hj, hj_lt_len, and_self, ↓reduceDIte] at h_col
          exact Or.inr h_col
  · case _ =>
    constructor
    · nth_rewrite 2 [←size_eq_entries_len]
      rw[entries, List.flatten_append, List.flatten_singleton, List.length_append,
        List.length_singleton, List.range_succ, ←entries, size_eq_entries_len]
      exact List.Perm.append hSYT.left (List.singleton_perm_singleton.mpr rfl)
    · apply SSYT_append_row hSSYT (size cells) ?_
      split
      · case _ => trivial
      · case _ hlen_ne_zero =>
        have hsublen_lt_len := Nat.sub_one_lt hlen_ne_zero
        have hnot_nil := SSYT_row_not_nil hSSYT (cells.length - 1) hsublen_lt_len
        have hzero_lt_row := List.length_pos_iff.mpr hnot_nil
        exact SYT_getElem_le hSYT 0 (cells.length - 1) hsublen_lt_len hzero_lt_row


@[simp]
def SYT_remove_cells (cells : Grid) (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) : Grid :=
  let j := (SYT_size_location cells hSYT hnot_nil).j
  have hj := (SYT_size_location cells hSYT hnot_nil).hj_lt_len
  if cells[j].length > 1 then
    cells.set j cells[j].dropLast
  else
    cells.dropLast

theorem SYT_remove (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  IsSYT (SYT_remove_cells cells hSYT hnot_nil) := by
  have hSSYT := SYT_SSYT hSYT
  have size_pos := (SSYT_size_nzero_nnil (hSSYT)).mpr hnot_nil
  have len_pos := List.length_pos_iff.mpr hnot_nil
  simp only [SYT_remove_cells]
  let location := SYT_size_location cells hSYT hnot_nil
  have hlocation_eq : location = SYT_size_location cells hSYT hnot_nil := by rfl
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
      apply (List.Perm.congr_left (entries_remove cells location.j hj_lt_len
        (SSYT_row_not_nil (hSSYT) location.j hj_lt_len)) _).mpr
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
        have := SSYT_col_increasing hSSYT 0 location.j (cells.length - 1)
          (by omega) hsublen_lt_len hzero_lt_len_lowest
        simp only [←hji_eq] at this
        have := SYT_getElem_le hSYT 0 (cells.length - 1) hsublen_lt_len hzero_lt_len_lowest
        have := SYT_Nodup hSYT location.j (cells.length - 1) 0 0
          hj_lt_len hsublen_lt_len (Nat.zero_lt_of_lt hi_lt_len) hzero_lt_len_lowest (by simp[hP])
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
      simp only [hsingleton, ↓reduceIte]
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
    exact SYT_size_location_hcol hSYT hnot_nil

theorem SYT_add_right_inverse (hSYT : IsSYT cells) (hnot_nil : cells ≠ []) :
  SYT_add_cells (SYT_remove_cells cells hSYT hnot_nil)
  (SYT_size_location cells hSYT hnot_nil).j = cells := by
  let loc := SYT_size_location cells hSYT hnot_nil
  have hloc_eq : loc = SYT_size_location cells hSYT hnot_nil := by rfl
  rw[SYT_remove_cells]
  simp_rw[←hloc_eq]
  have hj_lt_len := loc.hj_lt_len
  have hi_lt_len := loc.hi_lt_len
  have hlenj_ne_nil : cells[loc.j] ≠ [] := by
    exact SSYT_row_not_nil (SYT_SSYT hSYT) loc.j hj_lt_len
  have hi_eq := SYT_size_location_col hSYT hnot_nil
  rw[←hloc_eq] at hi_eq
  split
  · case _ =>
    simp_rw[SYT_add_cells, List.length_set, loc.hj_lt_len, reduceDIte]
    apply List.ext_getElem
    · repeat rw[List.length_set]
    · intro i hi_lt_len₁ hi_lt_len₂
      if hi_eq_j : i = loc.j then
        simp_rw[hi_eq_j]
        repeat rw[List.getElem_set_self]
        rw[size_remove (hnot_nil:=hlenj_ne_nil)]
        simp_rw[loc.eq, hi_eq]
        rw[←List.getLast_eq_getElem]
        exact List.dropLast_append_getLast hlenj_ne_nil
      else
        repeat rw[List.getElem_set_ne (Ne.symm hi_eq_j)]
  · case _ hlenj_one₂ =>
    have hlenj_one : cells[loc.j].length = 1 := by
      have := List.length_pos_iff.mpr hlenj_ne_nil
      omega
    simp_rw[hlenj_one, Nat.add_one_sub_one] at hi_eq
    have hj_eq_sublen : loc.j = cells.length - 1 := by
      by_contra hP
      have hj_lt_sublen : loc.j < cells.length - 1 := by omega
      have hsublen_lt_len : cells.length - 1 < cells.length :=
        Nat.sub_one_lt_of_lt hj_lt_len
      have hsublen_length_pos := List.length_pos_iff.mpr
        (SSYT_row_not_nil (SYT_SSYT hSYT) (cells.length - 1) hsublen_lt_len)
      have eq_size := loc.eq
      simp_rw[hi_eq] at eq_size
      have col_inc := SSYT_col_increasing (SYT_SSYT hSYT) 0 loc.j (cells.length - 1)
        hj_lt_sublen hsublen_lt_len hsublen_length_pos
      simp only at col_inc
      rw[←eq_size] at col_inc
      have := SYT_getElem_le hSYT 0 (cells.length - 1) hsublen_lt_len hsublen_length_pos
      omega
    simp_rw[SYT_add_cells, List.length_dropLast, hj_eq_sublen, lt_self_iff_false, reduceDIte]
    simp_rw[hj_eq_sublen] at hlenj_one
    rw[←List.getLast_eq_getElem hnot_nil] at hlenj_one
    rw[size_dropLast cells hnot_nil hlenj_one]
    simp_rw[loc.eq, hi_eq, hj_eq_sublen, ←List.getLast_eq_getElem hnot_nil,
      ←List.eq_getElem_of_length_eq_one (List.getLast cells hnot_nil) hlenj_one,
      List.dropLast_append_getLast]

theorem SYT_size_location_add_cells (hSYT : IsSYT cells) (j : Nat)
  (hj_lt_len : j ≤ cells.length) (h_col) :
  (SYT_size_location (SYT_add_cells cells j) (SYT_add hSYT j h_col) (SYT_add_cells_not_nil)).j = j
  := by
  simp_rw[SYT_size_location, entry_location, SYT_add_cells]
  split
  · case _ hj_lt_len =>
    rw[size_add, Nat.add_sub_self_right]
    refine (List.findIdx_eq ?_).mpr ?_
    · rw[List.length_set]
      exact hj_lt_len
    · constructor
      · rw[List.getElem_set_self, decide_eq_true_iff.mpr]
        exact List.mem_concat_self
      · intro j₂ hj₂_lt_j
        have hj₂_ne_j : j ≠ j₂ := Ne.symm (Nat.ne_of_lt hj₂_lt_j)
        have hj₂_lt_len : j₂ < cells.length := Nat.lt_trans hj₂_lt_j hj_lt_len
        rw[List.getElem_set_ne hj₂_ne_j, decide_eq_false_iff_not, List.mem_iff_getElem]
        apply not_exists_mem.mpr
        intro i hi_lt_len
        exact Nat.ne_of_lt (SYT_getElem_le hSYT i j₂ hj₂_lt_len hi_lt_len)
  · case _ hj =>
    have hj_eq_len : j = cells.length := by omega
    have hj_lt_nlen : j < (cells ++ [[size cells]]).length := by
      rw[List.length_append, List.length_singleton]
      omega
    apply (List.findIdx_eq hj_lt_nlen).mpr
    simp_rw[hj_eq_len]
    rw[size_append, Nat.add_sub_self_right]
    constructor
    · rw[decide_eq_true_iff.mpr]
      rw[List.getElem_append_right (by omega), List.getElem_singleton, List.mem_singleton]
    · intro j₂ hj₂_lt_len
      rw[List.getElem_append_left hj₂_lt_len, decide_eq_false_iff_not, List.mem_iff_getElem,
        not_exists_mem]
      intro i hi_lt_len
      exact Nat.ne_of_lt (SYT_getElem_le hSYT i j₂ hj₂_lt_len hi_lt_len)

theorem SYT_add_left_inverse (hSYT : IsSYT cells) (j : Nat) (hj_le_len : j ≤ cells.length) (h_col) :
  SYT_remove_cells (SYT_add_cells cells j) (SYT_add hSYT j h_col) (SYT_add_cells_not_nil) = cells
  := by
  rw[SYT_remove_cells]
  have := SYT_size_location_add_cells hSYT j hj_le_len h_col
  simp_rw[this]
  simp_rw[SYT_add_cells]
  split
  · case _ hj_lt_len =>
    have hlenj_pos := List.length_pos_iff.mpr (SSYT_row_not_nil (SYT_SSYT hSYT) j hj_lt_len)
    simp [hlenj_pos]
  · case _ hj =>
    have hj_eq_len : j = cells.length := by omega
    simp[hj_eq_len]

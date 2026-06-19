import Mathlib.Tactic
/-
    This file contains some basic statements on basic operations which where useful
    for the proof, but are not in base Lean or mathlib.
-/


-- Changing a row in a grid removes the entries originally in this row and adds the new entries.
theorem count_flatten_set (cells : List (List Nat)) (j a : Nat) (l : List Nat)
  (hj_lt_len : j < cells.length) :
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

-- Given a list l and a number k, The number of k's in l withouth the last entry is equal
-- to the number of k's in l if the last entry of l is not k.
-- Otherwise, it is one less.
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

/-- p is false for all items before findIdx p -/
theorem lt_findIdx_false (l : List α) (p : α → Bool) : ∀(i : Nat) (hi_lt_find : i < l.findIdx p),
  have hi_lt_len := Nat.lt_of_lt_of_le hi_lt_find List.findIdx_le_length
  ¬ p l[i] := by
  intro i hi_lt_find
  have hi_lt_len := Nat.lt_of_lt_of_le hi_lt_find List.findIdx_le_length
  if h_find_eq_len : l.findIdx p = l.length then
    have := List.findIdx_eq_length.mp h_find_eq_len
    have := this l[i] (List.getElem_mem hi_lt_len)
    exact ne_true_of_eq_false this
  else
    have h_find_lt_len : l.findIdx p < l.length :=
      Nat.lt_of_le_of_ne List.findIdx_le_length h_find_eq_len
    have := ((List.findIdx_eq h_find_lt_len).mp (by rfl)).right i hi_lt_find
    exact ne_true_of_eq_false this

-- Given a list with no duplicate entries, and two different indices, the entries at these indices
-- are different.
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

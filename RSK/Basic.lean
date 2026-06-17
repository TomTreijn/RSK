import Mathlib.Tactic

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

import Mathlib.Logic.Function.Basic
import Mathlib.Data.SetLike.Basic
import RSK.Basic
import Mathlib.Tactic
import RSK.OrderedList
import RSK.SSYT

set_option relaxedAutoImplicit true

structure bmpshft_row_in where
  row : List Nat
  h_wkinc : IsWeakInc row
  k : Nat

structure bmpshft_row_out where
  row : List Nat
  h_wkinc : IsWeakInc row
  k' : Option Nat
  h_notnil : row ≠ []
  h_leq : op_lt (row.head h_notnil) k'

-- insert into a row
def bmpshft_row (var : bmpshft_row_in) : bmpshft_row_out :=
  let ⟨row, h_wkinc, k⟩ := var
  let i := row.findIdx? (· > k)
  have i_eq : i = row.findIdx? (· > k) := by rfl
  match hi : i with
  | none =>
    -- Add to the end
    let row' := row ++ [k]
    let k' := none
    have h_wkinc' : IsWeakInc row' := by
      dsimp only [row']
      apply wkinc_append_wkinc
      · exact h_wkinc
      · match hrl : row.getLast? with
        | none => exact op_le_none_l
        | some a =>
          have left_le := List.findIdx?_eq_none_iff.mp (i_eq.symm)
          have ha_in : a ∈ row := List.mem_of_getLast? hrl
          have ha_leq := left_le a ha_in
          rw[decide_eq_false_iff_not, Not] at ha_leq
          exact Option.some_le_some.mpr (Nat.le_of_not_lt ha_leq)
    have h_notnil' : row' ≠ [] := List.concat_ne_nil k row
    have h_leq' : op_lt (row'.head h_notnil') k' := by
      dsimp only [k']
      exact op_lt_none_r
    ⟨row', h_wkinc', k', h_notnil', h_leq'⟩
  | some j =>
    have h_eq_some := List.findIdx?_eq_some_iff_getElem.mp hi
    have h_j_lt_len := h_eq_some.choose
    let row' := row.set j k
    let k' := row[j]
    have hk' : k' = row[j] := by rfl
    have hk_lt_k' : k < k' := by
      rcases h_eq_some with ⟨_, h, _⟩
      rw[←hk', decide_eq_true_eq] at h
      exact h
    have hleft_lt_k : ∀ (i₂ : ℕ) (_ : i₂ < j), row[i₂] ≤ k := by
      rcases h_eq_some with ⟨_, _, h⟩
      intro i₂ hij
      have h_lt := h i₂ hij
      rw[Not, decide_eq_true_eq] at h_lt
      exact Nat.le_of_not_lt h_lt
    have h_notnil : row ≠ [] := by
      by_contra hP
      have h₀ : [].findIdx? (· > k) = none := List.findIdx?_nil
      dsimp only [i] at hi
      rw [←hP] at h₀
      rw [hi] at h₀
      contradiction
    have h_len_gt_zero : 0 < row.length := List.length_pos_iff.mpr h_notnil
    have h_notnil' : row' ≠ [] := by
      dsimp [row']
      rw [←ne_eq]
      have row'len : (row.set (↑j) k).length = row.length := List.length_set
      have row'len_not_zero : (row.set (↑j) k).length > 0 := by rw[row'len]; exact h_len_gt_zero
      exact List.ne_nil_of_length_pos row'len_not_zero
    have h_wkinc' : IsWeakInc row' := by
      dsimp only [row']
      apply wkinc_set_wkinc
      · exact h_wkinc
      · dsimp only [i] at hi
        constructor
        · if hj : j = 0 then
            exact Or.inl hj
          else
            apply Or.inr
            have hsubj_lt_j : j-1 < j := Nat.sub_one_lt hj
            rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt h_j_lt_len)]
            simp only [op_le]
            exact hleft_lt_k (j-1) hsubj_lt_j
        · if hsuccj : j + 1 ≥ row.length then
            rw [List.getElem?_eq_none hsuccj]
            exact op_le_none_r
          else
            apply Nat.lt_of_not_le at hsuccj
            rw[List.getElem?_eq_getElem hsuccj]
            rw[op_le_some]
            have hrow_j_lt_succj : row[j] ≤ row[j+1] :=
              wkinc_wkinc2.mp h_wkinc j (j+1) (lt_add_one j) hsuccj
            rw[←hk'] at hrow_j_lt_succj
            apply Nat.le_of_lt
            exact Nat.lt_of_lt_of_le hk_lt_k' hrow_j_lt_succj
    have h_leq' : op_lt (row'.head h_notnil') k' := by
      rw [op_lt_some]
      rw[List.head_eq_getElem h_notnil']
      have h_row'_get_zero : (row.set 0 k).length > 0 := by
        rw[List.length_set]
        exact h_len_gt_zero
      match hj : j with
      | 0 =>
        dsimp [row']
        simp_rw[hj]
        rw[List.getElem_set_self (h_row'_get_zero)]
        exact hk_lt_k'
      | n + 1 =>
        rw[List.getElem_set_ne]
        · exact Nat.lt_of_le_of_lt (hleft_lt_k 0 (Nat.zero_lt_succ n)) hk_lt_k'
        · have h : j > 0 :=
            by exact Nat.lt_of_sub_eq_succ hj
          exact Nat.ne_zero_of_lt h
    ⟨row', h_wkinc', k', h_notnil', h_leq'⟩

#eval! bmpshft_row ⟨[1, 2, 4, 5], (by simp[IsWeakInc, IsMonotone]), 3⟩
#eval! bmpshft_row ⟨[1, 2, 4, 5], (by simp[IsWeakInc, IsMonotone]), 6⟩

def bmpshft_row_inv (var : bmpshft_row_out) : bmpshft_row_in :=
  let ⟨row', h_wkinc', k', h_notnil', h_leq'⟩ := var
  match k' with
  | none => ⟨row'.dropLast, wkinc_front_wkinc h_wkinc', row'.getLast h_notnil'⟩
  | some k' =>
    let i := row'.findIdx (· ≥ k') - 1
    have hi : i = row'.findIdx (· ≥ k') - 1 := by rfl
    have hi_lt_len : i < row'.length := by
      grind
    let row := row'.set i k'
    let k := row'[i]
    have h_wkinc : IsWeakInc row := by
      apply wkinc_set_wkinc
      · exact h_wkinc'
      · have hfind_gt_zero : row'.findIdx (· ≥ k') > 0 := by
          by_contra hP
          have his_zero := Nat.eq_zero_of_not_pos hP
          rw[List.findIdx_eq] at his_zero
          · have hge := his_zero.left
            rw [decide_eq_true_iff] at hge
            rw [op_lt_some, List.head_eq_getElem] at h_leq'
            omega
          · exact List.length_pos_iff.mpr h_notnil'
        have hfind_i : i + 1 = row'.findIdx (· ≥ k') := Nat.sub_add_cancel hfind_gt_zero
        have sub_i_lt_len : i - 1 < row'.length := Nat.sub_lt_of_lt hi_lt_len
        rw[(List.getElem?_eq_some_getElem_iff (sub_i_lt_len)).mpr True.intro, op_le_some]
        if hfind : row'.findIdx (· ≥ k') = row'.length then
          constructor
          · simp_rw[List.findIdx_eq_length, decide_eq_false_iff_not] at hfind
            apply Or.intro_right
            have lt := hfind row'[i-1] (List.getElem_mem sub_i_lt_len)
            exact Nat.le_of_not_ge lt
          · rw[hfind] at hi
            rw[hi, Nat.sub_one_add_one, List.getElem?_eq_none_iff.mpr (Nat.le_refl row'.length)]
            · exact op_le_none_r
            · exact Nat.ne_zero_of_lt hi_lt_len
        else
          have hsucc_i_lt_len : i + 1 < row'.length := by
            grind
          have hfind_eq := (List.findIdx_eq hsucc_i_lt_len).mp (Eq.symm hfind_i)
          constructor
          · apply Or.intro_right
            have le := hfind_eq.right (i-1) (Nat.sub_lt_succ i 1)
            rw [decide_eq_false_iff_not] at le
            exact Nat.le_of_not_ge le
          · rw[(List.getElem?_eq_some_getElem_iff (hsucc_i_lt_len)).mpr True.intro, op_le_some]
            have le := hfind_eq.left
            rw[decide_eq_true_iff] at le
            omega
    ⟨row, h_wkinc, k⟩


example {a : Nat} (h : ¬a > 0) : (a = 0) := Nat.eq_zero_of_not_pos h
example {a b : Nat} (h : a ≤ b) : (b ≥ a) := by exact String.Pos.Raw.mk_le_mk.mp h
#eval! bmpshft_row_inv ⟨[1, 2, 4, 5],
  (by simp[IsWeakInc, IsMonotone]), none, (by simp), (op_lt_none_r)⟩
#eval! bmpshft_row_inv ⟨[1, 2, 4, 5],
  (by simp[IsWeakInc, IsMonotone]), some 5, (by simp), (by rw[op_lt_some]; decide)⟩

theorem bmpshft_row_left_inverse : Function.LeftInverse bmpshft_row_inv bmpshft_row := by
  apply Function.leftInverse_iff_comp.mpr
  apply funext
  intro var
  let ⟨row, h_wkinc, k⟩ := var
  dsimp only [id_eq, Function.comp_apply]
  rw[bmpshft_row]
  split
  -- If nothing is bumped out
  · case h_1 =>
      rw[bmpshft_row_inv]
      grind
  -- If something is bumped out
  · case h_2 _ j h_some_j _ _ _ =>
      rw[bmpshft_row_inv]
      have h_eq_some := List.findIdx?_eq_some_iff_getElem.mp (Eq.symm h_some_j)
      rcases h_eq_some with ⟨hj_lt_len, hrowj_gt, hleft_row_lt⟩
      rw[decide_eq_true_iff] at hrowj_gt
      have hleft_lt_k : ∀ (i₂ : ℕ) (_ : i₂ < j), row[i₂] ≤ k := by
        intro i₂ hij
        have h_lt := hleft_row_lt i₂ hij
        rw[Not, decide_eq_true_eq] at h_lt
        exact Nat.le_of_not_lt h_lt
      -- Proof that bmpshft_row and bmpshft_row_inv manipulate the same element
      have set_set : (List.findIdx (· ≥ row[j])) (row.set j k) - 1 = j := by
        have hj := (List.findIdx?_eq_some_iff_findIdx_eq.mp (Eq.symm h_some_j)).right
        refine Eq.symm (Nat.eq_sub_of_add_eq' ?_)
        apply Eq.symm
        -- If bmpshft_row manipulated the last element
        -- We have to prove that row' is less than k
        if h_succj : 1 + j = (row.set j k).length then
          rw [h_succj, List.findIdx_eq_length_of_false]
          intro x hx
          rw [decide_eq_false_iff_not]
          have ⟨i, hi_lt_len, hx_getElem⟩ := List.mem_iff_getElem.mp hx
          if hi_eq_j : i = j then
            simp_rw[←hx_getElem, hi_eq_j, List.getElem_set_self, Nat.not_ge_eq]
            exact Order.add_one_le_iff.mpr hrowj_gt
          else
            have hi_lt_j : i < j := by
              rw [←h_succj] at hi_lt_len
              have hi_le_j : i ≤ j := Nat.lt_one_add_iff.mp hi_lt_len
              exact Nat.lt_of_le_of_ne hi_le_j hi_eq_j
            have := Ne.symm (Nat.ne_of_lt hi_lt_j)
            rw [List.getElem_set_of_ne this k hi_lt_len] at hx_getElem
            have hx_le_k : x ≤ k := by
              have hleft := hleft_lt_k i hi_lt_j
              rw[hx_getElem] at hleft
              exact hleft
            omega
        -- If bmpshft_row manipulated another element at j
        -- We have to prove that row'[i] ≤ k for row[i] ≤ j, and greater than k for j+1
        else
          rw [List.findIdx_eq]
          constructor
          · rw[decide_eq_true_eq, List.getElem_set_ne]
            · have hsuccj_lt_len : 1 + j < row.length := by
                rw[List.length_set] at h_succj
                omega
              exact wkinc_wkinc2.mp h_wkinc j (1+j) (lt_one_add j) hsuccj_lt_len
            · rw[Nat.add_comm]
              exact Nat.ne_add_one j
          · grind
          · rw [List.length_set]
            rw [List.length_set] at h_succj
            have hsuccj_le_len : j + 1 ≤ row.length := Order.add_one_le_iff.mpr hj_lt_len
            rw[Nat.add_comm] at hsuccj_le_len
            exact Nat.lt_of_le_of_ne hsuccj_le_len h_succj
      -- Using the fact that both manipulate the same data, the rest follows.
      simp_rw [set_set]
      rw[List.getElem_set_self]
      have rows_eq : (row.set j k).set j row[j] = row := by
        apply List.ext_getElem
        · repeat rw [List.length_set]
        · intro i h₁ h₂
          if h_i : i = j then
            simp_rw[h_i]
            rw [List.getElem_set_self]
          else
            have h_j_neq_i : j ≠ i := by exact Ne.symm (Ne.intro h_i)
            repeat rw [List.getElem_set_ne (h_j_neq_i)]
      simp_rw[rows_eq]

theorem bmpshft_row_right_inverse : Function.RightInverse bmpshft_row_inv bmpshft_row := by
  apply Function.rightInverse_iff_comp.mpr
  refine Eq.symm (funext ?_)
  intro ⟨row', h_wkinc', k', h_notnil', h_leq'⟩
  rw [Function.comp_apply, bmpshft_row_inv.eq_def]
  simp only [id_eq]
  split
  -- If k' = none
  · case h_1 k' _ _ =>
    rw [bmpshft_row]
    have none_find_none : List.findIdx? ((· > row'.getLast h_notnil')) row'.dropLast = none :=
    by
      apply List.findIdx?_eq_none_iff.mpr
      intro x hx_in_row'
      have ⟨i, hi_lt_len, hx_getElem⟩ := List.mem_iff_getElem.mp hx_in_row'
      have row_len_lt : row'.length - 1 < row'.length := by
        have := List.length_pos_of_ne_nil h_notnil'; omega
      have hi_lt_len' : i < row'.length - 1 := by
        rw[List.length_dropLast] at hi_lt_len
        exact hi_lt_len
      rw[←List.getElem_length_sub_one_eq_getLast row_len_lt]
      rw[List.getElem_dropLast hi_lt_len] at hx_getElem
      rw[←hx_getElem]
      rw[decide_eq_false_iff_not, Nat.not_gt_eq]
      exact wkinc_wkinc2.mp h_wkinc' i (row'.length - 1) hi_lt_len' row_len_lt
    -- Should be replaced with a variant of rw[k'_find_k]
    split
    · case h_1 =>
      simp only [bmpshft_row_out.mk.injEq, and_true]
      exact Eq.symm (List.dropLast_concat_getLast h_notnil')
    · case h_2 find_eq_some _ _=>
        rw [none_find_none] at find_eq_some
        contradiction
  -- if k' = some
  · case h_2 k' h_leq' =>
    let j' := (List.findIdx (· ≥ k') row' - 1)
    have hj'_eq : (List.findIdx (· ≥ k') row' - 1) = j' := by rfl
    simp_rw [hj'_eq]
    rw [bmpshft_row]
    simp only
    have find_gt_zero : List.findIdx (· ≥ k') row' > 0 := by
      apply Nat.zero_lt_of_ne_zero
      by_contra h_cont
      rw[List.findIdx_eq (List.length_pos_iff.mpr h_notnil')] at h_cont
      rw [op_lt_some, List.head_eq_getElem] at h_leq'
      have h_cont_left := h_cont.left
      rw[decide_eq_true_iff] at h_cont_left
      omega
    have hj'_le_len : j' < row'.length := by
      rw[←hj'_eq]
      exact Nat.sub_one_lt_of_le find_gt_zero List.findIdx_le_length
    have j_find_j : List.findIdx? (· > row'[j']) (row'.set j' k') = some j' := by
      rw[List.findIdx?_eq_some_iff_getElem]
      simp_rw[List.length_set]
      if hfind_eq_len : List.findIdx (· ≥ k') row' = row'.length then
        have none_gt := List.findIdx_eq_length.mp hfind_eq_len
        apply Exists.intro
        · constructor
          · rw[List.getElem_set_self, decide_eq_true_iff]
            have gt := none_gt row'[j'] (List.getElem_mem hj'_le_len)
            rw[decide_eq_false_iff_not] at gt
            exact Nat.lt_of_not_le gt
          · intro j hji
            rw[decide_eq_true_iff]
            rw[List.getElem_set_ne]
            · have lt : row'[j] ≤ row'[j'] := wkinc_wkinc2.mp h_wkinc' j j' hji hj'_le_len
              refine Nat.not_lt.mpr lt
            · exact Ne.symm (Nat.ne_of_lt hji)
        · exact hj'_le_len
      else
        have find_eq_succ_j : List.findIdx (· ≥ k') row' = j' + 1 :=
          (Nat.sub_eq_iff_eq_add find_gt_zero).mp hj'_eq
        have succ_j_lt_len : j' + 1 < row'.length := by
          rw[←find_eq_succ_j]
          exact Nat.lt_of_le_of_ne List.findIdx_le_length hfind_eq_len
        have find_eq := (List.findIdx_eq succ_j_lt_len).mp find_eq_succ_j
        have left_row_lt := find_eq.right
        apply Exists.intro
        · constructor
          · rw [List.getElem_set_self]
            have k_gt := left_row_lt j' (lt_add_one j')
            rw [decide_eq_false_iff_not] at k_gt
            rw [decide_eq_true_iff]
            omega
          · intro j hji
            rw[decide_eq_true_iff, List.getElem_set_ne]
            · refine Nat.not_lt.mpr ?_
              exact wkinc_wkinc2.mp h_wkinc' j j' hji hj'_le_len
            · exact Ne.symm (Nat.ne_of_lt hji)
        · exact hj'_le_len
    split
    · case h_1 =>
      grind
    · case h_2 j'₂ _ find_eq_some _ _=>
      rw [j_find_j] at find_eq_some
      have j'₂_eq_j' : j'₂ = j' := ENat.coe_inj.mp find_eq_some
      -- Basically the same as the left inverse, should be factored out
      simp_rw [j'₂_eq_j', List.getElem_set_self]
      have rows_eq : (row'.set j' k').set j' row'[j'] = row' := by
        apply List.ext_getElem
        · repeat rw [List.length_set]
        · intro i h₁ h₂
          if h_i : i = j' then
            simp_rw[h_i]
            rw [List.getElem_set_self]
          else
            have h_j_neq_i : j' ≠ i := by exact Ne.symm (Ne.intro h_i)
            repeat rw [List.getElem_set_ne (h_j_neq_i)]
      simp_rw[rows_eq]

theorem bmpshft_row_bi : Function.Bijective bmpshft_row := by
  apply Function.bijective_iff_has_inverse.mpr
  have is_inv : Function.LeftInverse bmpshft_row_inv bmpshft_row ∧
    Function.RightInverse bmpshft_row_inv bmpshft_row :=
      ⟨bmpshft_row_left_inverse, bmpshft_row_right_inverse⟩
  exact Exists.intro bmpshft_row_inv is_inv

example (a b : Nat) (h_1 : a ≤ b) (h_2 : ¬a = b) : (a < b):= by exact Nat.lt_of_le_of_ne h_1 h_2
example (a b : Nat) (h_1 : some a = some b) : (a = b) := by exact ENat.coe_inj.mp h_1
example (a b : Nat) : (a < b) = (b > a) := by exact Eq.propIntro (fun a ↦ a) fun a ↦ a

structure bmpshft_row_full_in where
  cells : Grid
  hSSYT : IsSSYT cells
  k : Nat
  j : Nat
  hj_le_len : j ≤ cells.length
  h_col :
    if hj : j = 0 then
      True
    else
      if hj_lt_len : j < cells.length then
        have := diagram_decreasing hSSYT (j - 1) j (Nat.sub_one_lt hj) hj_lt_len
        -- There is an element in the row above, which
        -- a) is smaller than k and
        -- b) the number below is larger than k.
        ∃ (i : Nat) (hi_lt_lensubj : i < cells[j - 1].length), cells[j - 1][i] < k ∧
          if hi_lt_lenj : i < cells[j].length then
            cells[j][i] > k
          else
            True
      else
        have := List.length_pos_of_ne_nil (hSSYT.left (j - 1) (by omega)).right
        cells[j - 1][0] < k

structure bmpshft_row_full_out where
  cells : Grid
  hSSYT : IsSSYT cells
  k' : Option Nat
  j : Nat
  hj_lt_len : j < cells.length
  h_col :
    match k' with
      | none =>
        -- Just the assertions that if we remove an element, it stays an Young diagram
        if hj : j + 1 < cells.length then
          cells[j + 1].length < cells[j].length
        else
          True
      | some k' =>
        ∃ (i : Nat) (hi_lt_len : i < cells[j].length), cells[j][i] < k' ∧
          if hj : j + 1 < cells.length then
            have := diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hj
            if hi_lt_len : i < cells[j + 1].length then
              cells[j + 1][i] > k'
            else
              True
          else
            True

def bmpshft_row_full (var : bmpshft_row_full_in) : bmpshft_row_full_out :=
  have ⟨cells, hSSYT, k, j, hj_le_len, h_col⟩ := var
  if hj_lt_len : j < cells.length then
    let var_in : bmpshft_row_in := ⟨cells[j], (hSSYT.left j hj_lt_len).left, k⟩
    let var_out := bmpshft_row var_in
    have hvar_out_eq : var_out = bmpshft_row var_in := by rfl
    ⟨cells.set j var_out.row,
      -- The result is an SSYT
      by
        simp [hj_lt_len] at h_col
        simp only[bmpshft_row, var_in] at hvar_out_eq
        split at hvar_out_eq
        · case h_1 h_found _ =>
          simp only [hvar_out_eq]
          have wk_inc : IsWeakInc (cells[j] ++ [k]) := by
            have wk_inc := var_out.h_wkinc
            simp only [hvar_out_eq] at wk_inc
            exact wk_inc
          if hj : j = 0 then
            apply SSYT_append hSSYT
            · exact wk_inc
            · simp[hj]
            · simp[hj]
          else
            simp[hj] at h_col
            let ⟨i, hEsubji_lt_k, hji_gt_k⟩ := h_col
            let ⟨hi_lt_len_subj, hsubji_lt_k⟩ := hEsubji_lt_k
            have hi_gt_lenj : i ≥ cells[j].length := by
              by_contra hP
              have i_lt_len : i < cells[j].length := Nat.lt_of_not_le hP
              have h_k_lt := hji_gt_k (i_lt_len)
              have h_all_ge := List.findIdx?_eq_none_iff.mp h_found
              have h_k_ge := h_all_ge cells[j][i] (List.getElem_mem i_lt_len)
              simp at h_k_ge
              omega
            apply SSYT_append hSSYT
            · exact wk_inc
            · simp only [hj, ↓reduceDIte]
              if hi : i = cells[j].length then
                simp_rw[←hi]
                exact hsubji_lt_k
              else
                have hsubj_le_subji := SSYT_row_increasing hSSYT cells[j].length i (j-1)
                  (Nat.sub_lt_of_lt hj_lt_len) (by omega) (Nat.lt_of_succ_le hi_lt_len_subj)
                exact Nat.lt_of_le_of_lt hsubj_le_subji hsubji_lt_k
            · apply Or.intro_right
              omega
        · case h_2 i h_found _ _ _ =>
          simp only[hvar_out_eq]
          have ⟨hi_lt_len, find⟩ := List.findIdx?_eq_some_iff_findIdx_eq.mp (Eq.symm h_found)
          apply SSYT_set hSSYT
          · have wk_inc := var_out.h_wkinc
            simp only [hvar_out_eq] at wk_inc
            exact wk_inc
          · if hj : j = 0 then
              simp[hj]
            else
              simp only [hj, ↓reduceDIte]
              simp [hj] at h_col
              have ⟨i₂, hE_jsubi_lt_k, hk_lt_ji⟩ := h_col
              have ⟨hi₂_lt_subjlen, h_subji_lt_k⟩ := hE_jsubi_lt_k
              have hi_le_i₂ : i ≤ i₂ := by
                by_contra hP
                have hi₂_lt_i : i₂ < i := Nat.lt_of_not_le hP
                have hi₂_lt_len : i₂ < cells[j].length := Nat.lt_trans hi₂_lt_i hi_lt_len
                have hk_ge_ji₂ := ((List.findIdx_eq hi_lt_len).mp find).right i₂ hi₂_lt_i
                have hk_lt_ji₂ := hk_lt_ji hi₂_lt_len
                simp at hk_ge_ji₂
                omega
              if hi₂ : i₂ = i then
                simp_rw[hi₂] at h_subji_lt_k
                exact h_subji_lt_k
              else
                have hi_lt_i₂ : i < i₂ := by omega
                have := SSYT_row_increasing hSSYT i i₂ (j - 1)
                  (Nat.sub_lt_of_lt hj_lt_len) hi_lt_i₂ hi₂_lt_subjlen
                omega
          · if hj : j + 1 < List.length cells then
              simp[hj]
              if hi : i < cells[j + 1].length then
                simp[hi]
                have hji_gt_k := ((List.findIdx_eq hi_lt_len).mp find).left
                simp at hji_gt_k
                have := SSYT_col_increasing hSSYT i j (j + 1) (lt_add_one j) hj hi
                simp only at this
                omega
              else
                simp[hi]
            else
              simp[hj]
          · exact hi_lt_len
          · exact hSSYT
      , var_out.k'
      , j
      , by rw[List.length_set]; exact hj_lt_len
      ,
      -- The requirements for it to be invertable.
      by
        simp only[bmpshft_row] at hvar_out_eq
        split at hvar_out_eq
        · case h_1 h_1 h_found _ =>
          simp only [var_in] at hvar_out_eq
          simp only [hvar_out_eq]
          if hsuccj_lt_len : j + 1 < cells.length then
            simp [hsuccj_lt_len]
            exact diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hsuccj_lt_len
          else
            simp_rw[List.length_set]
            simp[hsuccj_lt_len]
        · case h_2 i h_found _ _ _ =>
          simp only [var_in] at hvar_out_eq
          simp only [var_in] at h_found
          simp only [hvar_out_eq]
          have ⟨hi_lt_len, hrowi_gt_k, _⟩ := List.findIdx?_eq_some_iff_getElem.mp (Eq.symm h_found)
          if hsuccj_lt_len : j + 1 < cells.length then
            simp [hsuccj_lt_len]
            exact ⟨i, ⟨
                ⟨
                  hi_lt_len,
                  by
                    simp only [decide_eq_true_eq] at hrowi_gt_k
                    rw[List.getElem_set_self]
                    exact hrowi_gt_k
                ⟩,
                by
                  intro hi_lt_len_succj
                  exact SSYT_col_increasing hSSYT i j (j + 1)
                    (lt_add_one j) hsuccj_lt_len hi_lt_len_succj
              ⟩
            ⟩
          else
            simp_rw[List.length_set]
            have ⟨i_lt_len, find, _⟩ := List.findIdx?_eq_some_iff_getElem.mp (Eq.symm h_found)
            rw [decide_eq_true_eq] at find
            simp [hsuccj_lt_len]
            exact ⟨i, i_lt_len, by rw[List.getElem_set_self]; exact find⟩
    ⟩
  else
    ⟨cells ++ [[k]],
      by
        apply SSYT_append_row hSSYT
        · have hj : j = cells.length := by omega
          if h_len : cells.length = 0 then
            simp[h_len]
          else
            simp[hj, h_len] at h_col
            simp[h_col]
      ,
      none,
      j,
      by
        rw[List.length_append]
        exact Nat.lt_succ_of_le hj_le_len,
      by
        simp[hj_lt_len]
    ⟩

theorem switch_if {α : Type} {a : Bool} {b c : α} {p : α → Prop} :
  p (if a then b else c) = if a then p b else p c := apply_ite p (a = true) b c


def bmpshft_row_inv_full (var : bmpshft_row_full_out) : bmpshft_row_full_in :=
  have ⟨cells, hSSYT, k', j , hj_lt_len, h_col⟩ := var
  let var_out : bmpshft_row_out := ⟨
    cells[j],
    (hSSYT.left j hj_lt_len).left,
    k',
    (hSSYT.left j hj_lt_len).right,
    by
      match k' with
      | none => exact op_lt_none_r
      | some k' =>
        rw[op_lt_some, List.head_eq_getElem]
        simp at h_col
        have ⟨i, ⟨⟨hi_lt_len, hcellsji_lt_k'⟩, _⟩⟩ := h_col
        if hi : i = 0 then
          simp_rw[hi] at hcellsji_lt_k'
          exact hcellsji_lt_k'
        else
          have := SSYT_row_increasing hSSYT 0 i j hj_lt_len (by omega) hi_lt_len
          omega
  ⟩

  let var_in := bmpshft_row_inv var_out
  have hvar_in_eq : var_in = bmpshft_row_inv var_out := by rfl

  ⟨
    if var_in.row.length > 0 then
      cells.set j var_in.row
    else
      cells.dropLast
   ,
    by
      simp only [bmpshft_row_inv, var_out] at hvar_in_eq
      split at hvar_in_eq
      · case h_1 =>
        simp only [dite_else_true] at h_col
        simp only [hvar_in_eq]
        rw [apply_ite IsSSYT, List.length_dropLast]
        simp_rw [gt_iff_lt, Nat.sub_pos_iff_lt (m:=1) (n:=cells[j].length)]
        apply SSYT_remove hSSYT
        · if hsuccj_len : j + 1 < List.length cells then
            simp[hsuccj_len, h_col]
          else
            simp[hsuccj_len]
      · case h_2 k' hk'_gt_head =>
        simp only [dite_else_true] at h_col
        have h_lenj_gt_zero := List.length_pos_of_ne_nil (hSSYT.left j hj_lt_len).right
        simp only [hvar_in_eq]
        rw[List.length_set]
        simp only [h_lenj_gt_zero, ↓reduceIte]
        apply SSYT_set hSSYT
        · have h_wkinc := var_in.h_wkinc
          simp only[hvar_in_eq] at h_wkinc
          exact h_wkinc
        · sorry
        · split
          · case _ hsuccj_lt_len =>
            split
            · case _ hi_lt_len =>
              sorry
            · case _ => exact True.intro
          · case _ => exact True.intro
        · have := List.findIdx_le_length (xs:=cells[j]) (p:=(· ≥ k'))
          omega
        · exact hSSYT
    ,
    var_in.k,
    j,
    by
    split
    · case _ =>
      rw[List.length_set]
      exact Nat.le_of_succ_le hj_lt_len
    · case _ =>
      rw[List.length_dropLast]
      exact Nat.le_sub_one_of_lt hj_lt_len
    ,
    sorry
  ⟩

theorem switch_bmpshft_row_var_out {var_in h_wkinc h_notnil h_leq} :
  (⟨(bmpshft_row var_in).row,
    h_wkinc,
    (bmpshft_row var_in).k',
    h_notnil,
    h_leq⟩ : bmpshft_row_out) = bmpshft_row var_in := by
  rfl

theorem switch_bmpshft_row_inv_var_in :
  (⟨(bmpshft_row_inv var_out).row,
    h_wkinc,
    (bmpshft_row_inv var_out).k⟩ : bmpshft_row_in) = bmpshft_row_inv var_out := by
  rfl

theorem bmpshft_row_full_left_inverse :
  Function.LeftInverse bmpshft_row_inv_full bmpshft_row_full := by
  apply Function.leftInverse_iff_comp.mpr
  apply funext
  intro ⟨cells, hSSYT, k, j, _, _⟩
  rw[Function.comp_apply, bmpshft_row_full.eq_def]
  simp
  split
  · case _ hj_lt_len =>
    rw[bmpshft_row_inv_full]
    simp
    rw[bmpshft_row_left_inverse]
    simp
    intro hcellj_eq_nil
    have := (hSSYT.left j hj_lt_len).right
    contradiction
  · case _ h_ge_len =>
    have hj : j = cells.length := by omega
    simp_rw[bmpshft_row_inv_full, hj]
    have getLast : (cells ++ [[k]])[cells.length] = [k] := by
      rw[List.getElem_append_right (Nat.le_refl cells.length)]
      simp_rw[Nat.sub_self, List.getElem_singleton]
    simp_rw[getLast]
    simp[bmpshft_row_inv]

theorem bmpshft_row_full_right_inverse :
  Function.RightInverse bmpshft_row_inv_full bmpshft_row_full := by
  apply Function.leftInverse_iff_comp.mpr
  apply funext
  intro ⟨cells, hSSYT, k', j, hj_lt_len, hcol⟩
  rw[Function.comp_apply, bmpshft_row_inv_full.eq_def]
  simp
  split
  · case _ =>
    rw[bmpshft_row_full]
    simp[switch_bmpshft_row_inv_var_in, hj_lt_len]
    rw[bmpshft_row_right_inverse]
    simp only [List.set_getElem_self, and_self]
  · case _ hlen_row_zero =>
    rw[bmpshft_row_inv.eq_def] at hlen_row_zero
    simp at hlen_row_zero
    split at hlen_row_zero
    · case _ =>
      simp at hcol
      simp only at hlen_row_zero
      have h_notnil := (hSSYT.left j hj_lt_len).right
      have h_lenj : cells[j].length = 1 := by
        have h_cellsj_len : cells[j].length > 0 := List.length_pos_of_ne_nil h_notnil
        have h_lendropLast : cells[j].dropLast.length = 0 := by
          rw[hlen_row_zero]
          exact List.length_nil
        rw[List.length_dropLast] at h_lendropLast
        omega
      have ⟨a, ha_eq⟩ := List.length_eq_one_iff.mp h_lenj
      have hj : j + 1 = cells.length := by
        by_contra hP
        have hsuccj_lt_len : j + 1 < cells.length := Nat.lt_of_le_of_ne hj_lt_len hP
        have lijk := hcol hsuccj_lt_len
        have lijkop : cells[j+1].length > 0 :=
          List.length_pos_of_ne_nil (hSSYT.left (j+1) hsuccj_lt_len).right
        omega
      have hj₂ : j = cells.length - 1 := Nat.eq_sub_of_add_eq hj
      have hj₃ : ¬j < cells.length - 1 := Eq.not_gt (Eq.symm hj₂)
      have hcells_notnil : cells ≠ [] := List.ne_nil_of_length_eq_add_one (Eq.symm hj)
      simp[bmpshft_row_full, List.length_dropLast, hj₃, ha_eq, bmpshft_row_inv]
      simp_rw[←ha_eq, hj₂, ←List.getLast_eq_getElem hcells_notnil]
      exact List.dropLast_concat_getLast hcells_notnil
    · case _ =>
      simp at hlen_row_zero
      have := (hSSYT.left j hj_lt_len).right
      contradiction

theorem bmpshft_row_bi_full : Function.Bijective bmpshft_row_full := by
  apply Function.bijective_iff_has_inverse.mpr
  have is_inv : Function.LeftInverse bmpshft_row_inv_full bmpshft_row_full ∧
    Function.RightInverse bmpshft_row_inv_full bmpshft_row_full := by
    constructor
    · exact bmpshft_row_full_left_inverse
    · exact bmpshft_row_full_right_inverse
  exact Exists.intro bmpshft_row_inv_full is_inv

structure bmpshft_in where
  cells : Grid
  hSSYT : IsSSYT cells
  k : Nat

structure bmpshft_out where
  cells : Grid
  hSSYT : IsSSYT cells
  j : Nat
  hj_lt_len : j < cells.length
  hend_col : (h : j + 1 < cells.length) → cells[j].length > cells[j+1].length

def bmpshft_ind (var : bmpshft_row_full_in) : bmpshft_out :=
  let var_out := bmpshft_row_full var
  have hvar_out_eq : var_out = bmpshft_row_full var := by rfl
  match hk : var_out.k' with
  | none =>
    ⟨var_out.cells, var_out.hSSYT, var_out.j, var_out.hj_lt_len, by
      have h_col := var_out.h_col
      simp only [hk, dite_else_true] at h_col
      exact h_col⟩
  | some k =>
    bmpshft_ind ⟨var_out.cells,
      var_out.hSSYT,
      k,
      var_out.j + 1,
      var_out.hj_lt_len,
      by
        have h_col := var_out.h_col
        simp only [hk, dite_else_true, exists_and_right] at h_col
        simp
        split
        · case _ hsuccj_lt_len =>
          simp [hsuccj_lt_len] at h_col
          exact h_col
        · case _ hsuccj_eq_len =>
          have ⟨i, ⟨hi_lt_len, hji_lt_k⟩, _⟩ := h_col
          if hi : i = 0 then
            simp_rw[←hi]
            exact hji_lt_k
          else
            have hi_pos : i > 0 := by omega
            have h_inc := SSYT_row_increasing var_out.hSSYT 0 i var_out.j var_out.hj_lt_len hi_pos hi_lt_len
            exact Nat.lt_of_le_of_lt h_inc hji_lt_k
        ⟩
  termination_by var.cells.length - var.j
  decreasing_by
    rw[bmpshft_row_full]
    split
    · case _ =>
      simp
      omega
    · case _ hj_eq_len =>
      simp[hvar_out_eq, bmpshft_row_full, hj_eq_len] at hk

def bmpshft_ind_inv (var : bmpshft_row_full_out) : bmpshft_in :=
  let var_in := bmpshft_row_inv_full var
  have hvar_in_eq : var_in = bmpshft_row_inv_full var := by rfl
  match hj : var_in.j with
  | 0 => ⟨var_in.cells, var_in.hSSYT, var_in.k⟩
  | j₂ + 1 =>
    have hj₂_lt_len : j₂ < var_in.cells.length := by
      have := var_in.hj_le_len
      omega
    bmpshft_ind_inv ⟨var_in.cells,
      var_in.hSSYT,
      var_in.k,
      j₂,
      hj₂_lt_len,
      by
        simp
        have h_col := var_in.h_col
        simp [hj] at h_col
        split at h_col
        · case _ hsuccj₂_lt_len =>
          simp[hsuccj₂_lt_len, h_col]
        · case _ hnotsuccj₂_lt_len =>
          simp[hnotsuccj₂_lt_len]
          have hlenj₂_pos := List.length_pos_iff_ne_nil.mpr
            ((var_in.hSSYT.left j₂ hj₂_lt_len).right)
          exact ⟨0, ⟨hlenj₂_pos, h_col⟩⟩
        ⟩
  termination_by var.j
  decreasing_by
    simp [hvar_in_eq, bmpshft_row_inv_full] at hj
    omega

def bmpshft (var : bmpshft_in) : bmpshft_out :=
  bmpshft_ind ⟨var.cells,
    var.hSSYT,
    var.k,
    0,
    by exact Nat.zero_le (var.cells.length),
    by simp only [↓reduceDIte]
  ⟩

def bmpshft_inv (var : bmpshft_out) : bmpshft_in :=
  bmpshft_ind_inv ⟨
    var.cells,
    var.hSSYT,
    none,
    var.j,
    var.hj_lt_len,
    by simp only [var.hend_col, dite_eq_ite, ite_self]
  ⟩

theorem switch_var_out :
  (⟨(bmpshft_ind var_in).cells,
    hSSYT,
    (bmpshft_ind var_in).j,
    hj_lt_len,
    hend_col⟩ : bmpshft_out) = bmpshft_ind var_in := by
  rfl

theorem bmpshft_ind_one : bmpshft_ind ⟨top :: rest, hSSYT, k, 1, hj_le_len, h_col⟩ = ⟨top::(bmpshft ⟨rest, sorry, k⟩).cells, a, (bmpshft ⟨rest, sorry, k⟩).j, b, c⟩ := by
  simp_rw[bmpshft]
  simp (config := { singlePass := true }) [bmpshft_ind]
  simp [bmpshft_row_full]
  sorry

theorem bmpshft_left_inverse (var : bmpshft_in) : bmpshft_inv (bmpshft var) = var := by
  have ⟨cells, hSSYT, k⟩ := var
  match cells with
  | [] =>
    rw[bmpshft, bmpshft_ind]
    simp_rw[bmpshft_row_full]
    simp only [List.length_nil, lt_self_iff_false, ↓dreduceDIte, List.nil_append, ↓reduceDIte]
    rw[bmpshft_inv, bmpshft_ind_inv]
    simp_rw[bmpshft_row_inv_full, bmpshft_row_inv]
    simp
  | top :: rest =>
    rw[bmpshft, bmpshft_ind]
    simp_rw[bmpshft_row_full]
    simp
    split
    · case _ hisNone =>
        rw[bmpshft_inv, bmpshft_ind_inv]
        simp_rw[bmpshft_row_inv_full]
        simp
        simp_rw[←hisNone]
        rw[switch_bmpshft_row_var_out]
        rw[bmpshft_row_left_inverse]
        have htop_ne_nil : top ≠ [] := (hSSYT.left 0 (Nat.zero_lt_succ rest.length)).right
        simp[htop_ne_nil]
    · case _ k' isSome =>
        rw[bmpshft_ind]
        simp_rw[bmpshft_row_full]
        simp


    sorry



variable (a b c : Nat)

example : a < b ↔ b > a := by exact gt_iff_lt

example (a : Nat) : a ≠ a + 1 := by exact Nat.ne_add_one a
variable (h1 : a = b) (h2 : b = c)

#check congrArg (fun _a ↦ _a = c) h1

example (a b c : Nat) (h1 : a = b) (h2 : b = c) := Eq.mp (congrArg (fun _a ↦ _a = c) (Eq.symm h1)) h2

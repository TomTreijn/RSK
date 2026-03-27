import Mathlib.Logic.Function.Basic
import Mathlib.Data.SetLike.Basic
import RSK.Basic
import Mathlib.Tactic
import RSK.OrderedList

set_option relaxedAutoImplicit true

abbrev Grid := List (List Nat)

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
      apply wkinc_ins_wkinc
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
      apply wkinc_ins_wkinc
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

theorem bmpshft_row_bi : Function.Bijective bmpshft_row := by
  apply Function.bijective_iff_has_inverse.mpr
  have is_inv : Function.LeftInverse bmpshft_row_inv bmpshft_row ∧
        Function.RightInverse bmpshft_row_inv bmpshft_row := by
    constructor
    -- Left inverse
    · refine Function.leftInverse_iff_comp.mpr ?_
      refine Eq.symm (funext ?_)
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
    -- right inverse
    · refine Function.rightInverse_iff_comp.mpr ?_
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
  exact Exists.intro bmpshft_row_inv is_inv

example (a b : Nat) (h_1 : a ≤ b) (h_2 : ¬a = b) : (a < b):= by exact Nat.lt_of_le_of_ne h_1 h_2
example (a b : Nat) (h_1 : some a = some b) : (a = b) := by exact ENat.coe_inj.mp h_1
example (a b : Nat) : (a < b) = (b > a) := by exact Eq.propIntro (fun a ↦ a) fun a ↦ a

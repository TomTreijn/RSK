import RSK.OrderedList
import RSK.Basic
import Mathlib.Tactic

set_option relaxedAutoImplicit true
set_option linter.style.whitespace false

/-
  This file contains the definition of a SSYT, alongside some theorems to use the defition.
  A Grid is just a List of Lists of Nats.
  In this file, a Semistandard Young tableau is Grid with the following
  properties:
   - The length of the Lists is decreasing. So the SSYT has the shape of a Young diagram.
   - The columns are strictly increasing.
   - The rows are weakly increasing

  The third property is defined using the definition of an ordered List.
  The first and second properties are defined using a relation between lists called row_comp,
  which is true if the bottom list is shorter than the top list and each entry in the bottom
  list is strictly less than the entry in the top list.
  Then the List of List of Nats is an ordered list with respect to row_comp.

  The three properties are also stated as theorems:
   - diagram_decreasing
   - SSYT_col_increasing
   - SSYT_row_increasing

  Then, some theorems are defined which help remove, add or set an entry in a semi
  standard Young tableau.

  Finally, the shape, entries and shape of a SSYT are defined, alongside some theorem to use
  these defintions.
-/

abbrev Grid := List (List Nat)

/- True if the row₁ is longer than row₂ and every entry of row₂ is strictly less than the
  corresponding entry in row₁.-/
def row_comp (row₁ row₂ : List Nat) : Prop :=
  ∃(h_diagram : row₂.length ≤ row₁.length), ∀(i : Nat) (hi : i < row₂.length), row₁[i] < row₂[i]

/-  States an equivalent definition of row_comp, and proves that these are equivalent.
    This is used because the Exists statement is not algorithmically verifiable.
-/
theorem row_comp₂ (row₁ row₂ : List Nat) :
  row_comp row₁ row₂ ↔
  if h_diagram : row₂.length ≤ row₁.length then
    ∀(i : Nat) (hi : i < row₂.length), row₁[i] < row₂[i]
  else
    False := by
  rw[row_comp]
  constructor
  · intro ⟨h_diagram, fall⟩
    simp [h_diagram, fall]
  · split
    · case _ h_diagram =>
      intro fall
      exact ⟨h_diagram, fall⟩
    · case _ =>
      intro f
      exact False.elim f

-- Shows that row_comp can be verified algorithmically
instance instDecidable_row_comp (row₁ row₂ : List Nat) : Decidable (row_comp row₁ row₂) :=
  decidable_of_decidable_of_iff (Iff.symm (row_comp₂ row₁ row₂))

-- Shows that row_comp is a transitive property, this is needed to define an ordered list.
theorem row_comp_trans (h₁ : row_comp row₁ row₂) (h₂ : row_comp row₂ row₃) :
  row_comp row₁ row₃ := by
  have ⟨h_diagram₁, h_inc₁⟩ := h₁
  have ⟨h_diagram₂, h_inc₂⟩ := h₂
  have h_diagram := Nat.le_trans h_diagram₂ h_diagram₁
  have h_inc : ∀(i : Nat) (hi : i < row₃.length), row₁[i] < row₃[i] := by
    intro i hi
    exact Nat.lt_trans (h_inc₁ i (Nat.lt_of_lt_of_le hi h_diagram₂)) (h_inc₂ i hi)
  exact ⟨h_diagram, h_inc⟩


/-  In this section, the general definitions of theorems defined in optionOrd and OrderedList
    are applied to row_comp_trans.
-/
def op_lst (a b : Option (List Nat)) := option_r (row_comp · ·) a b
theorem op_lst_some : op_lst (some a) (some b) = (row_comp a b) := by rfl
theorem op_lst_none_l : op_lst none a := option_r_left_none row_comp
theorem op_lst_none_r : op_lst a none := option_r_right_none row_comp

def IsRowInc (cells : Grid) := IsMonotone row_comp cells
instance instDecidableIsRowInc (cells : Grid) : Decidable (IsRowInc cells) :=
  instDecidableIsMonotone row_comp cells

def IsRowInc2 (cells : Grid) := IsMonotone2 row_comp cells

def rowinc_rowinc2 {cells : Grid} : IsRowInc cells ↔ IsRowInc2 cells
 := monotone_monotone2 row_comp row_comp_trans

theorem rowinc_append_rowinc (h_ord : IsRowInc list) (n : List Nat)
  (h_le : op_lst list.getLast? n) : IsRowInc (list ++ [n]) := monotone_append_monotone h_ord n h_le

theorem rowinc_set_rowinc (h_ord : IsRowInc cells) (k : List Nat) (i : Nat)
  (h_le : ((i = 0) ∨ (op_lst cells[i - 1]? k)) ∧ (op_lst k cells[i + 1]?)) :
  IsRowInc (cells.set i k) :=
  monotone_set_monotone row_comp h_ord k i h_le

theorem rowinc_front_rowinc (h : IsRowInc cells) : IsRowInc cells.dropLast :=
  montone_front_monotone row_comp h

theorem rowinc_tail_rowinc (h : IsRowInc (top :: rest)) : IsRowInc rest :=
  monotone_tail_monotone h

/- ------------------------------------------------------------------------------------------------
    The definition of a SSYT:
    The rows obey the row_comp property and
    every row:
    - is not empty
    - is weakly increasing.
------------------------------------------------------------------------------------------------ -/
def IsSSYT (cells : Grid) : Prop :=
  (∀ (j : Nat) (h : j < cells.length), IsWeakInc cells[j] ∧ cells[j] ≠ []) ∧
  IsRowInc cells

-- Convincing lean that it can algorithmically check that something is a SSYT.
instance instDecidableIsSSYT (cells : Grid) : Decidable (IsSSYT cells) := instDecidableAnd
example : IsSSYT [[1, 2, 2, 3], [2, 3, 4], [5]] := by decide


/- The next section are some theorems of properties of SSYTs.
-/

-- Some trivial results from the definition.
theorem SSYT_rows_inc (hSSYT : IsSSYT cells) : IsRowInc cells := hSSYT.right
theorem SSYT_row_weak (hSSYT : IsSSYT cells) (j : Nat) (h : j < cells.length) :
  IsWeakInc cells[j] := (hSSYT.left j h).left
theorem SSYT_row_not_nil (hSSYT : IsSSYT cells) (j : Nat) (h : j < cells.length) :
  cells[j] ≠ [] := (hSSYT.left j h).right

-- Given two rows, the bottom row is shorter than the top row.
theorem diagram_decreasing (hSSYT : IsSSYT cells)
  (j₁ j₂ : Nat) (hj₁_lt_j₂ : j₁ < j₂) (hj₂_lt_len : j₂ < cells.length) :
  cells[j₁].length ≥ cells[j₂].length := by
  have ⟨h_diagram, _⟩ := rowinc_rowinc2.mp hSSYT.right j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  exact h_diagram

-- Given two positions in a column, the top entry is strictly smaller than the bottom entry.
theorem SSYT_col_increasing (hSSYT : IsSSYT cells)
  (i j₁ j₂ : Nat) (hj₁_lt_j₂ : j₁ < j₂)
  (hj₂_lt_len : j₂ < cells.length) (hi_lt_len : i < cells[j₂].length) :
  have := diagram_decreasing hSSYT j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  cells[j₁][i] < cells[j₂][i] := by
  have ⟨_, inc⟩ := rowinc_rowinc2.mp hSSYT.right j₁ j₂ hj₁_lt_j₂ hj₂_lt_len
  exact inc i hi_lt_len

-- Given two positions in a row, the left entry is smaller than the right entry.
theorem SSYT_row_increasing (hSSYT : IsSSYT cells)
  (i₁ i₂ j : Nat) (hj_lt_len : j < cells.length) (hi₁_lt_i₂ : i₁ < i₂)
  (hi₂_lt_len : i₂ < cells[j].length) :
  cells[j][i₁] ≤ cells[j][i₂] :=
  wkinc_wkinc2.mp (hSSYT.left j hj_lt_len).left i₁ i₂ hi₁_lt_i₂ hi₂_lt_len


/-  The next section lists some ways of modifying a SSYT such that the result of the
    modification is also a SSYT.
-/

-- Removing the top row of a SSYT results in a SSYT.
theorem SSYT_sub_SSYT (hSSYT : IsSSYT (top :: rest)) : IsSSYT rest := by
  constructor
  · intro j hj_lt_len
    have this := hSSYT.left (j + 1) (Nat.add_lt_of_lt_sub hj_lt_len)
    rw [List.getElem_cons_succ] at this
    exact this
  · exact rowinc_tail_rowinc hSSYT.right

/-  Adding a entry to the bottom of a SSYT is valid if
    the entry is larger than the current bottom-left entry.
-/
theorem SSYT_append_row (hSSYT : IsSSYT cells) (k : Nat)
  (h_col_above :
    if hcells : cells.length = 0 then
      True
    else
      have iji : 0 < cells[cells.length - 1].length := by
        have := (hSSYT.left (cells.length - 1) (Nat.sub_one_lt hcells)).right
        exact List.length_pos_iff.mpr this
      cells[cells.length - 1][0] < k
  ) : IsSSYT (cells ++ [[k]]) := by
    constructor
    · intro j hj_le_len
      if hj : j = cells.length then
        rw[List.getElem_append_right (Nat.le_of_eq (Eq.symm hj))]
        rw[List.getElem_singleton]
        constructor
        · trivial
        · exact List.cons_ne_nil k []
      else
        rw [List.length_append, List.length_singleton] at hj_le_len
        have hj_lt_len : j < cells.length := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj_le_len) hj
        rw [List.getElem_append_left hj_lt_len]
        exact hSSYT.left j hj_lt_len
    · apply rowinc_append_rowinc hSSYT.right
      · match cells with
        | [] =>
          rw[List.getLast?_nil]
          exact op_lst_none_l
        | c :: cs =>
          rw[List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil c cs)]
          simp_rw[op_lst_some, row_comp, List.getLast_eq_getElem,
            List.length_singleton, Nat.lt_one_iff]
          have neq_nil := (hSSYT.left cs.length (Nat.lt_add_one cs.length)).right
          exact ⟨List.length_pos_iff.mpr neq_nil, by
            intro i hi
            simp_rw[hi]
            exact h_col_above
          ⟩

/-  Adding a entry k to a row j results in a SSYT if:
     - The new row j is weakly increasing
     - j = 0 or row j - 1 is strictly longer than row j
     - j = 0 or the new entry k is strictly larger than the entry above.
-/
theorem SSYT_append (hSSYT : IsSSYT cells) (j : Nat) (k : Nat)
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
  IsSSYT (cells.set j (cells[j] ++ [k])) := by
  rw[IsSSYT]
  constructor
  · intro j₂ hj₂_lt_len
    if hj_eq_j₂ : j = j₂ then
      simp_rw[←hj_eq_j₂, List.getElem_set_self]
      constructor
      · exact h_row
      · exact List.concat_ne_nil k cells[j]
    else
      rw[List.getElem_set_ne hj_eq_j₂]
      rw[List.length_set] at hj₂_lt_len
      exact hSSYT.left j₂ hj₂_lt_len
  · apply rowinc_set_rowinc hSSYT.right
    · constructor
      · if hj : j = 0 then
          simp_rw [hj, zero_tsub, true_or]
        else
          simp only [hj, false_or] at hst_dec
          simp only [hj, ↓reduceDIte] at h_col_above
          apply Or.intro_right
          rw[List.getElem?_eq_getElem, op_lst_some, row_comp]
          · simp_rw[List.length_append, List.length_singleton]
            have hdiagram := Order.add_one_le_iff.mpr hst_dec
            exact ⟨hdiagram, by
              intro i hi_lt_len
              if hi : i = cells[j].length then
                simp_rw[List.getElem_append_right (Nat.le_of_eq (Eq.symm hi)),
                  hi, List.getElem_singleton]
                exact h_col_above
              else
                have iji : i < cells[j].length := by omega
                rw[List.getElem_append_left iji]
                exact SSYT_col_increasing hSSYT i (j - 1) j (Nat.sub_one_lt hj) hj_lt_len iji
            ⟩
      · if hsuccj : cells.length = j + 1 then
          rw[List.getElem?_eq_none (Nat.le_of_eq hsuccj)]
          exact op_lst_none_r
        else
          have hsuccj_lt : j + 1 < cells.length := by omega
          rw[List.getElem?_eq_getElem hsuccj_lt, op_lst_some, row_comp]
          have len_dec := diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hsuccj_lt
          simp_rw[List.length_append, List.length_singleton]
          exact ⟨Nat.le_add_right_of_le len_dec, by
            intro i hi
            have i_lt : i < cells[j].length := Nat.lt_of_lt_of_le hi len_dec
            rw[List.getElem_append_left i_lt]
            exact SSYT_col_increasing hSSYT i j (j + 1) (lt_add_one j) hsuccj_lt hi
          ⟩

/-  Setting an entry k to k' at (j, i) results in a SSYT if:
     - The new row j is weakly increasing
     - j = 0 or the new entry k is strictly larger than the entry above.
     - j = 0 or the new entry k is strictly smaller than the entry below.
-/
theorem SSYT_set (hSSYT : IsSSYT cells) (j i : Nat) (k : Nat)
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
  ) : IsSSYT (cells.set j (cells[j].set i k)) := by
    constructor
    · intro j₂ hj₂_lt_len
      if hj : j = j₂ then
        simp_rw[←hj, List.getElem_set_self]
        constructor
        · exact h_row
        · have neq_nil := (hSSYT.left j hj_lt_len).right
          apply List.ne_nil_iff_length_pos.mpr
          rw[List.length_set]
          exact List.length_pos_iff.mpr neq_nil
      else
        rw[List.getElem_set_ne hj]
        rw[List.length_set] at hj₂_lt_len
        exact hSSYT.left j₂ hj₂_lt_len
    · apply rowinc_set_rowinc hSSYT.right
      · constructor
        · if hj : j = 0 then
            apply Or.intro_left
            exact hj
          else
            apply Or.intro_right
            simp_rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt hj_lt_len),
              op_lst_some, row_comp, List.length_set]
            have len_lt := diagram_decreasing hSSYT (j - 1) j (Nat.sub_one_lt hj) hj_lt_len
            exact ⟨len_lt, by
              intro i₂ hi₂_lt_len
              if hi₂_eq_i : i = i₂ then
                simp_rw[←hi₂_eq_i, List.getElem_set_self]
                simp only [hj, ↓reduceDIte] at h_col_above
                exact h_col_above
              else
                simp_rw[List.getElem_set_ne hi₂_eq_i]
                exact SSYT_col_increasing hSSYT i₂ (j - 1) j
                  (Nat.sub_one_lt hj) hj_lt_len hi₂_lt_len
            ⟩
        · if hsuccj : cells.length = j + 1 then
            rw[List.getElem?_eq_none (Nat.le_of_eq hsuccj)]
            exact op_lst_none_r
          else
            have hsuccj_lt_len : j + 1 < cells.length := by omega
            simp_rw[List.getElem?_eq_getElem hsuccj_lt_len, op_lst_some, row_comp, List.length_set]
            have len_lt := diagram_decreasing hSSYT j (j + 1) (lt_add_one j) hsuccj_lt_len
            exact ⟨len_lt, by
              intro i₂ hi₂_lt_len
              if hi₂_eq_i : i = i₂ then
                rw[←hi₂_eq_i] at hi₂_lt_len
                simp only [hsuccj_lt_len, ↓reduceDIte, hi₂_lt_len] at h_col_under
                simp_rw[←hi₂_eq_i, List.getElem_set_self]
                exact h_col_under
              else
                rw[List.getElem_set_ne hi₂_eq_i]
                exact SSYT_col_increasing hSSYT i₂ j (j + 1) (lt_add_one j) hsuccj_lt_len hi₂_lt_len
            ⟩

/-  Removing an entry from row j results in a SSYT if:
     - j is the bottom row, or it is stricty longer than the row j + 1 below.
-/
theorem SSYT_remove (hSSYT : IsSSYT cells) (j : Nat)
  (hj_lt_len : j < cells.length)
  (hst_dec :
    if hsuccj_len : j + 1 < cells.length then
      cells[j].length > cells[j + 1].length
    else
      True
  ) :
  if cells[j].length > 1 then
    IsSSYT (cells.set j (cells[j].dropLast))
  else
    IsSSYT cells.dropLast := by
  split
  · case isTrue hj_len =>
      constructor
      · intro j₂ hj₂_lt_len
        if hj₂_eq_j : j = j₂ then
          simp_rw[←hj₂_eq_j, List.getElem_set_self]
          have left_j := hSSYT.left j hj_lt_len
          constructor
          · exact wkinc_front_wkinc left_j.left
          · apply List.ne_nil_iff_length_pos.mpr
            rw[List.length_dropLast]
            omega
        else
          rw[List.getElem_set_ne hj₂_eq_j]
          rw[List.length_set] at hj₂_lt_len
          exact hSSYT.left j₂ hj₂_lt_len
      · apply rowinc_set_rowinc hSSYT.right
        constructor
        · if hj : j = 0 then
            simp[hj]
          else
            apply Or.intro_right
            rw[List.getElem?_eq_getElem (Nat.sub_lt_of_lt hj_lt_len), op_lst_some, row_comp]
            simp_rw [List.length_dropLast]
            have hdiag := diagram_decreasing hSSYT (j - 1) j (Nat.sub_one_lt hj) hj_lt_len
            exact ⟨by omega, by
              intro i hi_lt_len
              rw[List.getElem_dropLast]
              have hcol_inc : cells[j - 1][i] < cells[j][i] :=
                SSYT_col_increasing hSSYT i (j - 1) j
                  (Nat.sub_one_lt hj) hj_lt_len (Nat.lt_of_lt_pred hi_lt_len)
              simp [hcol_inc]
            ⟩
        · if hsuccj_lt : j + 1 < cells.length then
            simp_rw[List.getElem?_eq_getElem hsuccj_lt, op_lst_some, row_comp, List.length_dropLast,
              List.getElem_dropLast]
            simp only [hsuccj_lt, ↓reduceDIte,] at hst_dec
            exact ⟨by omega, by
              intro i hi_lt_len
              exact SSYT_col_increasing hSSYT i j (j + 1) (lt_add_one j) hsuccj_lt hi_lt_len
            ⟩
          else
            rw[List.getElem?_eq_none (Nat.le_of_not_lt hsuccj_lt)]
            exact op_lst_none_r
  · case isFalse a =>
    constructor
    · simp_rw[List.getElem_dropLast, List.length_dropLast]
      intro j hj_lt_len
      exact hSSYT.left j (Nat.lt_of_lt_pred hj_lt_len)
    · exact rowinc_front_rowinc hSSYT.right


/- The next section contains some theorems for working with the shape of a SSYT
-/
def shape (cells : Grid) : List Nat :=
  cells.map (·.length)

theorem shape_length_eq_length {cells : Grid} : (shape cells).length = cells.length := by
  rw[shape, List.length_map]

theorem rowlen_eq_shape (cells : Grid) (j : Nat) (hj : j < cells.length) :
  cells[j].length = (shape cells)[j]'(by rw[shape_length_eq_length]; exact hj) := by
  simp_rw[shape, List.getElem_map]

-- If two SSYTs have the same shape, they have the same length.
theorem length_eq_of_shape_eq :
  shape cells₁ = shape cells₂ → cells₁.length = cells₂.length := by
  intro shape_eq
  repeat rw[←shape_length_eq_length]
  rw[shape_eq]

-- If two SSYTs have the same shape, one is nil iff the other is nil.
theorem shape_eq_notnil_eq :
  shape cells₁ = shape cells₂ → (cells₁ ≠ [] ↔ cells₂ ≠ []) := by
  intro hshape
  repeat rw[←List.length_pos_iff]
  rw[length_eq_of_shape_eq hshape]

-- The shape of a SSYT is an decreasing list.
theorem shape_decreasing (hSSYT : IsSSYT cells) : IsWeakDec (shape cells) := by
  refine wkdec_wkdec2.mpr ?_
  rw[IsWeakDec2, IsMonotone2]
  intro i j h₁ h₂
  rw[shape_length_eq_length] at h₂
  repeat rw[←rowlen_eq_shape]
  exact diagram_decreasing hSSYT i j h₁ h₂

-- Changing a single entry of a SSYT doesn't change the shape.
theorem shape_set :
  shape (cells.set i row) = (shape cells).set i row.length := by
  rw[shape, List.map_set, ←shape]

-- Removing the last row of a SSYT also removes the last entry of the shape.
theorem shape_dropLast :
  shape (cells.dropLast) = (shape cells).dropLast := by
  rw[shape, List.map_dropLast, ←shape]

-- Adding an entry to a row of a SSYT increases the length of that row by one.
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

-- Removing an entry of a row in a SSYT decreases the length of that row by one.
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

/-  The next section contains some theorems about the entries of a SSYT
-/
def entries (cells : Grid) : List Nat :=
  cells.flatten

-- An empty SSYT contains no entries.
theorem entries_nil : entries [] = [] := by
  rw[entries, List.flatten_nil]

-- If an element is in some row of a SSYT, it is also in the entries of the SSYT.
theorem mem_entries_of_mem_row {a j : Nat} (hj_lt_len : j < cells.length) (h : a ∈ cells[j]) :
  a ∈ entries cells := by
  rw[entries, List.mem_flatten]
  exact ⟨cells[j], ⟨List.mem_of_getElem (by rfl), h⟩⟩

-- Every entry cells[j][i] is an entry.
theorem getElem_entry (cells : Grid) (i j : Nat)
  (hj : j < cells.length) (hi : i < cells[j].length) :
  cells[j][i] ∈ entries cells := by
  have hi_mem := List.getElem_mem hi
  exact mem_entries_of_mem_row hj hi_mem

-- For every k ∈ entry cells, there are j and i such that k = cells[j][i].
theorem entry_getElem (cells : Grid) (k : Nat) (hk : k ∈ entries cells) :
  ∃(j i : Nat) (hj_lt_len : j < cells.length) (hi_lt_len : i < cells[j].length), k = cells[j][i]
   := by
  rw[entries] at hk
  have ⟨row, ⟨row_in_cell, k_in_row⟩⟩ := List.mem_flatten.mp hk
  have ⟨j, ⟨hj, jrow⟩⟩:= List.getElem_of_mem row_in_cell
  rw[←jrow] at k_in_row
  have ⟨i, ⟨hi, krow⟩⟩:= List.getElem_of_mem k_in_row
  exact ⟨j, ⟨i, ⟨hj, ⟨hi, Eq.symm krow⟩⟩⟩⟩

-- Setting an entry k' to k in a SSYT removes k from the entries and adds k'.
theorem count_entries_set (cells : Grid) (j a : Nat) (l : List Nat) (hj_lt_len : j < cells.length) :
  (entries (cells.set j l)).count a = (entries cells).count a + l.count a - cells[j].count a := by
  repeat rw[entries]
  exact count_flatten_set cells j a l hj_lt_len

-- Adding a k to a row in a SSYT also adds it to the entry of that SSYT.
theorem entries_add (cells : Grid) (k j : Nat)
  (hj_lt_len : j < cells.length) :
  List.Perm (entries (cells.set j (cells[j] ++ [k]))) (k::(entries cells)) := by
  repeat rw[entries]
  apply List.perm_iff_count.mpr
  intro a
  rw[count_flatten_set (hj_lt_len:=hj_lt_len)]
  nth_rewrite 2 [←List.singleton_append]
  repeat rw[List.count_append]
  omega

-- Adding a k to the end of a SSYT also adds it to the entries of that SSYT.
theorem entries_append (cells : Grid) :
  entries (cells ++ [[k]]) = (entries cells) ++ [k] := by
  repeat rw[entries]
  rw[List.flatten_append, List.flatten_singleton]

-- Removing the last row of a SSYT also removes these entries from the entries.
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

/-- Removing an element from a grid also removes it from its entries. -/
theorem entries_remove (cells : Grid) (j : Nat)
  (hj_lt_len : j < cells.length) (hnot_nil : cells[j] ≠ []) :
  List.Perm (entries (cells.set j (cells[j].dropLast)))
  ((entries cells).erase (cells[j].getLast hnot_nil)) := by
  repeat rw[entries]
  apply List.perm_iff_count.mpr
  intro a
  rw[count_flatten_set (hj_lt_len := hj_lt_len), count_dropLast (hnot_nil := hnot_nil),
  List.count_erase]
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

/- The next section contains some theorems about the size of a SSYT, the total number of entries.
-/
def size (cells : Grid) : Nat :=
  (shape cells).sum

/-- The size of a Grid is the number of entries -/
theorem size_eq_entries_len (cells : Grid) :
  (entries cells).length = size cells := by
  rw[entries]
  apply List.length_flatten


theorem size_pos_of_length_pos (hSSYT : IsSSYT cells) (h_pos : 0 < cells.length) :
  0 < size cells := by
  match cells with
  | [] => contradiction
  | a :: as =>
    rw[←size_eq_entries_len, entries, List.flatten_cons, List.length_append]
    exact Nat.add_pos_left (List.length_pos_iff.mpr (SSYT_row_not_nil hSSYT 0 h_pos)) ?_

theorem size_pos_of_not_nill (hSSYT : IsSSYT cells) (hnot_nil : cells ≠ []) :
  0 < size cells :=
  size_pos_of_length_pos hSSYT (List.length_pos_iff.mpr hnot_nil)

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

theorem SSYT_size_nzero_nnil (hSSYT : IsSSYT cells) : 0 < size cells ↔ cells ≠ [] := by
  rw[←Nat.ne_zero_iff_zero_lt]
  exact not_congr (SSYT_size_zero_nil hSSYT)

-- Adding an element increases the size by one.
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

-- Adding an element increases the size by one.
theorem size_append (cells : Grid) : size (cells ++ [[k]]) = size cells + 1 := by
  rw[size, shape, List.map_append, List.map_singleton, List.length_singleton, List.sum_append,
    List.sum_singleton, ←shape, ←size]

-- Removing an element decreases the size by one.
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
    exact mem_entries_of_mem_row hj_lt_len in_row
  rw [entries_remove_rw, List.length_erase_of_mem last_in_entries]
  rw [size_eq_entries_len]

-- Removing an element decreases the size by one.
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

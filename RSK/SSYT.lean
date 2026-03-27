import RSK.OrderedList

structure SSYT where
  cells : List (List Nat)
  hdiagram : IsWeakInc (cells.map (·.length))
  hrow_ord : ∀ (i : Nat) (h : i < cells.length), IsWeakInc cells[i]

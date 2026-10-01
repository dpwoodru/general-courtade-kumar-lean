import GeneralCK.Certificates.E8TAxisPartitionKernel

/-! Local aggregation only.  None of these declarations asserts that the
positive-t production cells cover the full t-axis domain. -/

namespace GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

open E8TAxisPartitionKernel

theorem cellPositive_of_allLeaves {tree : Tree} {r : Rect}
    (h : AllLeaves CellPositive tree r) : CellPositive r := by
  intro s t hadm hcover
  obtain ⟨leaf, hleaf, hpoint⟩ := locate_leaf h hcover
  exact hleaf s t hadm hpoint

def CellsPositive (rs : List Rect) : Prop := ∀ r ∈ rs, CellPositive r

theorem cellsPositive_nil : CellsPositive [] := by
  intro r hr
  simp at hr

theorem cellsPositive_cons {r : Rect} {rs : List Rect}
    (hr : CellPositive r) (hrs : CellsPositive rs) : CellsPositive (r :: rs) := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · simpa only [h] using hr
  · exact hrs x h

theorem cellsPositive_append {xs ys : List Rect}
    (hx : CellsPositive xs) (hy : CellsPositive ys) : CellsPositive (xs ++ ys) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact hx r h
  · exact hy r h

#print axioms cellPositive_of_allLeaves
#print axioms cellsPositive_cons
#print axioms cellsPositive_append

end GeneralCK.Certificates.E8TAxisPositiveAggregationKernel

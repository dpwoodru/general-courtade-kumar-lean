import CKLaneE.SLeaf
import CKLaneG3.SCover

/-!
# Lane E: adapter to the canonical (S) module `CKLaneG3.SCover`

The lane-local `CKLaneE.S.SBox` / `sBoxL` / `InS` are field-for-field copies of `CKLaneG3.SBox` /
`sBox` / `InS`; `toG3` maps boxes, commutes with the root and the halving step, hence
`toG3 (sBoxL p) = CKLaneG3.sBox p`, and `LeafS` is `CKLaneG3.RowS`.  So every lane leaf theorem
`LeafS (sBoxL p)` yields the canonical obligation `CKLaneG3.SLeafOK (CKLaneG3.sBox p)`.
-/

set_option autoImplicit false

namespace CKLaneE.SAdapt

open CKLaneE.S

def toG3 (B : SBox) : CKLaneG3.SBox := ⟨B.x0, B.x1, B.b0, B.b1, B.t0, B.t1⟩

theorem toG3_sBoxL (p : List ℕ) : toG3 (sBoxL p) = CKLaneG3.sBox p :=
  CKLaneG3.sBox_of_commute SBox.child sRoot toG3 rfl
    (fun X d => by rcases d with _ | _ | _ | _ | _ | _ | d <;> rfl) p

theorem rowS_of_leafS {B : SBox} (h : LeafS B) : CKLaneG3.RowS (toG3 B) := by
  intro k μ hab hin hact
  exact h k μ hab hin hact

theorem sLeafOK_of_leafS (p : List ℕ) (h : LeafS (sBoxL p)) :
    CKLaneG3.SLeafOK (CKLaneG3.sBox p) := by
  rw [← toG3_sBoxL p]
  exact CKLaneG3.sLeafOK_of_rowS (rowS_of_leafS h)

/-- Family transport: a lane family over a path list gives the canonical obligations. -/
theorem family_sLeafOK (L : List (List ℕ)) (h : ∀ p ∈ L, LeafS (sBoxL p)) :
    ∀ p ∈ L, CKLaneG3.SLeafOK (CKLaneG3.sBox p) :=
  fun p hp => sLeafOK_of_leafS p (h p hp)

end CKLaneE.SAdapt

#print axioms CKLaneE.SAdapt.family_sLeafOK

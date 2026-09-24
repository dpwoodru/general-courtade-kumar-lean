import CKLaneN1b.Cert
import CKLaneN1b.Tree

/-!
# Lane N1b: batch soundness over `(path, certificate)` lists

`checkAll_sound`: if every certificate of a list checks on the exact archived box of its path,
then `Sem` holds on every such box.  No other hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN1b

theorem checkAll_sound (L : List (List ℕ × Cert))
    (h : (L.all fun x => checkCert (boxOf x.1) x.2) = true) : ∀ x ∈ L, Sem (boxOf x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkCert_sound _ _ (h x hx)

end CKLaneN1b

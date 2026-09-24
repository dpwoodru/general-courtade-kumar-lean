import CKLaneN23.CornerOkUC
import CKLaneN23.CornerOkUE
import CKLaneN23.CornerOkTC
import CKLaneN23.CornerOkPosCells

/-!
# CKLaneN23.CornerClosure — the closed RA-stat corner theorem `GammaCorner (1/20)` (Lane N23b)

The Boolean corner checker `cornerCheck = ucCheck && (ueCheck && (tcCheck && posCheckC))` is evaluated by
the kernel (`decide +kernel` in `CornerOk{UC,UE,TC}` and the 128 positivity cells `PosCell.C<j>_<k>` assembled in `CornerOkPosCells`, no `native_decide`); `cornerCheck_sound`
(its only premise is the check) turns it into `GammaCorner (1/20)`.
-/

namespace CKLaneN23.CT

theorem cornerCheck_ok : cornerCheck = true := by
  show (ucCheck && (ueCheck && (tcCheck && posCheckC))) = true
  rw [uc_ok, ue_ok, tc_ok, pos_ok]
  all_goals rfl

end CKLaneN23.CT

namespace CKLaneN23.RS

/-- **RA-stat corner certificate** (Lane N23b): `rayGamma ≥ 0` on the corner `(1/2-b)+d ≤ 1/20`. -/
theorem gammaCorner_one_twentieth : GammaCorner (1 / 20) :=
  CKLaneN23.CT.cornerCheck_sound CKLaneN23.CT.cornerCheck_ok

end CKLaneN23.RS

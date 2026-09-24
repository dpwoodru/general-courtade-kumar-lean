import GeneralCK.PureGapE8SAxisOriginClosure
import GeneralCK.PureGapE8CertificateReduction

/-!
# Lane C3 — the `origin` field of `GeneralCK.E8CertificateOwners` (by-product)

`0 < e8Delta e8Q s t` on the admissible region with `s + t ≤ 2/25`, from the unconditional
origin second-`s`-derivative bound `e8RegularDeltaSS_pos_on_origin` and the consumer-side
reduction `e8Delta_pos_of_second_s_derivative` (integrate twice in `s` from `s = 0`).
Same proof as `CKLaneC3.Compact.originOwner`, packaged without the compact fleet imports.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.Origin

open GeneralCK

/-- The `origin` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem origin : E8PositiveOn fun s t => s + t ≤ 2 / 25 := by
  intro s t hadm hR
  have hR' : s + t ≤ 2 / 25 := hR
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact e8RegularDeltaSS_pos_on_origin (hadm.mono_s hu.1 hu.2.le) (by linarith [hu.2, hR'])

end CKLaneC3.Origin

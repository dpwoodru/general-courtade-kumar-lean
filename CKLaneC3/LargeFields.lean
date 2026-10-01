import E8GlobalRatioCertificate
import E8LargeTFinal
import GeneralCK.PureGapE8CertificateReduction

/-!
# Lane C3 — the `largeS`, `largeT`, `smallSTail` fields of `GeneralCK.E8CertificateOwners`

Re-verified P-E8 results over the final assembly root `~/ck_lanes_20260923/coord/asmRoot`, importing
the CANONICAL E8 modules (`E8GlobalRatioCertificate` = C2's pinned 989ac0b7…1461, `E8LargeTFinal`)
rather than lane copies (integration conflict C3):

* `largeS` is `GeneralCK.E8RatioMonotonicity.e8LargeSCertified` (ratio monotonicity of the E8
  inverse; canonical 14-module ratio package over the canonical GeneralCK large-s modules);
* `largeT` is `GeneralCK.E8LargeTSAxis.largeT`;
* `smallSTail` follows from `GeneralCK.E8LargeTSAxis.largeT_elevenNine`, whose region
  `119/10 ≤ t ∧ s ≤ 63/20` contains `20 ≤ t ∧ s ≤ 1/200`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.LargeFields

open GeneralCK

/-- The `largeS` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem largeS : E8PositiveOn fun s _ => (63 / 20 : ℝ) ≤ s :=
  GeneralCK.E8RatioMonotonicity.e8LargeSCertified

/-- The `largeT` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem largeT : E8PositiveOn fun s t => (119 / 10 : ℝ) ≤ t ∧ (1 / 200 : ℝ) ≤ s ∧ s ≤ 63 / 20 :=
  GeneralCK.E8LargeTSAxis.largeT

/-- The `smallSTail` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem smallSTail : E8PositiveOn fun s t => (20 : ℝ) ≤ t ∧ s ≤ 1 / 200 := by
  intro s t hadm h
  have h' : (20 : ℝ) ≤ t ∧ s ≤ 1 / 200 := h
  exact GeneralCK.E8LargeTSAxis.largeT_elevenNine s t hadm
    ⟨by linarith [h'.1], by linarith [h'.2]⟩

end CKLaneC3.LargeFields

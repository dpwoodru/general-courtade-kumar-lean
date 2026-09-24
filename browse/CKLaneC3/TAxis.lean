import GeneralCK.Certificates.Generated.E8TAxisFullBridge.All
import GeneralCK.Certificates.E8TAxisZero0051Root
import GeneralCK.Certificates.E8TAxisZero0052Root
import GeneralCK.Certificates.E8TAxisZero0053Root
import GeneralCK.Certificates.E8TAxisZero0054Root
import GeneralCK.Certificates.E8TAxisZero0055Root
import GeneralCK.Certificates.E8TAxisZero0056Root
import GeneralCK.Certificates.E8TAxisZero0057Root

/-!
# Lane C3 — the E8 t-axis owner field

`E8TAxisFullBridge.e8_taxis_derivative_bound` (compiled, provider root) proves
`E8TAxisDerivativeBound` from the historical 773-leaf tree
(`qValid tree qDomain` and `qLeaves tree qDomain ⊆ cells`, both `decide +kernel`),
the 766 already-compiled leaf certificates, and seven explicit premises: the seven
zero-t cells with `s ∈ [2.898…, 63/20]`, `t ∈ [0, 0.00125]` (geometry indices
661, 677, 693, 709, 725, 741, 757).

The seven premises are discharged by the compiled repaired roots
`E8TAxisZero0057Root … E8TAxisZero0051Root` (index map 661 ← 0057, 677 ← 0056,
693 ← 0055, 709 ← 0054, 725 ← 0053, 741 ← 0052, 757 ← 0051).

The final declaration has the exact type of the `tAxis` field of
`GeneralCK.E8CertificateOwners`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneC3.TAxis

open GeneralCK GeneralCK.Certificates
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The numerical t-axis input `E8TAxisDerivativeBound`, unconditionally. -/
theorem e8TAxisDerivativeBound : E8TAxisDerivativeBound := by
  apply E8TAxisFullBridge.e8_taxis_derivative_bound
  · simpa only [RatRect.real, E8TAxisZero0057Root.rectangle,
      E8TAxisZero0057Root.rationalRectangle, zero_div] using E8TAxisZero0057Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0056Root.rectangle,
      E8TAxisZero0056Root.rationalRectangle, zero_div] using E8TAxisZero0056Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0055Root.rectangle,
      E8TAxisZero0055Root.rationalRectangle, zero_div] using E8TAxisZero0055Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0054Root.rectangle,
      E8TAxisZero0054Root.rationalRectangle, zero_div] using E8TAxisZero0054Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0053Root.rectangle,
      E8TAxisZero0053Root.rationalRectangle, zero_div] using E8TAxisZero0053Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0052Root.rectangle,
      E8TAxisZero0052Root.rationalRectangle, zero_div] using E8TAxisZero0052Root.cellPositive
  · simpa only [RatRect.real, E8TAxisZero0051Root.rectangle,
      E8TAxisZero0051Root.rationalRectangle, zero_div] using E8TAxisZero0051Root.cellPositive

/-- The `tAxis` field of `GeneralCK.E8CertificateOwners`, with its exact type. -/
theorem tAxis :
    E8PositiveOn fun s t => (3 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ t ≤ 1 / 50 :=
  e8_tAxis_of_derivative_bound e8TAxisDerivativeBound

end CKLaneC3.TAxis

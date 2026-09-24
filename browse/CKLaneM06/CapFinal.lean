import CKLaneM06.CapSSAgg
import CKLaneM06.CapXHAgg

/-!
# Lane M06: the cap theorem (5), CAP_REGION — closed

* `capPsi : CapPsi` — archive form `ζ ≥ R_ψ` for every feasible split, canonical laws with
  `a, b ∈ [1/10, 9/10]` and mean entropy deficit `s ≤ 3/40`;
* `centralCap : CentralCap` — the hybrid row (verbatim `CKLaneN23.CentralCap`, route row
  `CentralSquare` cap part), via `hybrid_gap_le_psi`.

Assembled from the two populations:
* `CapSSAgg.capSameSide : CapSameSide` — `SAME_SIDE_CAP` root `[1/10,1/2]²`, 2,108 archived leaves
  (trapezoid checker, fleet `M06-cap-ss`);
* `CapXHAgg.capCross : CapCross` — `EXPANDED_CAP` root `[1/10,1/2] × [1/2,9/10]`, 14,525 archived leaves
  (trapezoid + secant checkers, fleet `M06-cap-xh`).
-/

set_option autoImplicit false

namespace CKLaneM06.Cap.CapFinal

open CKLaneM06.Cap

/-- **Cap theorem (5)**, archive form: `ζ ≥ R_ψ` on the whole cap region at depth `3/40`. -/
theorem capPsi : CapPsi := capPsi_of_parts CapSSAgg.capSameSide CapXHAgg.capCross

/-- **CentralCap** (N23 row 3): strict psi-activity, `a,b ∈ [1/10,9/10]`, `s ≤ 3/40` ⟹ `gap ≤ cost`. -/
theorem centralCap : CentralCap := centralCap_of_parts CapSSAgg.capSameSide CapXHAgg.capCross

end CKLaneM06.Cap.CapFinal

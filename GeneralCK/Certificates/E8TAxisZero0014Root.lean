import GeneralCK.Certificates.E8TAxisZero0014LCertified
import GeneralCK.Certificates.E8TAxisZero0014RCertified
import GeneralCK.Certificates.E8TAxisGeneratedGeometry
namespace GeneralCK.Certificates.E8TAxisZero0014Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[24]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  by_cases hcut2 : s ≤ ((12812500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
  ·
    apply E8TAxisZero0014LCertified.positiveAt
    norm_num [E8TAxisZero0014LGeometry.rectangle, Rect.Covers, E8TAxisZero0014LGeometry.sLower,
      E8TAxisZero0014LGeometry.sUpper, E8TAxisZero0014LGeometry.tLower, E8TAxisZero0014LGeometry.tUpper] at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  ·
    apply E8TAxisZero0014RCertified.positiveAt
    norm_num [E8TAxisZero0014RGeometry.rectangle, Rect.Covers, E8TAxisZero0014RGeometry.sLower,
      E8TAxisZero0014RGeometry.sUpper, E8TAxisZero0014RGeometry.tLower, E8TAxisZero0014RGeometry.tUpper] at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0014Root

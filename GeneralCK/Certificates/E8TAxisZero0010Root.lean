import GeneralCK.Certificates.E8TAxisZero0010Certified
import GeneralCK.Certificates.E8TAxisGeneratedGeometry
namespace GeneralCK.Certificates.E8TAxisZero0010Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[40]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0010Certified.positiveAt
  norm_num [E8TAxisZero0010Geometry.rectangle, Rect.Covers, E8TAxisZero0010Geometry.sLower,
    E8TAxisZero0010Geometry.sUpper, E8TAxisZero0010Geometry.tLower, E8TAxisZero0010Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0010Root

import CKLaneM07.CE.R3Cover
import CKLaneM07.CE.R3Yup
import CKLaneN1.R3Octaves

/-! Lane M07 cross-check of the joint row-3 closure: N1's `transverse_of_octaves` (analytic side:
exclusions, octave dispatch, gapLB ≤ canonicalPureGap) instantiated with M07's numeric cover
(`R3Cover.sem<k>`) and octave heights (`R3Yup.yup<k>`). -/

namespace CKLaneM07.CE.R3Final

open CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Cover CKLaneM07.CE.R3Yup

/-- **CE-stat row 3** (`1/80000 ≤ t_C ≤ 1/100`, `A ≤ 1/20`): transverse-curvature pure-gap owner. -/
theorem transverseCurvatureOwner : CKLaneN1.CEStat.TransverseCurvatureOwner :=
  CKLaneN1.R3.transverse_of_octaves Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17
    sem17 yup17 sem16 yup16 sem15 yup15 sem14 yup14 sem13 yup13 sem12 yup12 sem11 yup11 sem10 yup10 sem9 yup9 sem8 yup8 sem7 yup7

end CKLaneM07.CE.R3Final

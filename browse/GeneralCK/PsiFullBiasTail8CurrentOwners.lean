import GeneralCK.PsiCentralFullBiasWedges
import GeneralCK.PsiSameSideTail8SmallMeanRegionClosure

/-! Checked analytic psi owner interface after the full-bias central wedges. -/

namespace GeneralCK

structure PsiFullBiasTail8CurrentOwners : Prop where
  sameChart : SameSidePsiTail8SmallMeanChartOwner
  oppositeCentral : PsiCentralFullBiasWedges.CentralOwner
  oppositeCompact : PsiThreeTenthsTail28.CompactOwner

theorem PsiFullBiasTail8CurrentOwners.toTail37Central
    (h : PsiFullBiasTail8CurrentOwners) :
    PsiThreeTenthsCentralTail37.CentralOwner :=
  PsiThreeTenthsTail28.toTail37CentralOwner
    (PsiCentralSixteenWedge.toTail28CentralOwner
      (PsiCentralTwentyFourWedge.toSixteenCentralOwner
        (PsiCentralFullBiasWedges.toTwentyFourCentralOwner
          h.oppositeCentral)))

theorem PsiFullBiasTail8CurrentOwners.toTail14Same
    (h : PsiFullBiasTail8CurrentOwners) :
    SameSidePsiTail14ExtendedChartOwner :=
  sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean h.sameChart

theorem PsiFullBiasTail8CurrentOwners.toThreeTenthsCompact
    (h : PsiFullBiasTail8CurrentOwners) :
    PsiThreeTenthsBias.CompactOwner :=
  PsiThreeTenthsTail28.toThreeTenthsCompactOwner h.oppositeCompact

#print axioms PsiFullBiasTail8CurrentOwners.toTail37Central
#print axioms PsiFullBiasTail8CurrentOwners.toTail14Same
#print axioms PsiFullBiasTail8CurrentOwners.toThreeTenthsCompact

end GeneralCK

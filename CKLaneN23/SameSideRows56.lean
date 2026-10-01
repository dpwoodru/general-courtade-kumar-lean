import CKLaneN23.Row6Strip

/-!
# Lane N23 — rows 5 and 6 plugged into the same-side interface

Conditional adapters (NOT closures): `SR_SameSideHalf` from the remaining six certificate rows
and `SR_DiagonalBand` from the remaining four, with rows 5 (`NoSepA_HighBiasRem`) and
6 (`NoSepA_StripRem`) discharged unconditionally by `Row5.row_noSepA_highBiasRem` and
`Row6.row_noSepA_stripRem`.
-/

namespace CKLaneN23

/-- Conditional (NOT a closure): rows 1–4, 7, 8 imply `SR_SameSideHalf`. -/
theorem sameSideHalf_of_remaining_six_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest)
    (hNear : SmallRatioT3NearRest) (hFE : FullEntropySSCoverRest) : SR_SameSideHalf :=
  sameSideHalf_of_certificate_rows hT1 hT4 hcap hMod Row5.row_noSepA_highBiasRem
    Row6.row_noSepA_stripRem hNear hFE

/-- Conditional (NOT a closure): rows 1–4 imply `SR_DiagonalBand`. -/
theorem diagonalBand_of_remaining_four_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest) :
    SR_DiagonalBand :=
  diagonalBand_of_certificate_rows hT1 hT4 hcap hMod Row5.row_noSepA_highBiasRem
    Row6.row_noSepA_stripRem

end CKLaneN23

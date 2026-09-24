import CKLaneA1.Identities
import GeneralCK.CorrectionComplementCharts

/-!
# CKLaneA1.Bridge — from pointwise positivity to `RatioSigns`

`RatioSigns u rho` (the sign strength required by `ChartOwners`) follows from
`0 ≤ actualDetGapCoefficient u w` and `0 < m11 u w` at `w = u + rho (1/2 - u)`, via
`kernel_eq_actual`, `kdet = (w-u)^2 · actualDetGapCoefficient` and
`Mdet_nonneg_iff_Kfactored_nonneg`.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

theorem ratioSigns_of_pos {u rho : ℝ} (hu : 0 < u) (hu2 : u < 1 / 2) (hr : 0 < rho)
    (hr1 : rho < 1)
    (hcoef : 0 ≤ actualDetGapCoefficient u (u + rho * (1 / 2 - u)))
    (hm : 0 < m11 u (u + rho * (1 / 2 - u))) :
    GeneralCK.Correction.Complement.RatioSigns u rho := by
  have hgap : 0 < rho * (1 / 2 - u) := mul_pos hr (by linarith)
  have huw : u < u + rho * (1 / 2 - u) := by linarith
  have hw : u + rho * (1 / 2 - u) < 1 / 2 := by
    have : rho * (1 / 2 - u) < 1 * (1 / 2 - u) := mul_lt_mul_of_pos_right hr1 (by linarith)
    linarith
  have hk : 0 ≤ kdet u (u + rho * (1 / 2 - u)) := by
    rw [kdet_eq_gap_sq_mul_coefficient hu huw hw]
    exact mul_nonneg (sq_nonneg _) hcoef
  obtain ⟨h1, h2⟩ := kernel_eq_actual hu huw hw
  have hw0 : 0 < H (u + rho * (1 / 2 - u)) := H_pos (hu.trans huw) (by linarith)
  have hw1 : H (u + rho * (1 / 2 - u)) < 1 := by
    have ht := H_strictMonoOn ⟨(hu.trans huw).le, hw.le⟩
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2)) hw
    simpa only [H_half] using ht
  unfold GeneralCK.Correction.Complement.RatioSigns
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact hm
  · exact (Mdet_nonneg_iff_Kfactored_nonneg hw0 hw1).2 (by rw [← h2]; exact hk)

#print axioms ratioSigns_of_pos

end CKLaneA1

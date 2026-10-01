import GeneralCK.PureGapDoubleCapLowTailHalfGap
import GeneralCK.Certificates.MixedConstants

/-! Uniform logarithmic and entropy bounds in the high-bias part of the
double-cap low tail. All constants are exact rationals. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapLowTail_A_ge_207 {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    207 / 100 ≤ SmallMean.A z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hRatio : (64 : ℝ) ≤ (1 + z) / (1 - z) := by
    apply (le_div_iff₀ hm).mpr
    nlinarith [hz]
  have hLog := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hRatio
  have hLog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hLog64] at hLog
  unfold SmallMean.A
  nlinarith [hLog, Certificates.Mixed.log_two_gt_69]

theorem doubleCapLowTail_B_ge_207 {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    207 / 100 ≤ biasB z := by
  have hD : 0 < 1 - z * z := by nlinarith
  have hD16 : 1 - z * z ≤ (1 / 16 : ℝ) := by nlinarith [hz]
  have hLog := Real.log_le_log hD hD16
  have hLog16 : Real.log (1 / 16 : ℝ) = -4 * Real.log 2 := by
    rw [show (1 / 16 : ℝ) = ((2 : ℝ) ^ (4 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  rw [hLog16] at hLog
  unfold biasB
  nlinarith [hLog, Certificates.Mixed.log_two_gt_69]

theorem doubleCapLowTail_A_le_B {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) :
    SmallMean.A z ≤ biasB z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hD : 0 < 1 - z * z := by nlinarith
  have hPlus : Real.log (1 + z) ≤ Real.log 2 :=
    Real.log_le_log hp (by linarith)
  have hLogD : Real.log (1 - z * z) =
      Real.log (1 + z) + Real.log (1 - z) := by
    rw [show 1 - z * z = (1 + z) * (1 - z) by ring,
      Real.log_mul hp.ne' hm.ne']
  unfold SmallMean.A biasB
  rw [Real.log_div hp.ne' hm.ne', hLogD]
  linarith only [hPlus]

theorem doubleCapLowTail_E_le_five_fourths_gap_B {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    biasE z ≤ (5 / 4) * (1 - z) * biasB z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hLog := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 2) hp)
  have hLogTerm : Real.log 2 - Real.log (1 + z) ≤
      (1 - z) / (1 + z) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hLog
    have hFrac : 2 / (1 + z) - 1 = (1 - z) / (1 + z) := by
      field_simp [hp.ne']
      ring
    simpa only [hFrac] using hLog
  have hEIdentity : biasE z = (1 - z) * SmallMean.A z +
      (Real.log 2 - Real.log (1 + z)) := by
    unfold biasE SmallMean.A
    rw [Real.log_div hp.ne' hm.ne']
    ring
  have hEUpper : biasE z ≤
      (1 - z) * SmallMean.A z + (1 - z) / (1 + z) := by
    rw [hEIdentity]
    linarith only [hLogTerm]
  have hAB := doubleCapLowTail_A_le_B hz0 hz1
  have hB := doubleCapLowTail_B_ge_207 hz hz1
  have hDen : (4 : ℝ) ≤ (1 + z) * biasB z := by
    have h := mul_le_mul_of_nonneg_left hB hp.le
    nlinarith [h, hz]
  have hFrac : 1 / (1 + z) ≤ biasB z / 4 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [hDen]
  have hAProd := mul_le_mul_of_nonneg_left hAB hm.le
  have hFracProd := mul_le_mul_of_nonneg_left hFrac hm.le
  have hFracProd' : (1 - z) / (1 + z) ≤
      (1 - z) * biasB z / 4 := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hFracProd
  nlinarith only [hEUpper, hAProd, hFracProd']

#print axioms doubleCapLowTail_A_ge_207
#print axioms doubleCapLowTail_B_ge_207
#print axioms doubleCapLowTail_A_le_B
#print axioms doubleCapLowTail_E_le_five_fourths_gap_B

end GeneralCK

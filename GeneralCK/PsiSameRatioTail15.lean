import GeneralCK.PsiSameRatioTail16
import GeneralCK.LowInformationMeans

/-!
# Same-side ratio tail through `a/b≤2⁻¹⁵`

The checked quartic upper bound for the binary bias deficit sharpens the
second posterior of the deterministic entropy chain. The resulting Jensen
entropy drop is at most `5(b-a)/8`, exactly matching the fifteen-unit odds
cost with the existing profile slope bound twelve.
-/

namespace GeneralCK
open Set
namespace PsiSameRatioTail15

theorem biasDeficit_le_three_quarters_sq {r : ℝ}
    (hr : 0 ≤ r) (hru : r ≤ 1 / 3) :
    PsiSmallDistance.biasDeficit r ≤ (3 / 4) * r ^ 2 := by
  have hr1 : r < 1 := by linarith
  have hsq : r ^ 2 ≤ 1 / 9 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hru)]
  have hn : 0 < 1 - r ^ 2 := by linarith
  have hden : 0 < 12 * (1 - r ^ 2) := by positivity
  have hf : r ^ 2 / (12 * (1 - r ^ 2)) ≤ (1 / 96 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hsq]
  have hc := LowInformation.Cn_upper_sharp hr hr1
  have hm := mul_le_mul_of_nonneg_left hf (sq_nonneg r)
  have he : r ^ 2 * (r ^ 2 / (12 * (1 - r ^ 2))) =
      r ^ 4 / (12 * (1 - r ^ 2)) := by ring
  rw [he] at hm
  have hcore : SmallMean.Cn r ≤ (49 / 96) * r ^ 2 := by
    linarith only [hc, hm]
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Certificates.PilotData.log_two.1
    norm_num at h
    linarith
  have hcoeff : (49 / 96 : ℝ) ≤ (3 / 4) * Real.log 2 := by linarith
  have hbound := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg r)
  unfold PsiSmallDistance.biasDeficit
  apply (div_le_iff₀ log_two_pos).mpr
  nlinarith only [hcore, hbound]

theorem entropy_drop_le_five_eighths {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (5 / 8) * (b - a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hbalance : 3 * (b - a) ≤ 2 - a - b := by linarith
  have hratio : 0 ≤ (b - a) / (2 - a - b) ∧
      (b - a) / (2 - a - b) ≤ 1 / 3 := by
    constructor
    · positivity
    · apply (div_le_iff₀ ht).mpr
      linarith
  have hp := PsiSameRatioTail.entropy_chord (p := a / (a + b)) (by positivity)
    ((div_le_iff₀ hs).mpr (by linarith))
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (a + b) / 2 by linarith)
  have hep : ((a + b) / 2) * (2 * (a / (a + b))) = a := by field_simp
  rw [hep] at hp'
  have hposterior : (1 - b) / (2 - a - b) =
      (1 - (b - a) / (2 - a - b)) / 2 := by
    field_simp
    ring
  have hcap := biasDeficit_le_three_quarters_sq hratio.1 hratio.2
  rw [PsiSmallDistance.biasDeficit_eq] at hcap
  have hsecond := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 1 - (a + b) / 2 by linarith)
  have hprod := mul_le_mul_of_nonneg_left hbalance hd
  have hsecondBound :
      (1 - (a + b) / 2) *
          (1 - H ((1 - (b - a) / (2 - a - b)) / 2)) ≤ (b - a) / 8 := by
    have hident :
        (1 - (a + b) / 2) *
          ((3 / 4) * ((b - a) / (2 - a - b)) ^ 2) =
          (3 / 4) * ((b - a) ^ 2 / (2 * (2 - a - b))) := by
      field_simp
      ring
    rw [hident] at hsecond
    have hden : 0 < 2 * (2 - a - b) := by positivity
    have hfrac : (b - a) ^ 2 / (2 * (2 - a - b)) ≤ (b - a) / 6 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hprod]
    have hscaled := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 3 / 4)
    nlinarith only [hsecond, hscaled]
  rw [← hposterior] at hsecondBound
  rw [deterministic_entropy_chain ha ha1 hb0 hb1]
  nlinarith only [hp', hsecondBound]

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a / b ≤ 1 / 32768) :
    (15 / 2) * (b - a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2 : ℝ) ^ (15 : ℕ) ≤ b / a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log (show (0 : ℝ) < 2 ^ (15 : ℕ) by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1 - a) - Real.log (1 - b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a - J b =
      (Real.log (b / a) + (Real.log (1 - a) - Real.log (1 - b))) / Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (15 : ℝ) ≤ J a - J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b - a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail15

namespace InteriorLaw
theorem same_ratio_tail15_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hr : μ.a / μ.b ≤ 1 / 32768) : μ.splitBound ≤ μ.cost := by
  have ha0 := μ.a_interior.1
  have hb0 := μ.b_interior.1
  have hm0 : 0 ≤ μ.midpoint := by
    unfold midpoint
    linarith
  have hm : μ.midpoint ≤ 2501 / 10000 := by
    have hr' := (div_le_iff₀ hb0).mp hr
    unfold midpoint
    linarith
  have hIm : μ.information ≤ H μ.midpoint := by
    unfold information meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hd : μ.entropyDrop ≤ (5 / 8) * (μ.b - μ.a) :=
    PsiSameRatioTail15.entropy_drop_le_five_eighths ha0 hab hb
  have hcost : (15 / 2) * (μ.b - μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail15.ratio_tail_cost ha0 hab μ.b_interior.2 hr
  have hi := μ.information_mem
  by_cases hIz : μ.information = 0
  · have hd0 : μ.entropyDrop = 0 := by
      rw [μ.information_eq] at hIz
      linarith [μ.entropyDrop_nonneg, μ.meanDeficit_mem.1]
    have hnonneg : 0 ≤ μ.cost := by
      have hc := (μ.interiorCost_le_psiLogSumCostFloor).trans μ.psiLogSumCostFloor_le_cost
      linarith
    simpa [splitBound, hd0] using hnonneg
  · have hIp : 0 < μ.information := lt_of_le_of_ne hi.1 (Ne.symm hIz)
    have hs : deriv Scalar.P μ.information ≤ 12 :=
      PsiSameRatioTail24.slope_le_twelve hIp hIm hm0 hm
    have hinc := Scalar.P_increment_upper μ.meanDeficit_mem.1
      (show μ.meanDeficit ≤ μ.information by
        rw [μ.information_eq]
        linarith [μ.entropyDrop_nonneg]) hIp hi.2
    rw [μ.information_eq] at hinc
    have hmul := mul_le_mul_of_nonneg_left hs μ.entropyDrop_nonneg
    rw [μ.information_eq] at hmul
    have hsbound : μ.splitBound ≤ interiorCost μ.a μ.b := by
      unfold splitBound
      nlinarith only [hinc, hmul, hd, hcost]
    exact hsbound.trans
      ((μ.interiorCost_le_psiLogSumCostFloor).trans μ.psiLogSumCostFloor_le_cost)

end InteriorLaw

theorem sameSidePsiRatioTail15Owner {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hr : μ.a / μ.b ≤ 1 / 32768)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail15_splitBound hab hb hr)

end GeneralCK

#print axioms GeneralCK.PsiSameRatioTail15.biasDeficit_le_three_quarters_sq
#print axioms GeneralCK.PsiSameRatioTail15.entropy_drop_le_five_eighths
#print axioms GeneralCK.InteriorLaw.same_ratio_tail15_splitBound
#print axioms GeneralCK.sameSidePsiRatioTail15Owner

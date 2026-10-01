import GeneralCK.PsiSameRatioTail24
import GeneralCK.PsiSmallDistanceLowEntropy

/-!
# A stronger same-side entropy chain and ratio tail

The second posterior in the deterministic entropy chain has bias at most
one third when `a≤b≤1/2`. Its quadratic deficit then reduces the Jensen
entropy drop from `b-a` to `2(b-a)/3`. The existing slope bound twelve
therefore only requires an eight-unit cost, extending the ratio tail to
`a/b≤2⁻¹⁶` for every child entropy split.
-/

namespace GeneralCK
open Set
namespace PsiSameRatioTail16

theorem entropy_drop_le_two_thirds {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (2 / 3) * (b - a) := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have hratio : 0 ≤ (b - a) / (2 - a - b) ∧
      (b - a) / (2 - a - b) ≤ 1 := by
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
  have hcap := PsiSmallDistance.biasDeficit_le_sq
    (r := (b - a) / (2 - a - b)) (abs_le.mpr ⟨by linarith [hratio.1], hratio.2⟩)
  rw [PsiSmallDistance.biasDeficit_eq] at hcap
  have hsecond := mul_le_mul_of_nonneg_left hcap
    (show 0 ≤ 1 - (a + b) / 2 by linarith)
  have hbalance : 3 * (b - a) ≤ 2 - a - b := by linarith
  have hprod := mul_le_mul_of_nonneg_left hbalance hd
  have hsecondBound :
      (1 - (a + b) / 2) *
          (1 - H ((1 - (b - a) / (2 - a - b)) / 2)) ≤ (b - a) / 6 := by
    have hident :
        (1 - (a + b) / 2) * ((b - a) / (2 - a - b)) ^ 2 =
          (b - a) ^ 2 / (2 * (2 - a - b)) := by
      field_simp
      ring
    rw [hident] at hsecond
    have hden : 0 < 2 * (2 - a - b) := by positivity
    have hfrac : (b - a) ^ 2 / (2 * (2 - a - b)) ≤ (b - a) / 6 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hprod]
    exact hsecond.trans hfrac
  rw [← hposterior] at hsecondBound
  rw [deterministic_entropy_chain ha ha1 hb0 hb1]
  nlinarith only [hp', hsecondBound]

theorem ratio_tail_cost {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (hr : a / b ≤ 1 / 65536) :
    8 * (b - a) ≤ interiorCost a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a < 1 := hab.trans_lt hb
  have hratio : (2 : ℝ) ^ (16 : ℕ) ≤ b / a := by
    have hr' := (div_le_iff₀ hb0).mp hr
    apply (le_div_iff₀ ha).mpr
    norm_num
    linarith
  have hl := Real.log_le_log (show (0 : ℝ) < 2 ^ (16 : ℕ) by positivity) hratio
  rw [Real.log_pow] at hl
  have hc : 0 ≤ Real.log (1 - a) - Real.log (1 - b) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have he : J a - J b =
      (Real.log (b / a) + (Real.log (1 - a) - Real.log (1 - b))) / Real.log 2 := by
    unfold J
    rw [Real.log_div (by linarith) ha.ne', Real.log_div (by linarith) hb0.ne',
      Real.log_div hb0.ne' ha.ne']
    ring
  have hj : (16 : ℝ) ≤ J a - J b := by
    rw [he]
    apply (le_div_iff₀ log_two_pos).mpr
    norm_num at hl
    linarith
  have hm := mul_le_mul_of_nonneg_left hj (show 0 ≤ b - a by linarith)
  unfold interiorCost
  nlinarith only [hm]

end PsiSameRatioTail16

namespace InteriorLaw
theorem same_ratio_tail16_splitBound {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hr : μ.a / μ.b ≤ 1 / 65536) : μ.splitBound ≤ μ.cost := by
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
  have hd : μ.entropyDrop ≤ (2 / 3) * (μ.b - μ.a) :=
    PsiSameRatioTail16.entropy_drop_le_two_thirds ha0 hab hb
  have hcost : 8 * (μ.b - μ.a) ≤ interiorCost μ.a μ.b :=
    PsiSameRatioTail16.ratio_tail_cost ha0 hab μ.b_interior.2 hr
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

theorem sameSidePsiRatioTail16Owner {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2)
    (hr : μ.a / μ.b ≤ 1 / 65536)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  μ.gap_le_of_splitBound hactive (μ.same_ratio_tail16_splitBound hab hb hr)

end GeneralCK

#print axioms GeneralCK.PsiSameRatioTail16.entropy_drop_le_two_thirds
#print axioms GeneralCK.InteriorLaw.same_ratio_tail16_splitBound
#print axioms GeneralCK.sameSidePsiRatioTail16Owner

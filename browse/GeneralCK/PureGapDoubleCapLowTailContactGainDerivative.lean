import GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin
import GeneralCK.Certificates.MixedConstants

/-! Exact derivative of the positive contact contribution to the
double-cap slope. It measures the loss when the contact lies below the
inverse-entropy bias. -/

namespace GeneralCK

open Reflection Certificates.Reflection

noncomputable def doubleCapContactGain (c : ℝ) : ℝ :=
  c ^ 2 / ((1 - c ^ 2) * biasB c)

theorem doubleCapContactGain_hasDerivAt {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    HasDerivAt doubleCapContactGain
      (c * (2 * biasB c - c ^ 2) /
        (((1 - c ^ 2) * biasB c) ^ 2)) c := by
  have hgap : 0 < 1 - c ^ 2 := by nlinarith
  have hB : 0 < biasB c := biasB_pos hc hc1
  have hD : (1 - c ^ 2) * biasB c ≠ 0 := (mul_pos hgap hB).ne'
  have hGap := ((hasDerivAt_id c).pow 2).const_sub 1
  have hDen := hGap.mul (hasDerivAt_biasB (by linarith) hc1)
  have hNum := (hasDerivAt_id c).pow 2
  have hRaw := hNum.div hDen hD
  convert! hRaw using 1
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  field_simp [hD, hgap.ne', hB.ne']
  norm_num
  ring

theorem doubleCapContactGain_deriv_pos {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    0 < deriv doubleCapContactGain c := by
  rw [(doubleCapContactGain_hasDerivAt hc hc1).deriv]
  have hgap : 0 < 1 - c ^ 2 := by nlinarith
  have hB : (69 / 100 : ℝ) < biasB c := by
    have hlog : Real.log (1 - c * c) ≤ 0 :=
      Real.log_nonpos (by nlinarith) (by nlinarith)
    unfold biasB
    linarith [Certificates.Mixed.log_two_gt_69]
  have hnum : 0 < c * (2 * biasB c - c ^ 2) := by
    apply mul_pos hc
    nlinarith [hB]
  exact div_pos hnum (sq_pos_of_pos (mul_pos hgap (by linarith [hB])))

#print axioms doubleCapContactGain_hasDerivAt
#print axioms doubleCapContactGain_deriv_pos

end GeneralCK

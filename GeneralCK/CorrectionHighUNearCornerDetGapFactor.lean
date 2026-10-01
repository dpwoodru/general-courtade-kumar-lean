import GeneralCK.CorrectionHighUNearCornerDetOnly
import Mathlib.Analysis.Calculus.DSlope

/-!
An exact removal of the squared probability gap from the actual determinant.
The coefficient uses derivative-extended secants. No sign of that coefficient
is assumed or proved in this module.
-/

namespace GeneralCK.Correction.HighU

noncomputable def regularBias (u w : ℝ) : ℝ :=
  Reflection.regularContact (2 * (w - u) / Natural.entropySum u w)

noncomputable def regularFsGap (u w : ℝ) : ℝ :=
  dslope (fun v => Natural.Fs (regularBias u v)) u w

noncomputable def regularWeight (u w : ℝ) : ℝ :=
  2 * Natural.Fss (regularBias u w) (Natural.entropySum u w)

noncomputable def detGapCoefficient (d q h J j R W S : ℝ) : ℝ :=
  let q' := q + h * d - d ^ 2
  let J' := J + d * j
  let U := (q * (j + 2 * R) - 1) / J + d
  let V := 2 + ((q * (j + 2 * R) - 1) * j -
    (h - d) * (j + 2 * R) * J) / (J * J')
  let Z := h - d - (q * J + q' * J') / S
  let z := -q * (1 + d * J / S)
  let m := q + q' + d * U - W * z ^ 2
  J' * (m * (V - W * Z ^ 2) - (U - W * z * Z) ^ 2)

noncomputable def actualDetGapCoefficient (u w : ℝ) : ℝ :=
  detGapCoefficient (w - u) (Natural.qp u) (1 - 2 * u) (Natural.jn u)
    (dslope Natural.jn u w) (regularFsGap u w) (regularWeight u w)
    (Natural.entropySum u w)

private noncomputable def determinantModel (d q h J j R W S : ℝ) : ℝ :=
  let q' := q + h * d - d ^ 2
  let J' := J + d * j
  let a := (q * (J + J' + 2 * d * R) + d * (J * h - 1)) / J
  let n := q' * (J + J' - 2 * d * R) + d * (1 - J' * (h - 2 * d))
  let z := -q - d * q * J / S
  let z' := q' * (1 - d * J' / S)
  a * n - J' * (q + q') ^ 2 -
    W * (J' * a * z' ^ 2 + n * z ^ 2 + 2 * J' * (q + q') * z * z')

set_option maxHeartbeats 800000 in
theorem determinantModel_gap_factor
    (d q h J j R W S : ℝ) (hJ : J ≠ 0) (hJ' : J + d * j ≠ 0) (hS : S ≠ 0) :
    determinantModel d q h J j R W S = d ^ 2 * detGapCoefficient d q h J j R W S := by
  unfold determinantModel detGapCoefficient
  field_simp [hJ, hJ', hS]
  <;> ring

@[simp] theorem regularBias_diagonal (u : ℝ) : regularBias u u = 0 := by
  simp [regularBias]

@[simp] theorem naturalFs_zero : Natural.Fs 0 = 0 := by
  simp [Natural.Fs]

theorem regularFsGap_mul_gap (u w : ℝ) :
    (w - u) * regularFsGap u w = Natural.Fs (regularBias u w) := by
  have h := sub_smul_dslope (fun v => Natural.Fs (regularBias u v)) u w
  simpa only [regularFsGap, smul_eq_mul, regularBias_diagonal, naturalFs_zero, sub_zero] using h

theorem natural_jn_nonzero {u : ℝ} (hu : 0 < u) (hu1 : u < 1 / 2) :
    Natural.jn u ≠ 0 := by
  have hJ := J_pos hu hu1
  have heq : Natural.jn u = Real.log 2 * J u := by
    unfold Natural.jn J
    field_simp [log_two_pos.ne']
  rw [heq]
  exact (mul_pos log_two_pos hJ).ne'

/-- The actual determinant has an exact squared-gap factor. -/
theorem kdet_eq_gap_sq_mul_coefficient
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1 / 2) :
    Natural.kdet u w = (w - u) ^ 2 * actualDetGapCoefficient u w := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  have hwJ := natural_jn_nonzero (hu.trans huw) hw
  have hS : Natural.entropySum u w ≠ 0 := by
    apply ne_of_gt
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hjs : Natural.jn u + (w - u) * dslope Natural.jn u w = Natural.jn w := by
    have h := sub_smul_dslope Natural.jn u w
    simp only [smul_eq_mul] at h
    linarith
  have hfs : (w - u) * regularFsGap u w = Natural.Fs (Natural.contact u w) := by
    rw [regularFsGap_mul_gap]
    rw [contact_eq_regularContact hu huw hw]
    rfl
  have hW : regularWeight u w = Natural.weight u w := by
    unfold regularWeight Natural.weight
    rw [contact_eq_regularContact hu huw hw]
    rfl
  have hfs2 : 2 * (w - u) * regularFsGap u w = 2 * Natural.Fs (Natural.contact u w) := by
    nlinarith only [hfs]
  have hq : Natural.qp u + (1 - 2 * u) * (w - u) - (w - u) ^ 2 = Natural.qp w := by
    unfold Natural.qp
    ring
  have he := determinantModel_gap_factor (w - u) (Natural.qp u) (1 - 2 * u)
    (Natural.jn u) (dslope Natural.jn u w) (regularFsGap u w) (regularWeight u w)
    (Natural.entropySum u w) huJ (by simpa only [hjs] using hwJ) hS
  change _ = (w - u) ^ 2 * actualDetGapCoefficient u w at he
  rw [determinantModel, hq, hjs, hfs2, hW,
    show 1 - 2 * u - 2 * (w - u) = 1 - 2 * w by ring] at he
  simpa only [Natural.kdet, Natural.au, Natural.nw, Natural.zu, Natural.zw] using he

/-- After exact gap removal, the two raw wedge lower bounds are equivalent
to these coefficient bounds. This statement adds no positivity premise. -/
theorem nearCorner_det_bounds_iff_gap_coefficient
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    (2 * rho ^ 2 * t ^ 9 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t) ↔
      2 * t ^ 7 ≤ actualDetGapCoefficient (1 / 2 - t) (1 / 2 - (1 - rho) * t)) ∧
    (2 * rho ^ 4 * t ^ 7 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t) ↔
      2 * rho ^ 2 * t ^ 5 ≤
        actualDetGapCoefficient (1 / 2 - t) (1 / 2 - (1 - rho) * t)) := by
  have hu : 0 < (1 / 2 : ℝ) - t := by linarith
  have huw : (1 / 2 : ℝ) - t < 1 / 2 - (1 - rho) * t := by nlinarith [mul_pos hr ht]
  have hw : (1 / 2 : ℝ) - (1 - rho) * t < 1 / 2 := by
    nlinarith [mul_pos (show 0 < 1 - rho by linarith) ht]
  rw [kdet_eq_gap_sq_mul_coefficient hu huw hw,
    show (1 / 2 - (1 - rho) * t) - (1 / 2 - t) = rho * t by ring]
  have hd : 0 < (rho * t) ^ 2 := by positivity
  constructor
  · rw [show 2 * rho ^ 2 * t ^ 9 = (rho * t) ^ 2 * (2 * t ^ 7) by ring]
    exact mul_le_mul_iff_right₀ hd
  · rw [show 2 * rho ^ 4 * t ^ 7 = (rho * t) ^ 2 * (2 * rho ^ 2 * t ^ 5) by ring]
    exact mul_le_mul_iff_right₀ hd

#print axioms determinantModel_gap_factor
#print axioms regularFsGap_mul_gap
#print axioms kdet_eq_gap_sq_mul_coefficient
#print axioms nearCorner_det_bounds_iff_gap_coefficient

end GeneralCK.Correction.HighU

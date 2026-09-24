import GeneralCK.CorrectionHighUNearCornerDetGapFactor
import GeneralCK.CorrectionHighUNearCornerRegularContact

/-!
# CKLaneA1.Identities — algebraic identities for the scaled correction kernel

Lane A1 (correction arm `u < 1/50`).  Pure algebra: the scaled gap coefficient
`(1/J) * detGapCoefficient` and `m11` expressed in "atom" variables that the interval
checker encloses.  No numerical facts are assumed here.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

/-- Scaled gap-coefficient formula in atoms (`t = 1/J`, `ku = q*J`, `hh = 1-2u`). -/
noncomputable def feTcoef (t qu ku Jw qw s S R W hh : ℝ) : ℝ :=
  let qj := (qu*Jw - ku)/s
  let tj := (t*Jw - 1)/s
  let A1 := qj + 2*qu*R - 1
  let U := t*A1 + s
  let tJV := 2*t*Jw + A1*t*tj - (hh - s)*(tj + 2*(t*R))
  let Z := hh - s - (ku + qw*Jw)/S
  let z := -qu - s*ku/S
  let m := qu + qw + s*U - W*(z*z)
  let tJw := t*Jw
  m*(tJV - tJw*W*(Z*Z)) - tJw*((U - W*z*Z)*(U - W*z*Z))

set_option maxHeartbeats 4000000 in
/-- Abstract algebraic form of the scaling identity. -/
theorem detGap_scaled (d q h J j R W S : ℝ) (hJ : J ≠ 0) (hJ' : J + d*j ≠ 0) (hS : S ≠ 0)
    (hd : d ≠ 0) :
    (1/J) * detGapCoefficient d q h J j R W S =
      feTcoef (1/J) q (q*J) (J + d*j) (q + h*d - d^2) d S R W h := by
  unfold detGapCoefficient feTcoef
  simp only []
  field_simp
  ring

/-- The scaled gap coefficient in natural atoms. -/
theorem tcoef_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    (1 / jn u) * actualDetGapCoefficient u w =
      feTcoef (1 / jn u) (qp u) (qp u * jn u) (jn w) (qp w) (w - u) (entropySum u w)
        (regularFsGap u w) (regularWeight u w) (1 - 2*u) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  have hwJ := natural_jn_nonzero (hu.trans huw) hw
  have hS : entropySum u w ≠ 0 := by
    apply ne_of_gt
    unfold entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hd : w - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huw)
  have hjs : jn u + (w - u) * dslope jn u w = jn w := by
    have h := sub_smul_dslope jn u w
    simp only [smul_eq_mul] at h
    linarith
  have hq : qp u + (1 - 2*u)*(w - u) - (w - u)^2 = qp w := by
    unfold qp; ring
  have h := detGap_scaled (w - u) (qp u) (1 - 2*u) (jn u) (dslope jn u w)
    (regularFsGap u w) (regularWeight u w) (entropySum u w) huJ (by rw [hjs]; exact hwJ) hS hd
  rw [hjs, hq] at h
  exact h

/-- The left minor in atoms. -/
noncomputable def feM11 (t qu ku Jw s S F W hh : ℝ) : ℝ :=
  let z := -qu - s*ku/S
  qu*(1 + t*(Jw + 2*F)) + s*(hh - t) - W*(z*z)

theorem m11_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    m11 u w = feM11 (1 / jn u) (qp u) (qp u * jn u) (jn w) (w - u) (entropySum u w)
      (Fs (contact u w)) (weight u w) (1 - 2*u) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  unfold m11 au zu feM11
  simp only []
  field_simp
  ring

#print axioms detGap_scaled
#print axioms tcoef_identity
#print axioms m11_identity

end CKLaneA1

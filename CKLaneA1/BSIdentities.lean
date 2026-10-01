import CKLaneA1.Identities

/-!
# CKLaneA1.BSIdentities — scaled identities for the both-small chart

With `r = u/w`, `p = 1/jn w`, `τ = jn w/jn u`, `ĵ = w·(jn w − jn u)/(w − u)`, `σ = −τ ĵ`,
`ν = 1/(1+σ)` and the scaled atoms below, `ν·τ·coef` and `m11/w` are rational functions
of atoms that stay bounded as `w → 0`, `u/w → 0` and `u/w → 1`.  Pure algebra.
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

/-- Normalized both-small gap coefficient `ν τ coef` in scaled atoms. -/
noncomputable def bsC (tau p om qu qw sh Sp kh qjh nu nus Rh Wh hh hms : ℝ) : ℝ :=
  let A1 := qjh + 2*p*qu*Rh - 1
  let Uh := tau*A1 + om*sh
  let Z := hms - (kh + qw)/Sp
  let zh := -(qu + sh*kh/Sp)
  let mh := qu + qw + p*sh*Uh - p*Wh*(zh*zh)
  let nT := 2*tau*om*nu - p*tau*A1*nus + hms*(nus - 2*p*tau*Rh*nu)
  mh*(nT - nu*tau*Wh*(Z*Z)) - nu*tau*p*((Uh - Wh*zh*Z)*(Uh - Wh*zh*Z))

/-- Scaled left minor `m11 / w` in atoms. -/
noncomputable def bsM (tau p qu sh Sp kh F Wh hh : ℝ) : ℝ :=
  let zh := -(qu + sh*kh/Sp)
  qu*(1 + tau + 2*p*tau*F) + sh*(hh - p*tau) - p*Wh*(zh*zh)

set_option maxHeartbeats 16000000 in
/-- Abstract algebraic form of the both-small scaling identity, with `ν` a free variable and
`νσ` passed as `ν * (-(Jw * w * tj))`, `tj = (t Jw - 1)/s`.  Relates the both-small scaled
coefficient to the fixed-edge scaled coefficient `feTcoef`. -/
theorem bs_from_fe (t qu ku Jw qw s S R W hh w nu : ℝ) (hw : w ≠ 0) (hJw : Jw ≠ 0)
    (hs : s ≠ 0) (hS : S ≠ 0) :
    bsC (t*Jw) (1/Jw) (w*Jw) (qu/w) (qw/w) (s/w) ((1/Jw)*S/w) ((1/Jw)*ku/w)
        ((qu*Jw - ku)/s) nu (nu*(-(Jw*w*((t*Jw - 1)/s)))) (w*R/(1/Jw)) (w*W/(1/Jw))
        hh (hh - s) =
      nu*Jw*feTcoef t qu ku Jw qw s S R W hh := by
  unfold bsC feTcoef
  simp only []
  field_simp
  ring

/-- The both-small scaled coefficient identity in natural atoms. -/
theorem bsC_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2)
    (hσ : 1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))) ≠ 0) :
    (1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u))))) * (jn w / jn u)) *
        actualDetGapCoefficient u w =
      bsC (jn w / jn u) (1 / jn w) (w * jn w) (qp u / w) (qp w / w) ((w - u)/w)
        ((1 / jn w) * entropySum u w / w) ((1 / jn w) * (qp u * jn u) / w)
        ((qp u / w) * (w * ((jn w - jn u)/(w - u))))
        (1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u))))))
        ((1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))))) *
          (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))))
        (w * regularFsGap u w / (1 / jn w)) (w * regularWeight u w / (1 / jn w))
        (1 - 2*u) (1 - 2*u - w*((w - u)/w)) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  have hwJ := natural_jn_nonzero (hu.trans huw) hw
  have hS : entropySum u w ≠ 0 := by
    apply ne_of_gt
    unfold entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hd : w - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huw)
  have hw0 : w ≠ 0 := (hu.trans huw).ne'
  have hfe := tcoef_identity hu huw hw
  have hab := bs_from_fe (1 / jn u) (qp u) (qp u * jn u) (jn w) (qp w) (w - u)
    (entropySum u w) (regularFsGap u w) (regularWeight u w) (1 - 2*u) w
    (1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))))) hw0 hwJ hd hS
  have e3 : -(jn w * w * ((1 / jn u * jn w - 1)/(w - u))) =
      -(jn w / jn u) * (w * ((jn w - jn u)/(w - u))) := by
    field_simp <;> ring
  have e1 : 1 / jn u * jn w = jn w / jn u := by ring
  have e2 : (qp u * jn w - qp u * jn u)/(w - u) =
      (qp u / w) * (w * ((jn w - jn u)/(w - u))) := by
    field_simp <;> ring
  have e4 : 1 - 2*u - (w - u) = 1 - 2*u - w*((w - u)/w) := by
    field_simp <;> ring
  rw [e3, e1, e2, e4] at hab
  rw [hab, ← hfe]
  ring

theorem bsM_identity {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    m11 u w = w * bsM (jn w / jn u) (1 / jn w) (qp u / w) ((w - u)/w)
      ((1 / jn w) * entropySum u w / w) ((1 / jn w) * (qp u * jn u) / w)
      (Fs (contact u w)) (w * weight u w / (1 / jn w)) (1 - 2*u) := by
  have huJ := natural_jn_nonzero hu (huw.trans hw)
  have hwJ := natural_jn_nonzero (hu.trans huw) hw
  have hS : entropySum u w ≠ 0 := by
    apply ne_of_gt
    unfold entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hw0 : w ≠ 0 := (hu.trans huw).ne'
  rw [m11_identity hu huw hw]
  unfold feM11 bsM
  simp only []
  field_simp
  ring

#print axioms bs_from_fe
#print axioms bsC_identity
#print axioms bsM_identity

end CKLaneA1

import GeneralCK.Certificates.E8LocalContactContraction
import GeneralCK.Certificates.E8CoupledTauCBox

/-! Proof-producing locally centered contact balls for E8 tau cells. -/

namespace GeneralCK.Certificates.E8LocalContactBall

open E8GaussianRatBall E8CoupledTauCBox E8LocalContactContraction
open Reflection.ComplexEntropy Reflection.ComplexGlobalAnalytic
open Reflection.ComplexDiscElementary

def localResidual (tauBall : RatBall) (z : GaussianRat) : RatBall :=
  (fixedPointImageBox tauBall (RatBall.point z.re z.im) logTwoBall).sub
    (RatBall.point z.re z.im)

def localContactBall (tauBall : RatBall) (z : GaussianRat) : RatBall :=
  { center := z
    radius := (25 / 21) *
      ((localResidual tauBall z).center.l1 + (localResidual tauBall z).radius) }

theorem localContactBall_sound_norm {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hzNorm : ‖z.val‖ ≤ (1 / 3 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) := by
  have hzMem : z.val ∈ Metric.closedBall (0 : ℂ) (1 / 3 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzNorm
  have hzContact : ‖z.val‖ ≤ (1103 / 2500 : ℝ) := hzNorm.trans (by norm_num)
  have hpoint : (RatBall.point z.re z.im).Holds z.val := by
    simpa [GaussianRat.val] using holds_point z.re z.im
  have hE := entropyBox_sound hpoint hzContact logTwoBall_holds
  have himage := holds_mul htauBall hE
  have hres : (localResidual tauBall z).Holds
      (contactMap entropyExt tau z.val - z.val) := by
    simpa [localResidual, fixedPointImageBox, contactMap, GaussianRat.val]
      using holds_sub himage hpoint
  have hresNorm : ‖contactMap entropyExt tau z.val - z.val‖ ≤
      (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) := by
    unfold RatBall.Holds E8ComplexBallKernel.InBall at hres
    calc
      ‖contactMap entropyExt tau z.val - z.val‖ ≤
          ‖(localResidual tauBall z).center.val‖ +
            ‖(contactMap entropyExt tau z.val - z.val) -
              (localResidual tauBall z).center.val‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ((localResidual tauBall z).center.l1 : ℝ) +
          (localResidual tauBall z).radius :=
        add_le_add (norm_val_le_l1 _) hres
      _ = _ := by norm_cast
  have hresDist : dist (contactMap entropyExt tau z.val) z.val ≤
      (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) := by
    simpa [dist_eq_norm] using hresNorm
  have hdist := fixedPointOnDisc_dist_le_residual htau hzMem
  unfold localContactBall RatBall.Holds E8ComplexBallKernel.InBall
  rw [dist_eq_norm] at hdist
  exact hdist.trans (by
    rw [show (((25 / 21 : ℚ) *
      ((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius) : ℚ) : ℝ) =
      (25 / 21 : ℝ) * (((localResidual tauBall z).center.l1 +
        (localResidual tauBall z).radius : ℚ) : ℝ) by
          push_cast
          norm_num]
    exact mul_le_mul_of_nonneg_left hresDist (by norm_num))

theorem localContactBall_sound_sq {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hz : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 ≤ (1 / 9 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) := by
  apply localContactBall_sound_norm htau htauBall
  have hsquare : ‖z.val‖ ^ 2 = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  nlinarith [norm_nonneg z.val]

theorem localContactBall_sound {tau : ℂ} {tauBall : RatBall} {z : GaussianRat}
    (htau : ‖tau‖ ≤ (2 / 5 : ℝ)) (htauBall : tauBall.Holds tau)
    (hz : (z.l1 : ℝ) ≤ (1 / 3 : ℝ)) :
    (localContactBall tauBall z).Holds (fixedPointOnDisc tau) :=
  localContactBall_sound_norm htau htauBall ((norm_val_le_l1 z).trans hz)

end GeneralCK.Certificates.E8LocalContactBall

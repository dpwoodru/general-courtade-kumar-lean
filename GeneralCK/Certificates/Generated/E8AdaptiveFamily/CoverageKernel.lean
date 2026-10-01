import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel

open E8ComplexBallKernel E8GaussianRatBall

def InSquare (x y h : ℝ) (tau : ℂ) : Prop :=
  x - h ≤ tau.re ∧ tau.re ≤ x + h ∧ y - h ≤ tau.im ∧ tau.im ≤ y + h

theorem childLL {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : tau.re ≤ x) (hy : tau.im ≤ y) :
    InSquare (x-h/2) (y-h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childLR {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : x ≤ tau.re) (hy : tau.im ≤ y) :
    InSquare (x+h/2) (y-h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childUL {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : tau.re ≤ x) (hy : y ≤ tau.im) :
    InSquare (x-h/2) (y+h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem childUR {x y h : ℝ} {tau : ℂ} (hs : InSquare x y h tau)
    (hx : x ≤ tau.re) (hy : y ≤ tau.im) :
    InSquare (x+h/2) (y+h/2) (h/2) tau := by
  unfold InSquare at hs ⊢
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem inBall_of_inSquare {x y h : ℝ} {tau : ℂ}
    (hs : InSquare x y h tau) (hh : 0 ≤ h) :
    InBall tau (x + y * Complex.I) (3/2*h) := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  unfold InBall
  have hre : (tau.re-x)^2 ≤ h^2 := by nlinarith
  have him : (tau.im-y)^2 ≤ h^2 := by nlinarith
  have hsquare : ‖tau - (x + y * Complex.I)‖^2 ≤ (3/2*h)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg h]
  nlinarith [norm_nonneg (tau - (x + y * Complex.I))]

theorem disc_in_root {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ)) :
    InSquare 0 0 (2/5) tau := by
  have hre := Complex.abs_re_le_norm tau
  have him := Complex.abs_im_le_norm tau
  rw [abs_le] at hre him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel

import GeneralCK.ReflectionSmallRatioMidpoint

namespace GeneralCK.Reflection.SmallRatio
open Set Certificates Certificates.Reflection

/-- A sound jet for the radius derivative supplies the quadratic majorant.
Only its midpoint value and uniform second derivative need numerical bounds. -/
theorem curvature_pos_of_midpoint_jet {a z p0 M : ℝ} {j : Jet2}
    (ha : 0<a) (ha' : a<1) (hz : 0<z) (hz' : z<1)
    (hj : j.SoundOn (Icc (a*(1-z)/2) (a*(1+z)/2)))
    (hvalue : ∀ s ∈ Icc (a*(1-z)/2) (a*(1+z)/2),
      j.value s=P a ((biasE a+biasE (a*z))/2) s)
    (hcenter : j.value (a/2) ≤ p0)
    (hsecond : ∀ s ∈ Icc (a*(1-z)/2) (a*(1+z)/2), j.second s ≤ M)
    (haccept : p0+M*(a*z)^2/24<2*a/(1-a^2)^2) : 0<curvature a (a*z) := by
  apply curvature_pos_of_midpoint_bound ha ha' hz hz' (p1 := j.first (a/2)) ?_ haccept
  intro s hs
  have hm : a/2 ∈ Icc (a*(1-z)/2) (a*(1+z)/2) := by
    constructor <;> nlinarith [mul_pos ha hz]
  have h := taylor_upper_on_interval hm ⟨hs.1.le,hs.2.le⟩
    (fun x hx => (hj x hx).1) (fun x hx => (hj x hx).2) hsecond
  rw [hvalue s ⟨hs.1.le,hs.2.le⟩] at h
  linarith

end GeneralCK.Reflection.SmallRatio

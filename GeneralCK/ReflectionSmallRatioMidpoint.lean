import GeneralCK.ReflectionSmallRatio
import GeneralCK.Certificates.MidpointBounds

namespace GeneralCK.Reflection.SmallRatio
open Set Certificates Certificates.Reflection Certificates.ReflectionExpression

/-- A quadratic majorant of P controls the contact difference with its exact
midpoint average. The entropy is fixed throughout the radius interval. -/
theorem difference_le_midpoint {a e l u p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (he : 0<e) (hl : 0<l) (hlu : l<u)
    (hP : ∀ s ∈ Ioo l u,
      P a e s ≤ p0+p1*(s-(l+u)/2)+M*(s-(l+u)/2)^2/2) :
    V a e u-V a e l ≤ (p0+M*(u-l)^2/24)*(u-l) := by
  have h := difference_le_midpoint_quadratic hlu
    (fun s hs => hasDerivAt_V ha ha' he (hl.trans_le hs.1)) hP
  convert! h using 1 <;> ring

theorem normalized_lower_of_midpoint {a b e p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (hb : 0<b) (hba : b<a) (he : 0<e)
    (hP : ∀ s ∈ Ioo ((a-b)/2) ((a+b)/2),
      P a e s ≤ p0+p1*(s-a/2)+M*(s-a/2)^2/2) :
    (2*a/(1-a^2)^2-(p0+M*b^2/24))/a^3 ≤
      (2*a*b/(1-a^2)^2+V a e ((a-b)/2)-V a e ((a+b)/2))/(a^3*b) := by
  have h := difference_le_midpoint ha ha' he (by linarith : 0<(a-b)/2)
    (by linarith : (a-b)/2<(a+b)/2) (p0 := p0) (p1 := p1) (M := M)
  have hm : ((a-b)/2+(a+b)/2)/2=a/2 := by ring
  have hb' : (a+b)/2-(a-b)/2=b := by ring
  simp only [hm,hb'] at h
  have hd := h hP
  have hgap : 1-a^2≠0 := by nlinarith
  calc
    _ = (2*a*b/(1-a^2)^2-(p0+M*b^2/24)*b)/(a^3*b) := by
      field_simp [ha.ne',hb.ne',hgap]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (mul_pos (pow_pos ha 3) hb).le

/-- Acceptance rule for the actual curvature. Numeric bounds on the center
value and second derivative suffice once the quadratic majorant is proved. -/
theorem curvature_pos_of_midpoint_bound {a z p0 p1 M : ℝ}
    (ha : 0<a) (ha' : a<1) (hz : 0<z) (hz' : z<1)
    (hP : ∀ s ∈ Ioo (a*(1-z)/2) (a*(1+z)/2),
      P a ((biasE a+biasE (a*z))/2) s ≤ p0+p1*(s-a/2)+M*(s-a/2)^2/2)
    (haccept : p0+M*(a*z)^2/24<2*a/(1-a^2)^2) : 0<curvature a (a*z) := by
  have hb : 0<a*z := mul_pos ha hz
  have hba : a*z<a := by nlinarith
  have he : 0<(biasE a+biasE (a*z))/2 := by
    rw [biasE_eq_log_mul_E (by linarith) ha',biasE_eq_log_mul_E (by linarith) (hba.trans ha')]
    have hmean := meanEntropy_pos (by linarith : -1<a) ha'
      (by linarith : -1<a*z) (hba.trans ha')
    convert! mul_pos log_two_pos hmean using 1
    unfold meanEntropy
    ring
  have h := normalized_lower_of_midpoint ha ha' hb hba he (p0 := p0) (p1 := p1) (M := M)
  rw [show (a-a*z)/2=a*(1-z)/2 by ring,show (a+a*z)/2=a*(1+z)/2 by ring] at h
  apply curvature_pos_of_normalizedValue_pos ha ha' hz hz'
  exact (div_pos (sub_pos.mpr haccept) (pow_pos ha 3)).trans_le (h hP)

end GeneralCK.Reflection.SmallRatio

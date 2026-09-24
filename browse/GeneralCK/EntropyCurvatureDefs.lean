import GeneralCK.EntropyRadialDerivatives
import GeneralCK.ProfileConvexity

namespace GeneralCK.EntropyCurvature

/-- The two natural-unit scalar signs in the upstream entropy-convexity proof. -/
noncomputable def polyP (x t B : ℝ) : ℝ :=
  B^3*(x*(1+t^2)-t)-x^3*t^2*(2*B-t^2)

noncomputable def polyR (x t B : ℝ) : ℝ :=
  4*B^3*(1+t^2)-2*B^2*t^3*x-8*B^2*t^2-6*B^2*t*x
    -B*t^5*x+3*B*t^4+9*B*t^3*x-3*t^5*x

noncomputable def xi (v : ℝ) : ℝ := Real.log 2*J v/2
noncomputable def P (v : ℝ) : ℝ := polyP (xi v) (1-2*v) (Certificates.Mixed.kap v)
noncomputable def R (v : ℝ) : ℝ := polyR (xi v) (1-2*v) (Certificates.Mixed.kap v)

/-- Natural entropy times natural entropy curvature of the perspective at its cap contact. -/
noncomputable def beta (v : ℝ) : ℝ :=
  2*Certificates.Mixed.hn v*(1-2*v)^2*(2*Certificates.Mixed.kap v-(1-2*v)^2) /
    ((Certificates.Mixed.kap v)^3*(4*v*(1-v))^2)

end GeneralCK.EntropyCurvature

import GeneralCK.PureGapCapAnalytic
import GeneralCK.SmallMeanPhiRetainedCutoff
import GeneralCK.ProfileConvexity
import GeneralCK.EntropyRadialDerivatives
import CKLaneN23.RightStationaryReduction

/-!
# Lane N23 — RA-stat (capFibers.rightStationary): the ray-convexity decomposition (DEFINITIONS)

Shared interface for lanes N23 and R1 (see `~/ck_lanes_20260923/N23/RS_PLAN.md`).

Degenerate-edge ray through the diagonal point `a = x = b`: for `b ∈ (0,1/2]`, `t ∈ [0,1]`, `d ∈ (0,b)`,
  `φ_{b,t}(d) = canonicalPureGap (b - t d) b (H (b - d)) (H b)`
(left entropy representative `u = b - d`, free mean `x = b - t d`). `rayGamma b t d` is the explicit
second derivative `φ''(d)`, written with the corpus curve calculus
(`hasDerivAt_F_curve`, `hasDerivAt_perspectiveSlope`, `hasDerivAt_eta`, `hasDerivAt_etaSlope`):
  `φ = ½((1-2b+3d) J(u) - d J(b)) + F(td,E) - F(d,E) + F(1-2b+td,E) - eta E - ½ F(1-2b+2td, H u)`,
  `E = (H u + H b)/2`, `E' = -J(u)/2`, `E'' = Jd1(u)/2`, `(H u)' = -J u`, `(H u)'' = Jd1 u`.
Numerically (float model, 388,680 grid points, `N23/work/rs/gammascan.py`) `rayGamma ≥ 1.18 ((1/2-b)^2 + d^2)`
away from the corner; at the corner `rayGamma ≈ 2A(t) q^2 + 6B(t) q d + 12C(t) d^2` (`q = 1/2 - b`), with
`A, B, C > 0` on `[0,1]` (exact corner series, `N23/work/rs/corner_series.py`).
Since `φ(0+) = φ'(0+) = 0`, `rayGamma ≥ 0` on a ray makes `φ ≥ 0` on it, which gives `RSValue` and hence
`RightStationaryProb` (stationarity is not needed).
-/

namespace CKLaneN23.RS

open GeneralCK

/-- `J'` (explicit). -/
noncomputable def Jd1 (v : ℝ) : ℝ := -1 / (Real.log 2 * v * (1 - v))

/-- `J''` (explicit). -/
noncomputable def Jd2 (v : ℝ) : ℝ := (1 - 2 * v) / (Real.log 2 * v ^ 2 * (1 - v) ^ 2)

/-- Second derivative of `δ ↦ F (s δ) (e δ)` along a curve with `s' = ds`, `s'' = 0`, `e' = de`,
`e'' = dde` (the right-hand side of `hasDerivAt_perspectiveSlope` with `dds = 0`). -/
noncomputable def raySec (s ds e de dde : ℝ) : ℝ :=
  ((ds - (s / e) * de) ^ 2 / e) * deriv (deriv (fun r => F r 1)) (s / e)
    + (-(s / e) * dde) * deriv (fun r => F r 1) (s / e) + dde * F (s / e) 1

/-- The ray second derivative `φ_{b,t}''(d)`. -/
noncomputable def rayGamma (b t d : ℝ) : ℝ :=
  -3 * Jd1 (b - d) + (1 - 2 * b + 3 * d) / 2 * Jd2 (b - d)
  + raySec (t * d) t ((H (b - d) + H b) / 2) (-(J (b - d)) / 2) (Jd1 (b - d) / 2)
  - raySec d 1 ((H (b - d) + H b) / 2) (-(J (b - d)) / 2) (Jd1 (b - d) / 2)
  + raySec (1 - 2 * b + t * d) t ((H (b - d) + H b) / 2) (-(J (b - d)) / 2) (Jd1 (b - d) / 2)
  - (Scalar.etaCurvature ((H (b - d) + H b) / 2) * (J (b - d) / 2) ^ 2
      + Scalar.etaSlope ((H (b - d) + H b) / 2) * (Jd1 (b - d) / 2))
  - raySec (1 - 2 * b + 2 * t * d) (2 * t) (H (b - d)) (-(J (b - d))) (Jd1 (b - d)) / 2

/-- Value positivity on the right cap face above the cutoff (implies `RightStationaryProb S`). -/
def RSValue (S : ℝ) : Prop :=
  ∀ a x b : ℝ, 0 < a → a < x → x < b → b ≤ 1 / 2 → S < x + b →
    0 ≤ canonicalPureGap x b (H a) (H b)

/-- Ray-convexity certificate, CORNER piece (owner: lane N23; exact-series Taylor model). -/
def GammaCorner (εc : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → (1 / 2 - b) + d ≤ εc →
    0 ≤ rayGamma b t d

/-- Ray-convexity certificate, NON-CORNER piece (owner: lane R1; interval / Taylor-model cover). -/
def GammaNonCorner (S εc : ℝ) : Prop :=
  ∀ b t d : ℝ, 0 ≤ t → t ≤ 1 → 0 < d → d < b → b ≤ 1 / 2 → S < 2 * b - t * d →
    εc ≤ (1 / 2 - b) + d → 0 ≤ rayGamma b t d

/-- Production split constant (corner = `a ≥ 2/5`). -/
noncomputable def epsC : ℝ := 1 / 10

/-- Value positivity drops the stationarity hypothesis. -/
theorem prob_of_value {S : ℝ} (h : RSValue S) : RightStationaryProb S := by
  intro a x b ha hax hxb hb hS _
  exact h a x b ha hax hxb hb hS

end CKLaneN23.RS

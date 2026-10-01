import GeneralCK.PureGapCapZeroReduction
import GeneralCK.RadialConvexity

/-!
# Exact scalar contract for the zero-cutoff double-cap endpoint

This removes the piecewise entropy floor and unfolds `phi` into the actual
entropy inverse and radial contact.  It is a reduction only: no numerical
sign is asserted here.
-/

namespace GeneralCK

noncomputable def doubleCapEndpointResidual (m h : ℝ) : ℝ :=
  4 * (H m - h) -
    ((1 - 2 * entropyInverse h) * J (entropyInverse h) -
      (1 - 2 * m) * J (radialContact (1 - 2 * m) h))

theorem doubleCap_endpoint_iff_residual_nonneg {m h : ℝ}
    (hm : 0 < m) (hm1 : m < 1 / 2) (hh : 0 < h) (hh1 : h ≤ 1) :
    phi m h ≤ 4 * (H m - h) ↔ 0 ≤ doubleCapEndpointResidual m h := by
  have hz : 0 < 1 - 2 * m := by linarith
  unfold phi
  rw [eta_eq_profile hh.le hh1]
  simp only [F, abs_of_pos hz, if_neg hz.ne']
  unfold doubleCapEndpointResidual
  constructor <;> intro hineq <;> linarith

noncomputable def doubleCapLowResidual (m : ℝ) : ℝ :=
  doubleCapEndpointResidual m (H (2 * m) / 2)

noncomputable def doubleCapHighResidual (m : ℝ) : ℝ :=
  doubleCapEndpointResidual m ((1 + H (2 * m - 1 / 2)) / 2)

/-- Exact one-dimensional certificate interface.  The two fields have
disjoint interiors and share only the explicit switch point through `low`. -/
structure CanonicalDoubleCapResidualCertificate : Prop where
  low : ∀ m, 0 < m → m ≤ 1 / 4 → 0 ≤ doubleCapLowResidual m
  high : ∀ m, 1 / 4 < m → m < 1 / 2 → 0 ≤ doubleCapHighResidual m

theorem strict_doubleCap_endpoint_of_residual_certificate
    (cert : CanonicalDoubleCapResidualCertificate) :
    ∀ m, 0 < m → m < 1 / 2 →
      phi m (capEntropyFloor m) ≤ 4 * (H m - capEntropyFloor m) := by
  intro m hm hm1
  unfold capEntropyFloor
  split_ifs with hquarter
  · have hh : 0 < H (2 * m) / 2 :=
      div_pos (H_pos (by linarith) (by linarith)) two_pos
    have hh1 : H (2 * m) / 2 ≤ 1 := by
      linarith [H_le_one (2 * m)]
    exact (doubleCap_endpoint_iff_residual_nonneg hm hm1 hh hh1).2
      (cert.low m hm hquarter)
  · have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    have hH0 : 0 ≤ H (2 * m - 1 / 2) := (H_pos hx0 hx1).le
    have hh : 0 < (1 + H (2 * m - 1 / 2)) / 2 := by linarith
    have hh1 : (1 + H (2 * m - 1 / 2)) / 2 ≤ 1 := by
      linarith [H_le_one (2 * m - 1 / 2)]
    exact (doubleCap_endpoint_iff_residual_nonneg hm hm1 hh hh1).2
      (cert.high m (lt_of_not_ge hquarter) hm1)

theorem canonicalDoubleCapEntropyEndpoints_of_residual_certificate
    (cert : CanonicalDoubleCapResidualCertificate) :
    CanonicalDoubleCapEntropyEndpoints :=
  canonicalDoubleCapEntropyEndpoints_of_strict
    (strict_doubleCap_endpoint_of_residual_certificate cert)

#print axioms doubleCap_endpoint_iff_residual_nonneg
#print axioms strict_doubleCap_endpoint_of_residual_certificate
#print axioms canonicalDoubleCapEntropyEndpoints_of_residual_certificate

end GeneralCK

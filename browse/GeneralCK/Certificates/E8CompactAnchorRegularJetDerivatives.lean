import GeneralCK.Certificates.E8CompactAnchorDeltaJet

/-!
# Canonical inverse jet as actual regular second and third derivatives

The compact pilot's interval boxes enclose the canonical inverse `qJet`.
On the open positive slope range, its raw second and third components
coincide with the corresponding derivatives of `e8RegularQ`.
-/

namespace GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives

open GeneralCK Filter E8TAxisDeltaDirectionalJet

theorem qJet_d1_eq_deriv_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d1 y = deriv e8RegularQ y := by
  simpa only [qPrimeJet, shift] using qPrimeJet_d0_eq_deriv_regular hy

theorem qJet_d2_eq_deriv2_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d2 y = deriv (deriv e8RegularQ) y := by
  have heq : qJet.d1 =ᶠ[nhds y] deriv e8RegularQ := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact qJet_d1_eq_deriv_regular hz
  have h := Filter.EventuallyEq.deriv_eq heq
  rw [(qJet_soundAt hy).2.1.deriv] at h
  exact h

theorem qJet_d3_eq_deriv3_regular {y : ℝ}
    (hy : y ∈ e8SlopeRange) :
    qJet.d3 y = deriv (deriv (deriv e8RegularQ)) y := by
  have heq : qJet.d2 =ᶠ[nhds y]
      (fun z => deriv (deriv e8RegularQ) z) := by
    filter_upwards [e8SlopeRange_mem_nhds hy] with z hz
    exact qJet_d2_eq_deriv2_regular hz
  have h := Filter.EventuallyEq.deriv_eq heq
  rw [(qJet_soundAt hy).2.2.1.deriv] at h
  exact h

#print axioms qJet_d1_eq_deriv_regular
#print axioms qJet_d2_eq_deriv2_regular
#print axioms qJet_d3_eq_deriv3_regular

end GeneralCK.Certificates.E8CompactAnchorRegularJetDerivatives

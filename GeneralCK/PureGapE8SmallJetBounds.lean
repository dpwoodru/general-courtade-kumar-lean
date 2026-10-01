import GeneralCK.PureGapE8RegularizedInverse
import GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge
import GeneralCK.Certificates.E8OriginMixedKTransfer

/-!
# Unconditional coarse local bounds for the regular E8 inverse jet

The completed complex-disc certificate and exact Taylor coefficient boxes
already imply these deliberately loose bounds.  No new numerical owner is
needed at the small argument occurring in the two axis strips.
-/

namespace GeneralCK

open Set Filter Certificates
open E8OriginAnalyticCertificate E8OriginPositiveConsumer
open E8OriginRealTaylorTransfer E8OriginMixedKTransfer E8OriginRemainder

theorem qReal_first_three_jets_abs_le_one (cert : QuantitativeCertificate)
    {y : ℝ} (hy : 0 ≤ y) (hyR : y ≤ 4 / 25) (j : ℕ) (hj : j ≤ 2) :
    |iteratedDeriv j (qReal cert) y| ≤ 1 := by
  have ht := qReal_derivative_taylor_tail_le_scaled cert j (by omega)
    hy (r := 2 / 25) (by linarith) (by norm_num) (by norm_num)
  have htri := norm_add_le
    (iteratedDeriv j (qReal cert) y - qRealTaylorDerivative cert j y)
    (qRealTaylorDerivative cert j y)
  rw [sub_add_cancel] at htri
  have hb0 : (tailError 0 : ℝ) * (2 / 25 : ℝ) ^ 17 + (p0c : ℝ) * (2 / 25) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p0c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]
  have hb1 : (tailError 1 : ℝ) * (2 / 25 : ℝ) ^ 16 + (p1c : ℝ) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p1c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_range_succ]
  have hb2 : (tailError 2 : ℝ) * (2 / 25 : ℝ) ^ 15 + (p2c : ℝ) * (2 / 25) ≤ 1 := by
    norm_num [tailError, q17AbsBound, p2c, radius, coeffAbsUpper,
      a1, a3, a5, a7, a9, a11, a13, a15, Finset.sum_Icc_succ_top]
  rw [← Real.norm_eq_abs]
  interval_cases j
  · have hp := qRealTaylorDerivative_zero_le_p0c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb0)
  · have hp := qRealTaylorDerivative_one_le_p1c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb1)
  · have hp := qRealTaylorDerivative_two_le_p2c cert hy (r := 2 / 25)
      (by linarith) (by norm_num) (by norm_num [radius])
    exact htri.trans ((add_le_add ht hp).trans hb2)

theorem e8RegularQ_first_three_jets_abs_le_one {y : ℝ}
    (hy : y ∈ e8SlopeRange) (hyR : y < 4 / 25) (j : ℕ) (hj : j ≤ 2) :
    |iteratedDeriv j e8RegularQ y| ≤ 1 := by
  let cert := E8AdaptiveOriginOwnerBridge.quantitativeCertificate
  have hagree : RealAgreementOnOrigin cert :=
    E8TauDiscRealAgreement.realAgreementOnOrigin_of_globalDerivativeBound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  have heq : e8RegularQ =ᶠ[nhds y] qReal cert := by
    filter_upwards [e8SlopeRange_mem_nhds hy, Iio_mem_nhds hyR] with z hz hzR
    rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hz).le]
    exact (hagree z hz hzR.le).symm
  rw [heq.iteratedDeriv_eq j]
  exact qReal_first_three_jets_abs_le_one cert (e8SlopeRange_subset_pos hy).le hyR.le j hj

theorem e8RegularQ_small_jet_upper {y : ℝ} (hy : y ∈ e8SlopeRange)
    (hyR : y ≤ 1 / 50) :
    e8RegularQ y ≤ 1 ∧ deriv e8RegularQ y ≤ 1 ∧ deriv (deriv e8RegularQ) y ≤ 1 := by
  have hj (j : ℕ) (hj : j ≤ 2) : iteratedDeriv j e8RegularQ y ≤ 1 :=
    (le_abs_self _).trans (e8RegularQ_first_three_jets_abs_le_one hy (by linarith) j hj)
  exact ⟨by simpa using hj 0 (by omega),
    by simpa only [iteratedDeriv_one] using hj 1 (by omega),
    by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hj 2 (by omega)⟩

#print axioms qReal_first_three_jets_abs_le_one
#print axioms e8RegularQ_first_three_jets_abs_le_one
#print axioms e8RegularQ_small_jet_upper

end GeneralCK

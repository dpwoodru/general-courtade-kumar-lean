import GeneralCK.Certificates.E8OriginSourceKExactExtensional

namespace GeneralCK.Certificates.E8OriginSourceKExactAssembly

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceAffineReplay
open E8OriginRealTaylorTransfer
open E8OriginSourceKExactReplay
open E8OriginSourceKCoefficientReplay

noncomputable def sourceK (s t : Real) : Real :=
  -4 * qSourceTaylorDerivative 0 s * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (s + t) -
  8 * qSourceTaylorDerivative 0 t * qSourceTaylorDerivative 3 (2 * s + t) +
  4 * qSourceTaylorDerivative 0 (s + t) * qSourceTaylorDerivative 3 (2 * s + t) +
  qSourceTaylorDerivative 0 (2 * s + t) * qSourceTaylorDerivative 3 (s + t) -
  4 * qSourceTaylorDerivative 1 s * qSourceTaylorDerivative 2 (2 * s + t) +
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 t -
  qSourceTaylorDerivative 2 s * qSourceTaylorDerivative 1 (2 * s + t) +
  qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (s + t) -
  8 * qSourceTaylorDerivative 1 t * qSourceTaylorDerivative 2 (2 * s + t) +
  8 * qSourceTaylorDerivative 1 (s + t) * qSourceTaylorDerivative 2 (2 * s + t) +
  5 * qSourceTaylorDerivative 2 (s + t) * qSourceTaylorDerivative 1 (2 * s + t)

theorem sourceK_eq_productData (s t : Real) :
    sourceK s t = evalTerms productData s t := by
  unfold sourceK productData
  simp only [evalTerms_append]
  rw [p0_eval, p1_eval, p2_eval, p3_eval, p4_eval, p5_eval,
    p6_eval, p7_eval, p8_eval, p9_eval, p10_eval, p11_eval]
  rw [← q0_1_0_eval, ← q3_2_1_eval, ← q0_0_1_eval,
    ← q3_1_1_eval, ← q0_1_1_eval, ← q0_2_1_eval,
    ← q1_1_0_eval, ← q2_2_1_eval, ← q2_1_0_eval,
    ← q1_0_1_eval, ← q1_2_1_eval, ← q2_1_1_eval,
    ← q1_1_1_eval]
  ring

theorem sourceK_eq_kData (s t : Real) :
    sourceK s t = evalTerms kData s t := by
  rw [sourceK_eq_productData, productData_eval_eq_kData]

end GeneralCK.Certificates.E8OriginSourceKExactAssembly

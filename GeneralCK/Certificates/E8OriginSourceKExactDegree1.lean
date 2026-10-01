import GeneralCK.Certificates.E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_1 : coeffAt productData 0 1 = coeffAt kData 0 1 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData,
    E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data,
    E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data,
    E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data,
    E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data,
    E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data,
    E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_1_0 : coeffAt productData 1 0 = coeffAt kData 1 0 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData,
    E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data,
    E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data,
    E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data,
    E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data,
    E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data,
    E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

end GeneralCK.Certificates.E8OriginSourceKExactReplay

import GeneralCK.Certificates.E8OriginSourceKExactData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 1000000 in
theorem coeff_0_5 : coeffAt productData 0 5 = coeffAt kData 0 5 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_1_4 : coeffAt productData 1 4 = coeffAt kData 1 4 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_2_3 : coeffAt productData 2 3 = coeffAt kData 2 3 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_3_2 : coeffAt productData 3 2 = coeffAt kData 3 2 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_4_1 : coeffAt productData 4 1 = coeffAt kData 4 1 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

set_option maxHeartbeats 1000000 in
theorem coeff_5_0 : coeffAt productData 5 0 = coeffAt kData 5 0 := by
  norm_num (config := { maxSteps := 1000000 }) [coeffAt, productData, E8OriginSourceKProducts.p0Data, E8OriginSourceKProducts.p1Data, E8OriginSourceKProducts.p2Data, E8OriginSourceKProducts.p3Data, E8OriginSourceKProducts.p4Data, E8OriginSourceKProducts.p5Data, E8OriginSourceKProducts.p6Data, E8OriginSourceKProducts.p7Data, E8OriginSourceKProducts.p8Data, E8OriginSourceKProducts.p9Data, E8OriginSourceKProducts.p10Data, E8OriginSourceKProducts.p11Data, kData]

end GeneralCK.Certificates.E8OriginSourceKExactReplay

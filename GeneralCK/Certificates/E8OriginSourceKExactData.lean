import GeneralCK.Certificates.E8OriginSourceKProducts
import GeneralCK.Certificates.E8OriginSourceKCoefficientData

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay
open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay
set_option maxRecDepth 100000

def productData : List Term := p0Data ++ p1Data ++ p2Data ++ p3Data ++ p4Data ++ p5Data ++ p6Data ++ p7Data ++ p8Data ++ p9Data ++ p10Data ++ p11Data

end GeneralCK.Certificates.E8OriginSourceKExactReplay

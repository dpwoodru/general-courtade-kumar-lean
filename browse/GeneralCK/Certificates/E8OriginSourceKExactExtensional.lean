import GeneralCK.Certificates.E8OriginSourceKExactSupport

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

theorem productData_mem_kSupport (r : Term) (hr : r ∈ productData) :
    (r.i, r.j) ∈ kSupport := by
  rw [productData] at hr
  rcases List.mem_append.mp hr with hr | h11
  ·
    rcases List.mem_append.mp hr with hr | h10
    ·
      rcases List.mem_append.mp hr with hr | h9
      ·
        rcases List.mem_append.mp hr with hr | h8
        ·
          rcases List.mem_append.mp hr with hr | h7
          ·
            rcases List.mem_append.mp hr with hr | h6
            ·
              rcases List.mem_append.mp hr with hr | h5
              ·
                rcases List.mem_append.mp hr with hr | h4
                ·
                  rcases List.mem_append.mp hr with hr | h3
                  ·
                    rcases List.mem_append.mp hr with hr | h2
                    ·
                      rcases List.mem_append.mp hr with hr | h1
                      ·
                        exact p0Data_mem_kSupport r hr
                      · exact p1Data_mem_kSupport r h1
                    · exact p2Data_mem_kSupport r h2
                  · exact p3Data_mem_kSupport r h3
                · exact p4Data_mem_kSupport r h4
              · exact p5Data_mem_kSupport r h5
            · exact p6Data_mem_kSupport r h6
          · exact p7Data_mem_kSupport r h7
        · exact p8Data_mem_kSupport r h8
      · exact p9Data_mem_kSupport r h9
    · exact p10Data_mem_kSupport r h10
  · exact p11Data_mem_kSupport r h11

theorem kData_mem_kSupport (r : Term) (hr : r ∈ kData) :
    (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKCoefficientReplay.kData, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem productData_eval_eq_kData (s t : Real) :
    evalTerms productData s t = evalTerms kData s t := by
  exact evalTerms_eq_of_coeffAtOn kSupport productData kData s t
    productData_mem_kSupport kData_mem_kSupport
    coeffAt_productData_eq_kData_on_support

end GeneralCK.Certificates.E8OriginSourceKExactReplay

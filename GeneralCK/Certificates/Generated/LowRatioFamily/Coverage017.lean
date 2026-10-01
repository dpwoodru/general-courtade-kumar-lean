import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0272
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0273
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0274
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0275
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0276
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0277
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0278
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0279
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0280
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0281
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0282
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0283
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0284
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0285
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0286
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0287
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_272_273 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (887 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1773 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_272 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_273 ⟨hr,ha.2⟩ hz
theorem cover_274_275 {a z : ℝ} (ha : a ∈ Set.Icc (887 / 5000) (111 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 400):ℝ) with hl | hr
  · exact curvature_leaf_274 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_275 ⟨hr,ha.2⟩ hz
theorem cover_272_275 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (111 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((887 / 5000):ℝ) with hl | hr
  · exact cover_272_273 ⟨ha.1,hl⟩ hz
  · exact cover_274_275 ⟨hr,ha.2⟩ hz
theorem cover_276_277 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 625) (889 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1777 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_276 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_277 ⟨hr,ha.2⟩ hz
theorem cover_278_279 {a z : ℝ} (ha : a ∈ Set.Icc (889 / 5000) (89 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1779 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_278 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_279 ⟨hr,ha.2⟩ hz
theorem cover_276_279 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 625) (89 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((889 / 5000):ℝ) with hl | hr
  · exact cover_276_277 ⟨ha.1,hl⟩ hz
  · exact cover_278_279 ⟨hr,ha.2⟩ hz
theorem cover_272_279 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (89 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((111 / 625):ℝ) with hl | hr
  · exact cover_272_275 ⟨ha.1,hl⟩ hz
  · exact cover_276_279 ⟨hr,ha.2⟩ hz
theorem cover_280_281 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 500) (891 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1781 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_280 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_281 ⟨hr,ha.2⟩ hz
theorem cover_282_283 {a z : ℝ} (ha : a ∈ Set.Icc (891 / 5000) (223 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1783 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_282 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_283 ⟨hr,ha.2⟩ hz
theorem cover_280_283 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 500) (223 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((891 / 5000):ℝ) with hl | hr
  · exact cover_280_281 ⟨ha.1,hl⟩ hz
  · exact cover_282_283 ⟨hr,ha.2⟩ hz
theorem cover_284_285 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 1250) (893 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((357 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_284 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_285 ⟨hr,ha.2⟩ hz
theorem cover_286_287 {a z : ℝ} (ha : a ∈ Set.Icc (893 / 5000) (447 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1787 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_286 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_287 ⟨hr,ha.2⟩ hz
theorem cover_284_287 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 1250) (447 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((893 / 5000):ℝ) with hl | hr
  · exact cover_284_285 ⟨ha.1,hl⟩ hz
  · exact cover_286_287 ⟨hr,ha.2⟩ hz
theorem cover_280_287 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 500) (447 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((223 / 1250):ℝ) with hl | hr
  · exact cover_280_283 ⟨ha.1,hl⟩ hz
  · exact cover_284_287 ⟨hr,ha.2⟩ hz
theorem cover_272_287 {a z : ℝ} (ha : a ∈ Set.Icc (443 / 2500) (447 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 500):ℝ) with hl | hr
  · exact cover_272_279 ⟨ha.1,hl⟩ hz
  · exact cover_280_287 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

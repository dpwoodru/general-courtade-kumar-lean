import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0240
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0241
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0242
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0243
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0244
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0245
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0246
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0247
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0248
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0249
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0250
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0251
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0252
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0253
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0254
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0255
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_240_241 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 500) (871 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1741 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_240 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_241 ⟨hr,ha.2⟩ hz
theorem cover_242_243 {a z : ℝ} (ha : a ∈ Set.Icc (871 / 5000) (109 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1743 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_242 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_243 ⟨hr,ha.2⟩ hz
theorem cover_240_243 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 500) (109 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((871 / 5000):ℝ) with hl | hr
  · exact cover_240_241 ⟨ha.1,hl⟩ hz
  · exact cover_242_243 ⟨hr,ha.2⟩ hz
theorem cover_244_245 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 625) (873 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((349 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_244 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_245 ⟨hr,ha.2⟩ hz
theorem cover_246_247 {a z : ℝ} (ha : a ∈ Set.Icc (873 / 5000) (437 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1747 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_246 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_247 ⟨hr,ha.2⟩ hz
theorem cover_244_247 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 625) (437 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((873 / 5000):ℝ) with hl | hr
  · exact cover_244_245 ⟨ha.1,hl⟩ hz
  · exact cover_246_247 ⟨hr,ha.2⟩ hz
theorem cover_240_247 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 500) (437 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 625):ℝ) with hl | hr
  · exact cover_240_243 ⟨ha.1,hl⟩ hz
  · exact cover_244_247 ⟨hr,ha.2⟩ hz
theorem cover_248_249 {a z : ℝ} (ha : a ∈ Set.Icc (437 / 2500) (7 / 40))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1749 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_248 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_249 ⟨hr,ha.2⟩ hz
theorem cover_250_251 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 40) (219 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1751 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_250 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_251 ⟨hr,ha.2⟩ hz
theorem cover_248_251 {a z : ℝ} (ha : a ∈ Set.Icc (437 / 2500) (219 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 40):ℝ) with hl | hr
  · exact cover_248_249 ⟨ha.1,hl⟩ hz
  · exact cover_250_251 ⟨hr,ha.2⟩ hz
theorem cover_252_253 {a z : ℝ} (ha : a ∈ Set.Icc (219 / 1250) (877 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1753 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_252 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_253 ⟨hr,ha.2⟩ hz
theorem cover_254_255 {a z : ℝ} (ha : a ∈ Set.Icc (877 / 5000) (439 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((351 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_254 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_255 ⟨hr,ha.2⟩ hz
theorem cover_252_255 {a z : ℝ} (ha : a ∈ Set.Icc (219 / 1250) (439 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((877 / 5000):ℝ) with hl | hr
  · exact cover_252_253 ⟨ha.1,hl⟩ hz
  · exact cover_254_255 ⟨hr,ha.2⟩ hz
theorem cover_248_255 {a z : ℝ} (ha : a ∈ Set.Icc (437 / 2500) (439 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((219 / 1250):ℝ) with hl | hr
  · exact cover_248_251 ⟨ha.1,hl⟩ hz
  · exact cover_252_255 ⟨hr,ha.2⟩ hz
theorem cover_240_255 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 500) (439 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((437 / 2500):ℝ) with hl | hr
  · exact cover_240_247 ⟨ha.1,hl⟩ hz
  · exact cover_248_255 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

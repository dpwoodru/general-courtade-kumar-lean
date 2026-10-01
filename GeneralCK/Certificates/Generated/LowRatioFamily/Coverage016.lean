import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0256
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0257
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0258
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0259
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0260
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0261
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0262
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0263
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0264
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0265
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0266
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0267
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0268
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0269
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0270
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0271
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_256_257 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 2500) (879 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1757 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_256 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_257 ⟨hr,ha.2⟩ hz
theorem cover_258_259 {a z : ℝ} (ha : a ∈ Set.Icc (879 / 5000) (22 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1759 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_258 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_259 ⟨hr,ha.2⟩ hz
theorem cover_256_259 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 2500) (22 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((879 / 5000):ℝ) with hl | hr
  · exact cover_256_257 ⟨ha.1,hl⟩ hz
  · exact cover_258_259 ⟨hr,ha.2⟩ hz
theorem cover_260_261 {a z : ℝ} (ha : a ∈ Set.Icc (22 / 125) (881 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1761 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_260 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_261 ⟨hr,ha.2⟩ hz
theorem cover_262_263 {a z : ℝ} (ha : a ∈ Set.Icc (881 / 5000) (441 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1763 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_262 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_263 ⟨hr,ha.2⟩ hz
theorem cover_260_263 {a z : ℝ} (ha : a ∈ Set.Icc (22 / 125) (441 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((881 / 5000):ℝ) with hl | hr
  · exact cover_260_261 ⟨ha.1,hl⟩ hz
  · exact cover_262_263 ⟨hr,ha.2⟩ hz
theorem cover_256_263 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 2500) (441 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((22 / 125):ℝ) with hl | hr
  · exact cover_256_259 ⟨ha.1,hl⟩ hz
  · exact cover_260_263 ⟨hr,ha.2⟩ hz
theorem cover_264_265 {a z : ℝ} (ha : a ∈ Set.Icc (441 / 2500) (883 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((353 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_264 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_265 ⟨hr,ha.2⟩ hz
theorem cover_266_267 {a z : ℝ} (ha : a ∈ Set.Icc (883 / 5000) (221 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1767 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_266 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_267 ⟨hr,ha.2⟩ hz
theorem cover_264_267 {a z : ℝ} (ha : a ∈ Set.Icc (441 / 2500) (221 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((883 / 5000):ℝ) with hl | hr
  · exact cover_264_265 ⟨ha.1,hl⟩ hz
  · exact cover_266_267 ⟨hr,ha.2⟩ hz
theorem cover_268_269 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 1250) (177 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1769 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_268 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_269 ⟨hr,ha.2⟩ hz
theorem cover_270_271 {a z : ℝ} (ha : a ∈ Set.Icc (177 / 1000) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1771 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_270 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_271 ⟨hr,ha.2⟩ hz
theorem cover_268_271 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 1250) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((177 / 1000):ℝ) with hl | hr
  · exact cover_268_269 ⟨ha.1,hl⟩ hz
  · exact cover_270_271 ⟨hr,ha.2⟩ hz
theorem cover_264_271 {a z : ℝ} (ha : a ∈ Set.Icc (441 / 2500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 1250):ℝ) with hl | hr
  · exact cover_264_267 ⟨ha.1,hl⟩ hz
  · exact cover_268_271 ⟨hr,ha.2⟩ hz
theorem cover_256_271 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 2500) (443 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((441 / 2500):ℝ) with hl | hr
  · exact cover_256_263 ⟨ha.1,hl⟩ hz
  · exact cover_264_271 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

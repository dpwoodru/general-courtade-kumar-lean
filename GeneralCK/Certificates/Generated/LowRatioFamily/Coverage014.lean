import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0224
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0225
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0226
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0227
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0228
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0229
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0230
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0231
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0232
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0233
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0234
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0235
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0236
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0237
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0238
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0239
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_224_225 {a z : ℝ} (ha : a ∈ Set.Icc (431 / 2500) (863 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((69 / 400):ℝ) with hl | hr
  · exact curvature_leaf_224 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_225 ⟨hr,ha.2⟩ hz
theorem cover_226_227 {a z : ℝ} (ha : a ∈ Set.Icc (863 / 5000) (108 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1727 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_226 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_227 ⟨hr,ha.2⟩ hz
theorem cover_224_227 {a z : ℝ} (ha : a ∈ Set.Icc (431 / 2500) (108 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((863 / 5000):ℝ) with hl | hr
  · exact cover_224_225 ⟨ha.1,hl⟩ hz
  · exact cover_226_227 ⟨hr,ha.2⟩ hz
theorem cover_228_229 {a z : ℝ} (ha : a ∈ Set.Icc (108 / 625) (173 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1729 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_228 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_229 ⟨hr,ha.2⟩ hz
theorem cover_230_231 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 1000) (433 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1731 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_230 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_231 ⟨hr,ha.2⟩ hz
theorem cover_228_231 {a z : ℝ} (ha : a ∈ Set.Icc (108 / 625) (433 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((173 / 1000):ℝ) with hl | hr
  · exact cover_228_229 ⟨ha.1,hl⟩ hz
  · exact cover_230_231 ⟨hr,ha.2⟩ hz
theorem cover_224_231 {a z : ℝ} (ha : a ∈ Set.Icc (431 / 2500) (433 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((108 / 625):ℝ) with hl | hr
  · exact cover_224_227 ⟨ha.1,hl⟩ hz
  · exact cover_228_231 ⟨hr,ha.2⟩ hz
theorem cover_232_233 {a z : ℝ} (ha : a ∈ Set.Icc (433 / 2500) (867 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1733 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_232 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_233 ⟨hr,ha.2⟩ hz
theorem cover_234_235 {a z : ℝ} (ha : a ∈ Set.Icc (867 / 5000) (217 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((347 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_234 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_235 ⟨hr,ha.2⟩ hz
theorem cover_232_235 {a z : ℝ} (ha : a ∈ Set.Icc (433 / 2500) (217 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((867 / 5000):ℝ) with hl | hr
  · exact cover_232_233 ⟨ha.1,hl⟩ hz
  · exact cover_234_235 ⟨hr,ha.2⟩ hz
theorem cover_236_237 {a z : ℝ} (ha : a ∈ Set.Icc (217 / 1250) (869 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1737 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_236 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_237 ⟨hr,ha.2⟩ hz
theorem cover_238_239 {a z : ℝ} (ha : a ∈ Set.Icc (869 / 5000) (87 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1739 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_238 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_239 ⟨hr,ha.2⟩ hz
theorem cover_236_239 {a z : ℝ} (ha : a ∈ Set.Icc (217 / 1250) (87 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((869 / 5000):ℝ) with hl | hr
  · exact cover_236_237 ⟨ha.1,hl⟩ hz
  · exact cover_238_239 ⟨hr,ha.2⟩ hz
theorem cover_232_239 {a z : ℝ} (ha : a ∈ Set.Icc (433 / 2500) (87 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((217 / 1250):ℝ) with hl | hr
  · exact cover_232_235 ⟨ha.1,hl⟩ hz
  · exact cover_236_239 ⟨hr,ha.2⟩ hz
theorem cover_224_239 {a z : ℝ} (ha : a ∈ Set.Icc (431 / 2500) (87 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 2500):ℝ) with hl | hr
  · exact cover_224_231 ⟨ha.1,hl⟩ hz
  · exact cover_232_239 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0208
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0209
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0210
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0211
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0212
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0213
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0214
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0215
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0216
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0217
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0218
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0219
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0220
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0221
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0222
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0223
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_208_209 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 2500) (171 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1709 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_208 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_209 ⟨hr,ha.2⟩ hz
theorem cover_210_211 {a z : ℝ} (ha : a ∈ Set.Icc (171 / 1000) (107 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1711 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_210 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_211 ⟨hr,ha.2⟩ hz
theorem cover_208_211 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 2500) (107 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((171 / 1000):ℝ) with hl | hr
  · exact cover_208_209 ⟨ha.1,hl⟩ hz
  · exact cover_210_211 ⟨hr,ha.2⟩ hz
theorem cover_212_213 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 625) (857 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1713 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_212 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_213 ⟨hr,ha.2⟩ hz
theorem cover_214_215 {a z : ℝ} (ha : a ∈ Set.Icc (857 / 5000) (429 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((343 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_214 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_215 ⟨hr,ha.2⟩ hz
theorem cover_212_215 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 625) (429 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((857 / 5000):ℝ) with hl | hr
  · exact cover_212_213 ⟨ha.1,hl⟩ hz
  · exact cover_214_215 ⟨hr,ha.2⟩ hz
theorem cover_208_215 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 2500) (429 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((107 / 625):ℝ) with hl | hr
  · exact cover_208_211 ⟨ha.1,hl⟩ hz
  · exact cover_212_215 ⟨hr,ha.2⟩ hz
theorem cover_216_217 {a z : ℝ} (ha : a ∈ Set.Icc (429 / 2500) (859 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1717 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_216 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_217 ⟨hr,ha.2⟩ hz
theorem cover_218_219 {a z : ℝ} (ha : a ∈ Set.Icc (859 / 5000) (43 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1719 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_218 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_219 ⟨hr,ha.2⟩ hz
theorem cover_216_219 {a z : ℝ} (ha : a ∈ Set.Icc (429 / 2500) (43 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((859 / 5000):ℝ) with hl | hr
  · exact cover_216_217 ⟨ha.1,hl⟩ hz
  · exact cover_218_219 ⟨hr,ha.2⟩ hz
theorem cover_220_221 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 250) (861 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1721 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_220 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_221 ⟨hr,ha.2⟩ hz
theorem cover_222_223 {a z : ℝ} (ha : a ∈ Set.Icc (861 / 5000) (431 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1723 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_222 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_223 ⟨hr,ha.2⟩ hz
theorem cover_220_223 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 250) (431 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((861 / 5000):ℝ) with hl | hr
  · exact cover_220_221 ⟨ha.1,hl⟩ hz
  · exact cover_222_223 ⟨hr,ha.2⟩ hz
theorem cover_216_223 {a z : ℝ} (ha : a ∈ Set.Icc (429 / 2500) (431 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 250):ℝ) with hl | hr
  · exact cover_216_219 ⟨ha.1,hl⟩ hz
  · exact cover_220_223 ⟨hr,ha.2⟩ hz
theorem cover_208_223 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 2500) (431 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((429 / 2500):ℝ) with hl | hr
  · exact cover_208_215 ⟨ha.1,hl⟩ hz
  · exact cover_216_223 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

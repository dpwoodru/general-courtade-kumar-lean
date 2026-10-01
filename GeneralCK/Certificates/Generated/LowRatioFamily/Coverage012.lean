import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0192
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0193
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0194
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0195
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0196
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0197
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0198
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0199
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0200
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0201
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0202
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0203
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0204
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0205
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0206
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0207
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_192_193 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (847 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1693 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_192 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_193 ⟨hr,ha.2⟩ hz
theorem cover_194_195 {a z : ℝ} (ha : a ∈ Set.Icc (847 / 5000) (106 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((339 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_194 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_195 ⟨hr,ha.2⟩ hz
theorem cover_192_195 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (106 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((847 / 5000):ℝ) with hl | hr
  · exact cover_192_193 ⟨ha.1,hl⟩ hz
  · exact cover_194_195 ⟨hr,ha.2⟩ hz
theorem cover_196_197 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 625) (849 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1697 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_196 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_197 ⟨hr,ha.2⟩ hz
theorem cover_198_199 {a z : ℝ} (ha : a ∈ Set.Icc (849 / 5000) (17 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1699 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_198 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_199 ⟨hr,ha.2⟩ hz
theorem cover_196_199 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 625) (17 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((849 / 5000):ℝ) with hl | hr
  · exact cover_196_197 ⟨ha.1,hl⟩ hz
  · exact cover_198_199 ⟨hr,ha.2⟩ hz
theorem cover_192_199 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (17 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((106 / 625):ℝ) with hl | hr
  · exact cover_192_195 ⟨ha.1,hl⟩ hz
  · exact cover_196_199 ⟨hr,ha.2⟩ hz
theorem cover_200_201 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 100) (851 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1701 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_200 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_201 ⟨hr,ha.2⟩ hz
theorem cover_202_203 {a z : ℝ} (ha : a ∈ Set.Icc (851 / 5000) (213 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1703 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_202 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_203 ⟨hr,ha.2⟩ hz
theorem cover_200_203 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 100) (213 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((851 / 5000):ℝ) with hl | hr
  · exact cover_200_201 ⟨ha.1,hl⟩ hz
  · exact cover_202_203 ⟨hr,ha.2⟩ hz
theorem cover_204_205 {a z : ℝ} (ha : a ∈ Set.Icc (213 / 1250) (853 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((341 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_204 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_205 ⟨hr,ha.2⟩ hz
theorem cover_206_207 {a z : ℝ} (ha : a ∈ Set.Icc (853 / 5000) (427 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1707 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_206 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_207 ⟨hr,ha.2⟩ hz
theorem cover_204_207 {a z : ℝ} (ha : a ∈ Set.Icc (213 / 1250) (427 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((853 / 5000):ℝ) with hl | hr
  · exact cover_204_205 ⟨ha.1,hl⟩ hz
  · exact cover_206_207 ⟨hr,ha.2⟩ hz
theorem cover_200_207 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 100) (427 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((213 / 1250):ℝ) with hl | hr
  · exact cover_200_203 ⟨ha.1,hl⟩ hz
  · exact cover_204_207 ⟨hr,ha.2⟩ hz
theorem cover_192_207 {a z : ℝ} (ha : a ∈ Set.Icc (423 / 2500) (427 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 100):ℝ) with hl | hr
  · exact cover_192_199 ⟨ha.1,hl⟩ hz
  · exact cover_200_207 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

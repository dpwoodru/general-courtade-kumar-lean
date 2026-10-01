import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0304
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0305
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0306
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0307
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0308
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0309
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0310
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0311
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0312
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0313
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0314
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0315
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0316
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0317
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0318
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0319
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_304_305 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 2500) (903 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((361 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_304 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_305 ⟨hr,ha.2⟩ hz
theorem cover_306_307 {a z : ℝ} (ha : a ∈ Set.Icc (903 / 5000) (113 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1807 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_306 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_307 ⟨hr,ha.2⟩ hz
theorem cover_304_307 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 2500) (113 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((903 / 5000):ℝ) with hl | hr
  · exact cover_304_305 ⟨ha.1,hl⟩ hz
  · exact cover_306_307 ⟨hr,ha.2⟩ hz
theorem cover_308_309 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 625) (181 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1809 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_308 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_309 ⟨hr,ha.2⟩ hz
theorem cover_310_311 {a z : ℝ} (ha : a ∈ Set.Icc (181 / 1000) (453 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1811 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_310 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_311 ⟨hr,ha.2⟩ hz
theorem cover_308_311 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 625) (453 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((181 / 1000):ℝ) with hl | hr
  · exact cover_308_309 ⟨ha.1,hl⟩ hz
  · exact cover_310_311 ⟨hr,ha.2⟩ hz
theorem cover_304_311 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 2500) (453 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 625):ℝ) with hl | hr
  · exact cover_304_307 ⟨ha.1,hl⟩ hz
  · exact cover_308_311 ⟨hr,ha.2⟩ hz
theorem cover_312_313 {a z : ℝ} (ha : a ∈ Set.Icc (453 / 2500) (907 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1813 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_312 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_313 ⟨hr,ha.2⟩ hz
theorem cover_314_315 {a z : ℝ} (ha : a ∈ Set.Icc (907 / 5000) (227 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((363 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_314 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_315 ⟨hr,ha.2⟩ hz
theorem cover_312_315 {a z : ℝ} (ha : a ∈ Set.Icc (453 / 2500) (227 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((907 / 5000):ℝ) with hl | hr
  · exact cover_312_313 ⟨ha.1,hl⟩ hz
  · exact cover_314_315 ⟨hr,ha.2⟩ hz
theorem cover_316_317 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 1250) (909 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1817 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_316 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_317 ⟨hr,ha.2⟩ hz
theorem cover_318_319 {a z : ℝ} (ha : a ∈ Set.Icc (909 / 5000) (91 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1819 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_318 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_319 ⟨hr,ha.2⟩ hz
theorem cover_316_319 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 1250) (91 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((909 / 5000):ℝ) with hl | hr
  · exact cover_316_317 ⟨ha.1,hl⟩ hz
  · exact cover_318_319 ⟨hr,ha.2⟩ hz
theorem cover_312_319 {a z : ℝ} (ha : a ∈ Set.Icc (453 / 2500) (91 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 1250):ℝ) with hl | hr
  · exact cover_312_315 ⟨ha.1,hl⟩ hz
  · exact cover_316_319 ⟨hr,ha.2⟩ hz
theorem cover_304_319 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 2500) (91 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((453 / 2500):ℝ) with hl | hr
  · exact cover_304_311 ⟨ha.1,hl⟩ hz
  · exact cover_312_319 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

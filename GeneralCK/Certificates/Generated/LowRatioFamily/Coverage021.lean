import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0336
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0337
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0338
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0339
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0340
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0341
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0342
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0343
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0344
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0345
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0346
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0347
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0348
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0349
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0350
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0351
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_336_337 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (919 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1837 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_336 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_337 ⟨hr,ha.2⟩ hz
theorem cover_338_339 {a z : ℝ} (ha : a ∈ Set.Icc (919 / 5000) (23 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1839 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_338 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_339 ⟨hr,ha.2⟩ hz
theorem cover_336_339 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (23 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((919 / 5000):ℝ) with hl | hr
  · exact cover_336_337 ⟨ha.1,hl⟩ hz
  · exact cover_338_339 ⟨hr,ha.2⟩ hz
theorem cover_340_341 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 125) (921 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1841 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_340 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_341 ⟨hr,ha.2⟩ hz
theorem cover_342_343 {a z : ℝ} (ha : a ∈ Set.Icc (921 / 5000) (461 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1843 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_342 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_343 ⟨hr,ha.2⟩ hz
theorem cover_340_343 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 125) (461 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((921 / 5000):ℝ) with hl | hr
  · exact cover_340_341 ⟨ha.1,hl⟩ hz
  · exact cover_342_343 ⟨hr,ha.2⟩ hz
theorem cover_336_343 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (461 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 125):ℝ) with hl | hr
  · exact cover_336_339 ⟨ha.1,hl⟩ hz
  · exact cover_340_343 ⟨hr,ha.2⟩ hz
theorem cover_344_345 {a z : ℝ} (ha : a ∈ Set.Icc (461 / 2500) (923 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((369 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_344 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_345 ⟨hr,ha.2⟩ hz
theorem cover_346_347 {a z : ℝ} (ha : a ∈ Set.Icc (923 / 5000) (231 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1847 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_346 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_347 ⟨hr,ha.2⟩ hz
theorem cover_344_347 {a z : ℝ} (ha : a ∈ Set.Icc (461 / 2500) (231 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((923 / 5000):ℝ) with hl | hr
  · exact cover_344_345 ⟨ha.1,hl⟩ hz
  · exact cover_346_347 ⟨hr,ha.2⟩ hz
theorem cover_348_349 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 1250) (37 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1849 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_348 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_349 ⟨hr,ha.2⟩ hz
theorem cover_350_351 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 200) (463 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1851 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_350 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_351 ⟨hr,ha.2⟩ hz
theorem cover_348_351 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 1250) (463 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 200):ℝ) with hl | hr
  · exact cover_348_349 ⟨ha.1,hl⟩ hz
  · exact cover_350_351 ⟨hr,ha.2⟩ hz
theorem cover_344_351 {a z : ℝ} (ha : a ∈ Set.Icc (461 / 2500) (463 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((231 / 1250):ℝ) with hl | hr
  · exact cover_344_347 ⟨ha.1,hl⟩ hz
  · exact cover_348_351 ⟨hr,ha.2⟩ hz
theorem cover_336_351 {a z : ℝ} (ha : a ∈ Set.Icc (459 / 2500) (463 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((461 / 2500):ℝ) with hl | hr
  · exact cover_336_343 ⟨ha.1,hl⟩ hz
  · exact cover_344_351 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

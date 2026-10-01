import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0320
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0321
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0322
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0323
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0324
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0325
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0326
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0327
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0328
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0329
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0330
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0331
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0332
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0333
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0334
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0335
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_320_321 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 500) (911 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1821 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_320 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_321 ⟨hr,ha.2⟩ hz
theorem cover_322_323 {a z : ℝ} (ha : a ∈ Set.Icc (911 / 5000) (114 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1823 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_322 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_323 ⟨hr,ha.2⟩ hz
theorem cover_320_323 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 500) (114 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((911 / 5000):ℝ) with hl | hr
  · exact cover_320_321 ⟨ha.1,hl⟩ hz
  · exact cover_322_323 ⟨hr,ha.2⟩ hz
theorem cover_324_325 {a z : ℝ} (ha : a ∈ Set.Icc (114 / 625) (913 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 400):ℝ) with hl | hr
  · exact curvature_leaf_324 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_325 ⟨hr,ha.2⟩ hz
theorem cover_326_327 {a z : ℝ} (ha : a ∈ Set.Icc (913 / 5000) (457 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1827 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_326 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_327 ⟨hr,ha.2⟩ hz
theorem cover_324_327 {a z : ℝ} (ha : a ∈ Set.Icc (114 / 625) (457 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((913 / 5000):ℝ) with hl | hr
  · exact cover_324_325 ⟨ha.1,hl⟩ hz
  · exact cover_326_327 ⟨hr,ha.2⟩ hz
theorem cover_320_327 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 500) (457 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((114 / 625):ℝ) with hl | hr
  · exact cover_320_323 ⟨ha.1,hl⟩ hz
  · exact cover_324_327 ⟨hr,ha.2⟩ hz
theorem cover_328_329 {a z : ℝ} (ha : a ∈ Set.Icc (457 / 2500) (183 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1829 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_328 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_329 ⟨hr,ha.2⟩ hz
theorem cover_330_331 {a z : ℝ} (ha : a ∈ Set.Icc (183 / 1000) (229 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1831 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_330 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_331 ⟨hr,ha.2⟩ hz
theorem cover_328_331 {a z : ℝ} (ha : a ∈ Set.Icc (457 / 2500) (229 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((183 / 1000):ℝ) with hl | hr
  · exact cover_328_329 ⟨ha.1,hl⟩ hz
  · exact cover_330_331 ⟨hr,ha.2⟩ hz
theorem cover_332_333 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 1250) (917 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1833 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_332 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_333 ⟨hr,ha.2⟩ hz
theorem cover_334_335 {a z : ℝ} (ha : a ∈ Set.Icc (917 / 5000) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((367 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_334 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_335 ⟨hr,ha.2⟩ hz
theorem cover_332_335 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 1250) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((917 / 5000):ℝ) with hl | hr
  · exact cover_332_333 ⟨ha.1,hl⟩ hz
  · exact cover_334_335 ⟨hr,ha.2⟩ hz
theorem cover_328_335 {a z : ℝ} (ha : a ∈ Set.Icc (457 / 2500) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((229 / 1250):ℝ) with hl | hr
  · exact cover_328_331 ⟨ha.1,hl⟩ hz
  · exact cover_332_335 ⟨hr,ha.2⟩ hz
theorem cover_320_335 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 500) (459 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 2500):ℝ) with hl | hr
  · exact cover_320_327 ⟨ha.1,hl⟩ hz
  · exact cover_328_335 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0368
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0369
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0370
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0371
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0372
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0373
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0374
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0375
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0376
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0377
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0378
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0379
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0380
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0381
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0382
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0383
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_368_369 {a z : ℝ} (ha : a ∈ Set.Icc (467 / 2500) (187 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1869 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_368 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_369 ⟨hr,ha.2⟩ hz
theorem cover_370_371 {a z : ℝ} (ha : a ∈ Set.Icc (187 / 1000) (117 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1871 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_370 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_371 ⟨hr,ha.2⟩ hz
theorem cover_368_371 {a z : ℝ} (ha : a ∈ Set.Icc (467 / 2500) (117 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((187 / 1000):ℝ) with hl | hr
  · exact cover_368_369 ⟨ha.1,hl⟩ hz
  · exact cover_370_371 ⟨hr,ha.2⟩ hz
theorem cover_372_373 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 625) (937 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1873 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_372 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_373 ⟨hr,ha.2⟩ hz
theorem cover_374_375 {a z : ℝ} (ha : a ∈ Set.Icc (937 / 5000) (469 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((3 / 16):ℝ) with hl | hr
  · exact curvature_leaf_374 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_375 ⟨hr,ha.2⟩ hz
theorem cover_372_375 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 625) (469 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((937 / 5000):ℝ) with hl | hr
  · exact cover_372_373 ⟨ha.1,hl⟩ hz
  · exact cover_374_375 ⟨hr,ha.2⟩ hz
theorem cover_368_375 {a z : ℝ} (ha : a ∈ Set.Icc (467 / 2500) (469 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 625):ℝ) with hl | hr
  · exact cover_368_371 ⟨ha.1,hl⟩ hz
  · exact cover_372_375 ⟨hr,ha.2⟩ hz
theorem cover_376_377 {a z : ℝ} (ha : a ∈ Set.Icc (469 / 2500) (939 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1877 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_376 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_377 ⟨hr,ha.2⟩ hz
theorem cover_378_379 {a z : ℝ} (ha : a ∈ Set.Icc (939 / 5000) (47 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1879 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_378 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_379 ⟨hr,ha.2⟩ hz
theorem cover_376_379 {a z : ℝ} (ha : a ∈ Set.Icc (469 / 2500) (47 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((939 / 5000):ℝ) with hl | hr
  · exact cover_376_377 ⟨ha.1,hl⟩ hz
  · exact cover_378_379 ⟨hr,ha.2⟩ hz
theorem cover_380_381 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 250) (941 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1881 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_380 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_381 ⟨hr,ha.2⟩ hz
theorem cover_382_383 {a z : ℝ} (ha : a ∈ Set.Icc (941 / 5000) (471 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1883 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_382 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_383 ⟨hr,ha.2⟩ hz
theorem cover_380_383 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 250) (471 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((941 / 5000):ℝ) with hl | hr
  · exact cover_380_381 ⟨ha.1,hl⟩ hz
  · exact cover_382_383 ⟨hr,ha.2⟩ hz
theorem cover_376_383 {a z : ℝ} (ha : a ∈ Set.Icc (469 / 2500) (471 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 250):ℝ) with hl | hr
  · exact cover_376_379 ⟨ha.1,hl⟩ hz
  · exact cover_380_383 ⟨hr,ha.2⟩ hz
theorem cover_368_383 {a z : ℝ} (ha : a ∈ Set.Icc (467 / 2500) (471 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 2500):ℝ) with hl | hr
  · exact cover_368_375 ⟨ha.1,hl⟩ hz
  · exact cover_376_383 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

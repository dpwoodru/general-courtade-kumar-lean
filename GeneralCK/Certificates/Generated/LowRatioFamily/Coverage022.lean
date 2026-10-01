import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0352
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0353
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0354
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0355
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0356
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0357
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0358
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0359
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0360
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0361
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0362
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0363
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0364
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0365
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0366
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0367
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_352_353 {a z : ℝ} (ha : a ∈ Set.Icc (463 / 2500) (927 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1853 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_352 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_353 ⟨hr,ha.2⟩ hz
theorem cover_354_355 {a z : ℝ} (ha : a ∈ Set.Icc (927 / 5000) (116 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((371 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_354 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_355 ⟨hr,ha.2⟩ hz
theorem cover_352_355 {a z : ℝ} (ha : a ∈ Set.Icc (463 / 2500) (116 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((927 / 5000):ℝ) with hl | hr
  · exact cover_352_353 ⟨ha.1,hl⟩ hz
  · exact cover_354_355 ⟨hr,ha.2⟩ hz
theorem cover_356_357 {a z : ℝ} (ha : a ∈ Set.Icc (116 / 625) (929 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1857 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_356 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_357 ⟨hr,ha.2⟩ hz
theorem cover_358_359 {a z : ℝ} (ha : a ∈ Set.Icc (929 / 5000) (93 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1859 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_358 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_359 ⟨hr,ha.2⟩ hz
theorem cover_356_359 {a z : ℝ} (ha : a ∈ Set.Icc (116 / 625) (93 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((929 / 5000):ℝ) with hl | hr
  · exact cover_356_357 ⟨ha.1,hl⟩ hz
  · exact cover_358_359 ⟨hr,ha.2⟩ hz
theorem cover_352_359 {a z : ℝ} (ha : a ∈ Set.Icc (463 / 2500) (93 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((116 / 625):ℝ) with hl | hr
  · exact cover_352_355 ⟨ha.1,hl⟩ hz
  · exact cover_356_359 ⟨hr,ha.2⟩ hz
theorem cover_360_361 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 500) (931 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1861 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_360 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_361 ⟨hr,ha.2⟩ hz
theorem cover_362_363 {a z : ℝ} (ha : a ∈ Set.Icc (931 / 5000) (233 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1863 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_362 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_363 ⟨hr,ha.2⟩ hz
theorem cover_360_363 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 500) (233 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((931 / 5000):ℝ) with hl | hr
  · exact cover_360_361 ⟨ha.1,hl⟩ hz
  · exact cover_362_363 ⟨hr,ha.2⟩ hz
theorem cover_364_365 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 1250) (933 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((373 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_364 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_365 ⟨hr,ha.2⟩ hz
theorem cover_366_367 {a z : ℝ} (ha : a ∈ Set.Icc (933 / 5000) (467 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1867 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_366 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_367 ⟨hr,ha.2⟩ hz
theorem cover_364_367 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 1250) (467 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((933 / 5000):ℝ) with hl | hr
  · exact cover_364_365 ⟨ha.1,hl⟩ hz
  · exact cover_366_367 ⟨hr,ha.2⟩ hz
theorem cover_360_367 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 500) (467 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 1250):ℝ) with hl | hr
  · exact cover_360_363 ⟨ha.1,hl⟩ hz
  · exact cover_364_367 ⟨hr,ha.2⟩ hz
theorem cover_352_367 {a z : ℝ} (ha : a ∈ Set.Icc (463 / 2500) (467 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 500):ℝ) with hl | hr
  · exact cover_352_359 ⟨ha.1,hl⟩ hz
  · exact cover_360_367 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

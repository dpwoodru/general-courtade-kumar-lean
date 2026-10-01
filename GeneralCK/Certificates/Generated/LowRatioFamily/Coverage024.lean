import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0384
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0385
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0386
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0387
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0388
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0389
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0390
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0391
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0392
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0393
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0394
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0395
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0396
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0397
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0398
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0399
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_384_385 {a z : ℝ} (ha : a ∈ Set.Icc (471 / 2500) (943 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((377 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_384 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_385 ⟨hr,ha.2⟩ hz
theorem cover_386_387 {a z : ℝ} (ha : a ∈ Set.Icc (943 / 5000) (118 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1887 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_386 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_387 ⟨hr,ha.2⟩ hz
theorem cover_384_387 {a z : ℝ} (ha : a ∈ Set.Icc (471 / 2500) (118 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((943 / 5000):ℝ) with hl | hr
  · exact cover_384_385 ⟨ha.1,hl⟩ hz
  · exact cover_386_387 ⟨hr,ha.2⟩ hz
theorem cover_388_389 {a z : ℝ} (ha : a ∈ Set.Icc (118 / 625) (189 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1889 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_388 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_389 ⟨hr,ha.2⟩ hz
theorem cover_390_391 {a z : ℝ} (ha : a ∈ Set.Icc (189 / 1000) (473 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1891 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_390 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_391 ⟨hr,ha.2⟩ hz
theorem cover_388_391 {a z : ℝ} (ha : a ∈ Set.Icc (118 / 625) (473 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((189 / 1000):ℝ) with hl | hr
  · exact cover_388_389 ⟨ha.1,hl⟩ hz
  · exact cover_390_391 ⟨hr,ha.2⟩ hz
theorem cover_384_391 {a z : ℝ} (ha : a ∈ Set.Icc (471 / 2500) (473 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((118 / 625):ℝ) with hl | hr
  · exact cover_384_387 ⟨ha.1,hl⟩ hz
  · exact cover_388_391 ⟨hr,ha.2⟩ hz
theorem cover_392_393 {a z : ℝ} (ha : a ∈ Set.Icc (473 / 2500) (947 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1893 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_392 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_393 ⟨hr,ha.2⟩ hz
theorem cover_394_395 {a z : ℝ} (ha : a ∈ Set.Icc (947 / 5000) (237 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_394 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_395 ⟨hr,ha.2⟩ hz
theorem cover_392_395 {a z : ℝ} (ha : a ∈ Set.Icc (473 / 2500) (237 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((947 / 5000):ℝ) with hl | hr
  · exact cover_392_393 ⟨ha.1,hl⟩ hz
  · exact cover_394_395 ⟨hr,ha.2⟩ hz
theorem cover_396_397 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 1250) (949 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1897 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_396 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_397 ⟨hr,ha.2⟩ hz
theorem cover_398_399 {a z : ℝ} (ha : a ∈ Set.Icc (949 / 5000) (19 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1899 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_398 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_399 ⟨hr,ha.2⟩ hz
theorem cover_396_399 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 1250) (19 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((949 / 5000):ℝ) with hl | hr
  · exact cover_396_397 ⟨ha.1,hl⟩ hz
  · exact cover_398_399 ⟨hr,ha.2⟩ hz
theorem cover_392_399 {a z : ℝ} (ha : a ∈ Set.Icc (473 / 2500) (19 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((237 / 1250):ℝ) with hl | hr
  · exact cover_392_395 ⟨ha.1,hl⟩ hz
  · exact cover_396_399 ⟨hr,ha.2⟩ hz
theorem cover_384_399 {a z : ℝ} (ha : a ∈ Set.Icc (471 / 2500) (19 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((473 / 2500):ℝ) with hl | hr
  · exact cover_384_391 ⟨ha.1,hl⟩ hz
  · exact cover_392_399 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

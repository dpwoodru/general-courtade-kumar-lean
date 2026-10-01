import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0432
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0433
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0434
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0435
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0436
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0437
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0438
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0439
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0440
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0441
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0442
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0443
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0444
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0445
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0446
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0447
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_432_433 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (967 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1933 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_432 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_433 ⟨hr,ha.2⟩ hz
theorem cover_434_435 {a z : ℝ} (ha : a ∈ Set.Icc (967 / 5000) (121 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((387 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_434 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_435 ⟨hr,ha.2⟩ hz
theorem cover_432_435 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (121 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((967 / 5000):ℝ) with hl | hr
  · exact cover_432_433 ⟨ha.1,hl⟩ hz
  · exact cover_434_435 ⟨hr,ha.2⟩ hz
theorem cover_436_437 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 625) (969 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1937 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_436 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_437 ⟨hr,ha.2⟩ hz
theorem cover_438_439 {a z : ℝ} (ha : a ∈ Set.Icc (969 / 5000) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1939 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_438 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_439 ⟨hr,ha.2⟩ hz
theorem cover_436_439 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 625) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((969 / 5000):ℝ) with hl | hr
  · exact cover_436_437 ⟨ha.1,hl⟩ hz
  · exact cover_438_439 ⟨hr,ha.2⟩ hz
theorem cover_432_439 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (97 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 625):ℝ) with hl | hr
  · exact cover_432_435 ⟨ha.1,hl⟩ hz
  · exact cover_436_439 ⟨hr,ha.2⟩ hz
theorem cover_440_441 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (971 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1941 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_440 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_441 ⟨hr,ha.2⟩ hz
theorem cover_442_443 {a z : ℝ} (ha : a ∈ Set.Icc (971 / 5000) (243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1943 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_442 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_443 ⟨hr,ha.2⟩ hz
theorem cover_440_443 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((971 / 5000):ℝ) with hl | hr
  · exact cover_440_441 ⟨ha.1,hl⟩ hz
  · exact cover_442_443 ⟨hr,ha.2⟩ hz
theorem cover_444_445 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1250) (973 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((389 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_444 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_445 ⟨hr,ha.2⟩ hz
theorem cover_446_447 {a z : ℝ} (ha : a ∈ Set.Icc (973 / 5000) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1947 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_446 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_447 ⟨hr,ha.2⟩ hz
theorem cover_444_447 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1250) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((973 / 5000):ℝ) with hl | hr
  · exact cover_444_445 ⟨ha.1,hl⟩ hz
  · exact cover_446_447 ⟨hr,ha.2⟩ hz
theorem cover_440_447 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 500) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 1250):ℝ) with hl | hr
  · exact cover_440_443 ⟨ha.1,hl⟩ hz
  · exact cover_444_447 ⟨hr,ha.2⟩ hz
theorem cover_432_447 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 2500) (487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 500):ℝ) with hl | hr
  · exact cover_432_439 ⟨ha.1,hl⟩ hz
  · exact cover_440_447 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

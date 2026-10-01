import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0464
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0465
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0466
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0467
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0468
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0469
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0470
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0471
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0472
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0473
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0474
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0475
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0476
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0477
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0478
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0479
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_464_465 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((393 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_464 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_465 ⟨hr,ha.2⟩ hz
theorem cover_466_467 {a z : ℝ} (ha : a ∈ Set.Icc (983 / 5000) (123 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1967 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_466 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_467 ⟨hr,ha.2⟩ hz
theorem cover_464_467 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (123 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((983 / 5000):ℝ) with hl | hr
  · exact cover_464_465 ⟨ha.1,hl⟩ hz
  · exact cover_466_467 ⟨hr,ha.2⟩ hz
theorem cover_468_469 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 625) (197 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1969 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_468 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_469 ⟨hr,ha.2⟩ hz
theorem cover_470_471 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 1000) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1971 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_470 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_471 ⟨hr,ha.2⟩ hz
theorem cover_468_471 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 625) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 1000):ℝ) with hl | hr
  · exact cover_468_469 ⟨ha.1,hl⟩ hz
  · exact cover_470_471 ⟨hr,ha.2⟩ hz
theorem cover_464_471 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (493 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 625):ℝ) with hl | hr
  · exact cover_464_467 ⟨ha.1,hl⟩ hz
  · exact cover_468_471 ⟨hr,ha.2⟩ hz
theorem cover_472_473 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1973 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_472 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_473 ⟨hr,ha.2⟩ hz
theorem cover_474_475 {a z : ℝ} (ha : a ∈ Set.Icc (987 / 5000) (247 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 400):ℝ) with hl | hr
  · exact curvature_leaf_474 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_475 ⟨hr,ha.2⟩ hz
theorem cover_472_475 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (247 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((987 / 5000):ℝ) with hl | hr
  · exact cover_472_473 ⟨ha.1,hl⟩ hz
  · exact cover_474_475 ⟨hr,ha.2⟩ hz
theorem cover_476_477 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1250) (989 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1977 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_476 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_477 ⟨hr,ha.2⟩ hz
theorem cover_478_479 {a z : ℝ} (ha : a ∈ Set.Icc (989 / 5000) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1979 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_478 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_479 ⟨hr,ha.2⟩ hz
theorem cover_476_479 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1250) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((989 / 5000):ℝ) with hl | hr
  · exact cover_476_477 ⟨ha.1,hl⟩ hz
  · exact cover_478_479 ⟨hr,ha.2⟩ hz
theorem cover_472_479 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 1250):ℝ) with hl | hr
  · exact cover_472_475 ⟨ha.1,hl⟩ hz
  · exact cover_476_479 ⟨hr,ha.2⟩ hz
theorem cover_464_479 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 2500) (99 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 2500):ℝ) with hl | hr
  · exact cover_464_471 ⟨ha.1,hl⟩ hz
  · exact cover_472_479 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

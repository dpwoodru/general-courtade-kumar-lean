import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0448
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0449
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0450
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0451
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0452
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0453
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0454
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0455
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0456
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0457
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0458
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0459
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0460
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0461
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0462
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0463
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_448_449 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (39 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1949 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_448 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_449 ⟨hr,ha.2⟩ hz
theorem cover_450_451 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 200) (122 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1951 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_450 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_451 ⟨hr,ha.2⟩ hz
theorem cover_448_451 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (122 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 200):ℝ) with hl | hr
  · exact cover_448_449 ⟨ha.1,hl⟩ hz
  · exact cover_450_451 ⟨hr,ha.2⟩ hz
theorem cover_452_453 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 625) (977 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1953 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_452 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_453 ⟨hr,ha.2⟩ hz
theorem cover_454_455 {a z : ℝ} (ha : a ∈ Set.Icc (977 / 5000) (489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((391 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_454 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_455 ⟨hr,ha.2⟩ hz
theorem cover_452_455 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 625) (489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((977 / 5000):ℝ) with hl | hr
  · exact cover_452_453 ⟨ha.1,hl⟩ hz
  · exact cover_454_455 ⟨hr,ha.2⟩ hz
theorem cover_448_455 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((122 / 625):ℝ) with hl | hr
  · exact cover_448_451 ⟨ha.1,hl⟩ hz
  · exact cover_452_455 ⟨hr,ha.2⟩ hz
theorem cover_456_457 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 2500) (979 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1957 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_456 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_457 ⟨hr,ha.2⟩ hz
theorem cover_458_459 {a z : ℝ} (ha : a ∈ Set.Icc (979 / 5000) (49 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1959 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_458 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_459 ⟨hr,ha.2⟩ hz
theorem cover_456_459 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 2500) (49 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((979 / 5000):ℝ) with hl | hr
  · exact cover_456_457 ⟨ha.1,hl⟩ hz
  · exact cover_458_459 ⟨hr,ha.2⟩ hz
theorem cover_460_461 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 250) (981 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1961 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_460 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_461 ⟨hr,ha.2⟩ hz
theorem cover_462_463 {a z : ℝ} (ha : a ∈ Set.Icc (981 / 5000) (491 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1963 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_462 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_463 ⟨hr,ha.2⟩ hz
theorem cover_460_463 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 250) (491 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((981 / 5000):ℝ) with hl | hr
  · exact cover_460_461 ⟨ha.1,hl⟩ hz
  · exact cover_462_463 ⟨hr,ha.2⟩ hz
theorem cover_456_463 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 2500) (491 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 250):ℝ) with hl | hr
  · exact cover_456_459 ⟨ha.1,hl⟩ hz
  · exact cover_460_463 ⟨hr,ha.2⟩ hz
theorem cover_448_463 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 2500) (491 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 2500):ℝ) with hl | hr
  · exact cover_448_455 ⟨ha.1,hl⟩ hz
  · exact cover_456_463 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

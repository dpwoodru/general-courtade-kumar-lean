import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0416
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0417
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0418
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0419
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0420
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0421
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0422
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0423
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0424
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0425
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0426
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0427
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0428
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0429
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0430
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0431
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_416_417 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (959 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1917 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_416 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_417 ⟨hr,ha.2⟩ hz
theorem cover_418_419 {a z : ℝ} (ha : a ∈ Set.Icc (959 / 5000) (24 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1919 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_418 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_419 ⟨hr,ha.2⟩ hz
theorem cover_416_419 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (24 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((959 / 5000):ℝ) with hl | hr
  · exact cover_416_417 ⟨ha.1,hl⟩ hz
  · exact cover_418_419 ⟨hr,ha.2⟩ hz
theorem cover_420_421 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 125) (961 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1921 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_420 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_421 ⟨hr,ha.2⟩ hz
theorem cover_422_423 {a z : ℝ} (ha : a ∈ Set.Icc (961 / 5000) (481 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1923 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_422 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_423 ⟨hr,ha.2⟩ hz
theorem cover_420_423 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 125) (481 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((961 / 5000):ℝ) with hl | hr
  · exact cover_420_421 ⟨ha.1,hl⟩ hz
  · exact cover_422_423 ⟨hr,ha.2⟩ hz
theorem cover_416_423 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (481 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((24 / 125):ℝ) with hl | hr
  · exact cover_416_419 ⟨ha.1,hl⟩ hz
  · exact cover_420_423 ⟨hr,ha.2⟩ hz
theorem cover_424_425 {a z : ℝ} (ha : a ∈ Set.Icc (481 / 2500) (963 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 400):ℝ) with hl | hr
  · exact curvature_leaf_424 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_425 ⟨hr,ha.2⟩ hz
theorem cover_426_427 {a z : ℝ} (ha : a ∈ Set.Icc (963 / 5000) (241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1927 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_426 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_427 ⟨hr,ha.2⟩ hz
theorem cover_424_427 {a z : ℝ} (ha : a ∈ Set.Icc (481 / 2500) (241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((963 / 5000):ℝ) with hl | hr
  · exact cover_424_425 ⟨ha.1,hl⟩ hz
  · exact cover_426_427 ⟨hr,ha.2⟩ hz
theorem cover_428_429 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 1250) (193 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1929 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_428 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_429 ⟨hr,ha.2⟩ hz
theorem cover_430_431 {a z : ℝ} (ha : a ∈ Set.Icc (193 / 1000) (483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1931 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_430 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_431 ⟨hr,ha.2⟩ hz
theorem cover_428_431 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 1250) (483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((193 / 1000):ℝ) with hl | hr
  · exact cover_428_429 ⟨ha.1,hl⟩ hz
  · exact cover_430_431 ⟨hr,ha.2⟩ hz
theorem cover_424_431 {a z : ℝ} (ha : a ∈ Set.Icc (481 / 2500) (483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 1250):ℝ) with hl | hr
  · exact cover_424_427 ⟨ha.1,hl⟩ hz
  · exact cover_428_431 ⟨hr,ha.2⟩ hz
theorem cover_416_431 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 2500) (483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 2500):ℝ) with hl | hr
  · exact cover_416_423 ⟨ha.1,hl⟩ hz
  · exact cover_424_431 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

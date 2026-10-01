import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0512
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0513
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0514
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0515
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0516
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0517
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0518
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0519
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0520
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0521
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0522
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0523
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0524
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0525
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0526
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0527
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_512_513 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (207 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((413 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_512 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_513 ⟨hr,ha.2⟩ hz
theorem cover_514_515 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 1000) (26 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 400):ℝ) with hl | hr
  · exact curvature_leaf_514 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_515 ⟨hr,ha.2⟩ hz
theorem cover_512_515 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (26 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((207 / 1000):ℝ) with hl | hr
  · exact cover_512_513 ⟨ha.1,hl⟩ hz
  · exact cover_514_515 ⟨hr,ha.2⟩ hz
theorem cover_516_517 {a z : ℝ} (ha : a ∈ Set.Icc (26 / 125) (209 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((417 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_516 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_517 ⟨hr,ha.2⟩ hz
theorem cover_518_519 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1000) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((419 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_518 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_519 ⟨hr,ha.2⟩ hz
theorem cover_516_519 {a z : ℝ} (ha : a ∈ Set.Icc (26 / 125) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 1000):ℝ) with hl | hr
  · exact cover_516_517 ⟨ha.1,hl⟩ hz
  · exact cover_518_519 ⟨hr,ha.2⟩ hz
theorem cover_512_519 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (21 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((26 / 125):ℝ) with hl | hr
  · exact cover_512_515 ⟨ha.1,hl⟩ hz
  · exact cover_516_519 ⟨hr,ha.2⟩ hz
theorem cover_520_521 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (211 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_520 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_521 ⟨hr,ha.2⟩ hz
theorem cover_522_523 {a z : ℝ} (ha : a ∈ Set.Icc (211 / 1000) (53 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((423 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_522 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_523 ⟨hr,ha.2⟩ hz
theorem cover_520_523 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (53 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((211 / 1000):ℝ) with hl | hr
  · exact cover_520_521 ⟨ha.1,hl⟩ hz
  · exact cover_522_523 ⟨hr,ha.2⟩ hz
theorem cover_524_525 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 250) (213 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 80):ℝ) with hl | hr
  · exact curvature_leaf_524 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_525 ⟨hr,ha.2⟩ hz
theorem cover_526_527 {a z : ℝ} (ha : a ∈ Set.Icc (213 / 1000) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_526 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_527 ⟨hr,ha.2⟩ hz
theorem cover_524_527 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 250) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((213 / 1000):ℝ) with hl | hr
  · exact cover_524_525 ⟨ha.1,hl⟩ hz
  · exact cover_526_527 ⟨hr,ha.2⟩ hz
theorem cover_520_527 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 100) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((53 / 250):ℝ) with hl | hr
  · exact cover_520_523 ⟨ha.1,hl⟩ hz
  · exact cover_524_527 ⟨hr,ha.2⟩ hz
theorem cover_512_527 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 500) (107 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((21 / 100):ℝ) with hl | hr
  · exact cover_512_519 ⟨ha.1,hl⟩ hz
  · exact cover_520_527 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

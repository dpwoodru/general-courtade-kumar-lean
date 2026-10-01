import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0560
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0561
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0562
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0563
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0564
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0565
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0566
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0567
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0568
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0569
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0570
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0571
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0572
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0573
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0574
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0575
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_560_561 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (231 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((461 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_560 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_561 ⟨hr,ha.2⟩ hz
theorem cover_562_563 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 1000) (29 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_562 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_563 ⟨hr,ha.2⟩ hz
theorem cover_560_563 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (29 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((231 / 1000):ℝ) with hl | hr
  · exact cover_560_561 ⟨ha.1,hl⟩ hz
  · exact cover_562_563 ⟨hr,ha.2⟩ hz
theorem cover_564_565 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 125) (233 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 400):ℝ) with hl | hr
  · exact curvature_leaf_564 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_565 ⟨hr,ha.2⟩ hz
theorem cover_566_567 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 1000) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((467 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_566 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_567 ⟨hr,ha.2⟩ hz
theorem cover_564_567 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 125) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 1000):ℝ) with hl | hr
  · exact cover_564_565 ⟨ha.1,hl⟩ hz
  · exact cover_566_567 ⟨hr,ha.2⟩ hz
theorem cover_560_567 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (117 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 125):ℝ) with hl | hr
  · exact cover_560_563 ⟨ha.1,hl⟩ hz
  · exact cover_564_567 ⟨hr,ha.2⟩ hz
theorem cover_568_569 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (47 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_568 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_569 ⟨hr,ha.2⟩ hz
theorem cover_570_571 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 200) (59 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((471 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_570 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_571 ⟨hr,ha.2⟩ hz
theorem cover_568_571 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (59 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 200):ℝ) with hl | hr
  · exact cover_568_569 ⟨ha.1,hl⟩ hz
  · exact cover_570_571 ⟨hr,ha.2⟩ hz
theorem cover_572_573 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 250) (237 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((473 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_572 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_573 ⟨hr,ha.2⟩ hz
theorem cover_574_575 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 1000) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 80):ℝ) with hl | hr
  · exact curvature_leaf_574 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_575 ⟨hr,ha.2⟩ hz
theorem cover_572_575 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 250) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((237 / 1000):ℝ) with hl | hr
  · exact cover_572_573 ⟨ha.1,hl⟩ hz
  · exact cover_574_575 ⟨hr,ha.2⟩ hz
theorem cover_568_575 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 500) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 250):ℝ) with hl | hr
  · exact cover_568_571 ⟨ha.1,hl⟩ hz
  · exact cover_572_575 ⟨hr,ha.2⟩ hz
theorem cover_560_575 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 100) (119 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 500):ℝ) with hl | hr
  · exact cover_560_567 ⟨ha.1,hl⟩ hz
  · exact cover_568_575 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

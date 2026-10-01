import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0592
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0593
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0594
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0595
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0596
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0597
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0598
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0599
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0600
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0601
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0602
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0603
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0604
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0605
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0606
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0607
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_592_593 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (247 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_592 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_593 ⟨hr,ha.2⟩ hz
theorem cover_594_595 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 1000) (31 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 400):ℝ) with hl | hr
  · exact curvature_leaf_594 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_595 ⟨hr,ha.2⟩ hz
theorem cover_592_595 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (31 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 1000):ℝ) with hl | hr
  · exact cover_592_593 ⟨ha.1,hl⟩ hz
  · exact cover_594_595 ⟨hr,ha.2⟩ hz
theorem cover_596_597 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 125) (249 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_596 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_597 ⟨hr,ha.2⟩ hz
theorem cover_598_599 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1000) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_598 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_599 ⟨hr,ha.2⟩ hz
theorem cover_596_599 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 125) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 1000):ℝ) with hl | hr
  · exact cover_596_597 ⟨ha.1,hl⟩ hz
  · exact cover_598_599 ⟨hr,ha.2⟩ hz
theorem cover_592_599 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (1 / 4))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 125):ℝ) with hl | hr
  · exact cover_592_595 ⟨ha.1,hl⟩ hz
  · exact cover_596_599 ⟨hr,ha.2⟩ hz
theorem cover_600_601 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (251 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((501 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_600 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_601 ⟨hr,ha.2⟩ hz
theorem cover_602_603 {a z : ℝ} (ha : a ∈ Set.Icc (251 / 1000) (63 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((503 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_602 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_603 ⟨hr,ha.2⟩ hz
theorem cover_600_603 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (63 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((251 / 1000):ℝ) with hl | hr
  · exact cover_600_601 ⟨ha.1,hl⟩ hz
  · exact cover_602_603 ⟨hr,ha.2⟩ hz
theorem cover_604_605 {a z : ℝ} (ha : a ∈ Set.Icc (63 / 250) (253 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 400):ℝ) with hl | hr
  · exact curvature_leaf_604 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_605 ⟨hr,ha.2⟩ hz
theorem cover_606_607 {a z : ℝ} (ha : a ∈ Set.Icc (253 / 1000) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((507 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_606 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_607 ⟨hr,ha.2⟩ hz
theorem cover_604_607 {a z : ℝ} (ha : a ∈ Set.Icc (63 / 250) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((253 / 1000):ℝ) with hl | hr
  · exact cover_604_605 ⟨ha.1,hl⟩ hz
  · exact cover_606_607 ⟨hr,ha.2⟩ hz
theorem cover_600_607 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 4) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((63 / 250):ℝ) with hl | hr
  · exact cover_600_603 ⟨ha.1,hl⟩ hz
  · exact cover_604_607 ⟨hr,ha.2⟩ hz
theorem cover_592_607 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 500) (127 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1 / 4):ℝ) with hl | hr
  · exact cover_592_599 ⟨ha.1,hl⟩ hz
  · exact cover_600_607 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

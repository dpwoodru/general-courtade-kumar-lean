import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0688
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0689
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0690
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0691
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0692
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0693
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0694
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0695
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0696
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0697
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0698
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0699
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0700
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0701
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0702
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0703
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_688_689 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (59 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((589 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_688 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_689 ⟨hr,ha.2⟩ hz
theorem cover_690_691 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 200) (37 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((591 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_690 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_691 ⟨hr,ha.2⟩ hz
theorem cover_688_691 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (37 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 200):ℝ) with hl | hr
  · exact cover_688_689 ⟨ha.1,hl⟩ hz
  · exact cover_690_691 ⟨hr,ha.2⟩ hz
theorem cover_692_693 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 125) (297 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((593 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_692 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_693 ⟨hr,ha.2⟩ hz
theorem cover_694_695 {a z : ℝ} (ha : a ∈ Set.Icc (297 / 1000) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 400):ℝ) with hl | hr
  · exact curvature_leaf_694 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_695 ⟨hr,ha.2⟩ hz
theorem cover_692_695 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 125) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((297 / 1000):ℝ) with hl | hr
  · exact cover_692_693 ⟨ha.1,hl⟩ hz
  · exact cover_694_695 ⟨hr,ha.2⟩ hz
theorem cover_688_695 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (149 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 125):ℝ) with hl | hr
  · exact cover_688_691 ⟨ha.1,hl⟩ hz
  · exact cover_692_695 ⟨hr,ha.2⟩ hz
theorem cover_696_697 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (299 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((597 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_696 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_697 ⟨hr,ha.2⟩ hz
theorem cover_698_699 {a z : ℝ} (ha : a ∈ Set.Icc (299 / 1000) (3 / 10))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((599 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_698 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_699 ⟨hr,ha.2⟩ hz
theorem cover_696_699 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (3 / 10))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((299 / 1000):ℝ) with hl | hr
  · exact cover_696_697 ⟨ha.1,hl⟩ hz
  · exact cover_698_699 ⟨hr,ha.2⟩ hz
theorem cover_700_701 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 10) (151 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((301 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_700 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_701 ⟨hr,ha.2⟩ hz
theorem cover_702_703 {a z : ℝ} (ha : a ∈ Set.Icc (151 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((303 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_702 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_703 ⟨hr,ha.2⟩ hz
theorem cover_700_703 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 10) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((151 / 500):ℝ) with hl | hr
  · exact cover_700_701 ⟨ha.1,hl⟩ hz
  · exact cover_702_703 ⟨hr,ha.2⟩ hz
theorem cover_696_703 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((3 / 10):ℝ) with hl | hr
  · exact cover_696_699 ⟨ha.1,hl⟩ hz
  · exact cover_700_703 ⟨hr,ha.2⟩ hz
theorem cover_688_703 {a z : ℝ} (ha : a ∈ Set.Icc (147 / 500) (38 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((149 / 500):ℝ) with hl | hr
  · exact cover_688_695 ⟨ha.1,hl⟩ hz
  · exact cover_696_703 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

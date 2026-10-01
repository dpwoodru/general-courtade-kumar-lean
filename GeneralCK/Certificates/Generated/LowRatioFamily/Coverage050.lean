import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0800
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0801
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0802
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0803
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0804
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0805
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0806
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0807
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0808
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0809
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0810
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0811
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0812
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0813
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0814
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0815
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_800_801 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (201 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((401 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_800 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_801 ⟨hr,ha.2⟩ hz
theorem cover_802_803 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 500) (101 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_802 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_803 ⟨hr,ha.2⟩ hz
theorem cover_800_803 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (101 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((201 / 500):ℝ) with hl | hr
  · exact cover_800_801 ⟨ha.1,hl⟩ hz
  · exact cover_802_803 ⟨hr,ha.2⟩ hz
theorem cover_804_805 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 250) (203 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 200):ℝ) with hl | hr
  · exact curvature_leaf_804 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_805 ⟨hr,ha.2⟩ hz
theorem cover_806_807 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 500) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((407 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_806 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_807 ⟨hr,ha.2⟩ hz
theorem cover_804_807 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 250) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 500):ℝ) with hl | hr
  · exact cover_804_805 ⟨ha.1,hl⟩ hz
  · exact cover_806_807 ⟨hr,ha.2⟩ hz
theorem cover_800_807 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (51 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 250):ℝ) with hl | hr
  · exact cover_800_803 ⟨ha.1,hl⟩ hz
  · exact cover_804_807 ⟨hr,ha.2⟩ hz
theorem cover_808_809 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (41 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_808 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_809 ⟨hr,ha.2⟩ hz
theorem cover_810_811 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 100) (103 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((411 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_810 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_811 ⟨hr,ha.2⟩ hz
theorem cover_808_811 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (103 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 100):ℝ) with hl | hr
  · exact cover_808_809 ⟨ha.1,hl⟩ hz
  · exact cover_810_811 ⟨hr,ha.2⟩ hz
theorem cover_812_813 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 250) (207 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((413 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_812 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_813 ⟨hr,ha.2⟩ hz
theorem cover_814_815 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 500) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 200):ℝ) with hl | hr
  · exact curvature_leaf_814 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_815 ⟨hr,ha.2⟩ hz
theorem cover_812_815 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 250) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((207 / 500):ℝ) with hl | hr
  · exact cover_812_813 ⟨ha.1,hl⟩ hz
  · exact cover_814_815 ⟨hr,ha.2⟩ hz
theorem cover_808_815 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 125) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 250):ℝ) with hl | hr
  · exact cover_808_811 ⟨ha.1,hl⟩ hz
  · exact cover_812_815 ⟨hr,ha.2⟩ hz
theorem cover_800_815 {a z : ℝ} (ha : a ∈ Set.Icc (2 / 5) (52 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((51 / 125):ℝ) with hl | hr
  · exact cover_800_807 ⟨ha.1,hl⟩ hz
  · exact cover_808_815 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

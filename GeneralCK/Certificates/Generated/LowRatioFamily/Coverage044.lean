import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0704
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0705
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0706
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0707
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0708
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0709
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0710
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0711
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0712
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0713
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0714
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0715
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0716
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0717
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0718
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0719
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_704_705 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (153 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 200):ℝ) with hl | hr
  · exact curvature_leaf_704 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_705 ⟨hr,ha.2⟩ hz
theorem cover_706_707 {a z : ℝ} (ha : a ∈ Set.Icc (153 / 500) (77 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((307 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_706 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_707 ⟨hr,ha.2⟩ hz
theorem cover_704_707 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (77 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((153 / 500):ℝ) with hl | hr
  · exact cover_704_705 ⟨ha.1,hl⟩ hz
  · exact cover_706_707 ⟨hr,ha.2⟩ hz
theorem cover_708_709 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 250) (31 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((309 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_708 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_709 ⟨hr,ha.2⟩ hz
theorem cover_710_711 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 100) (39 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((311 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_710 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_711 ⟨hr,ha.2⟩ hz
theorem cover_708_711 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 250) (39 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 100):ℝ) with hl | hr
  · exact cover_708_709 ⟨ha.1,hl⟩ hz
  · exact cover_710_711 ⟨hr,ha.2⟩ hz
theorem cover_704_711 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (39 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 250):ℝ) with hl | hr
  · exact cover_704_707 ⟨ha.1,hl⟩ hz
  · exact cover_708_711 ⟨hr,ha.2⟩ hz
theorem cover_712_713 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 125) (157 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((313 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_712 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_713 ⟨hr,ha.2⟩ hz
theorem cover_714_715 {a z : ℝ} (ha : a ∈ Set.Icc (157 / 500) (79 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((63 / 200):ℝ) with hl | hr
  · exact curvature_leaf_714 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_715 ⟨hr,ha.2⟩ hz
theorem cover_712_715 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 125) (79 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((157 / 500):ℝ) with hl | hr
  · exact cover_712_713 ⟨ha.1,hl⟩ hz
  · exact cover_714_715 ⟨hr,ha.2⟩ hz
theorem cover_716_717 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 250) (159 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((317 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_716 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_717 ⟨hr,ha.2⟩ hz
theorem cover_718_719 {a z : ℝ} (ha : a ∈ Set.Icc (159 / 500) (8 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((319 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_718 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_719 ⟨hr,ha.2⟩ hz
theorem cover_716_719 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 250) (8 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((159 / 500):ℝ) with hl | hr
  · exact cover_716_717 ⟨ha.1,hl⟩ hz
  · exact cover_718_719 ⟨hr,ha.2⟩ hz
theorem cover_712_719 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 125) (8 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((79 / 250):ℝ) with hl | hr
  · exact cover_712_715 ⟨ha.1,hl⟩ hz
  · exact cover_716_719 ⟨hr,ha.2⟩ hz
theorem cover_704_719 {a z : ℝ} (ha : a ∈ Set.Icc (38 / 125) (8 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 125):ℝ) with hl | hr
  · exact cover_704_711 ⟨ha.1,hl⟩ hz
  · exact cover_712_719 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

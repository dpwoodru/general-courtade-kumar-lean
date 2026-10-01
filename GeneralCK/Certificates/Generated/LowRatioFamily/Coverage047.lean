import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0752
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0753
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0754
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0755
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0756
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0757
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0758
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0759
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0760
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0761
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0762
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0763
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0764
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0765
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0766
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0767
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_752_753 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (177 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((353 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_752 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_753 ⟨hr,ha.2⟩ hz
theorem cover_754_755 {a z : ℝ} (ha : a ∈ Set.Icc (177 / 500) (89 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 200):ℝ) with hl | hr
  · exact curvature_leaf_754 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_755 ⟨hr,ha.2⟩ hz
theorem cover_752_755 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (89 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((177 / 500):ℝ) with hl | hr
  · exact cover_752_753 ⟨ha.1,hl⟩ hz
  · exact cover_754_755 ⟨hr,ha.2⟩ hz
theorem cover_756_757 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 250) (179 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((357 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_756 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_757 ⟨hr,ha.2⟩ hz
theorem cover_758_759 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 500) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((359 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_758 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_759 ⟨hr,ha.2⟩ hz
theorem cover_756_759 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 250) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 500):ℝ) with hl | hr
  · exact cover_756_757 ⟨ha.1,hl⟩ hz
  · exact cover_758_759 ⟨hr,ha.2⟩ hz
theorem cover_752_759 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (9 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 250):ℝ) with hl | hr
  · exact cover_752_755 ⟨ha.1,hl⟩ hz
  · exact cover_756_759 ⟨hr,ha.2⟩ hz
theorem cover_760_761 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (181 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((361 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_760 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_761 ⟨hr,ha.2⟩ hz
theorem cover_762_763 {a z : ℝ} (ha : a ∈ Set.Icc (181 / 500) (91 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((363 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_762 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_763 ⟨hr,ha.2⟩ hz
theorem cover_760_763 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (91 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((181 / 500):ℝ) with hl | hr
  · exact cover_760_761 ⟨ha.1,hl⟩ hz
  · exact cover_762_763 ⟨hr,ha.2⟩ hz
theorem cover_764_765 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 250) (183 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 200):ℝ) with hl | hr
  · exact curvature_leaf_764 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_765 ⟨hr,ha.2⟩ hz
theorem cover_766_767 {a z : ℝ} (ha : a ∈ Set.Icc (183 / 500) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((367 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_766 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_767 ⟨hr,ha.2⟩ hz
theorem cover_764_767 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 250) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((183 / 500):ℝ) with hl | hr
  · exact cover_764_765 ⟨ha.1,hl⟩ hz
  · exact cover_766_767 ⟨hr,ha.2⟩ hz
theorem cover_760_767 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 25) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 250):ℝ) with hl | hr
  · exact cover_760_763 ⟨ha.1,hl⟩ hz
  · exact cover_764_767 ⟨hr,ha.2⟩ hz
theorem cover_752_767 {a z : ℝ} (ha : a ∈ Set.Icc (44 / 125) (46 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 25):ℝ) with hl | hr
  · exact cover_752_759 ⟨ha.1,hl⟩ hz
  · exact cover_760_767 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

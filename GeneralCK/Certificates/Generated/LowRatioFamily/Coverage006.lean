import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0096
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0097
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0098
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0099
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0100
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0101
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0102
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0103
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0104
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0105
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0106
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0107
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0108
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0109
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0110
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0111
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_96_97 {a z : ℝ} (ha : a ∈ Set.Icc (399 / 2500) (799 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1597 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_96 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_97 ⟨hr,ha.2⟩ hz
theorem cover_98_99 {a z : ℝ} (ha : a ∈ Set.Icc (799 / 5000) (4 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1599 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_98 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_99 ⟨hr,ha.2⟩ hz
theorem cover_96_99 {a z : ℝ} (ha : a ∈ Set.Icc (399 / 2500) (4 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((799 / 5000):ℝ) with hl | hr
  · exact cover_96_97 ⟨ha.1,hl⟩ hz
  · exact cover_98_99 ⟨hr,ha.2⟩ hz
theorem cover_100_101 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 25) (801 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1601 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_100 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_101 ⟨hr,ha.2⟩ hz
theorem cover_102_103 {a z : ℝ} (ha : a ∈ Set.Icc (801 / 5000) (401 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1603 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_102 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_103 ⟨hr,ha.2⟩ hz
theorem cover_100_103 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 25) (401 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((801 / 5000):ℝ) with hl | hr
  · exact cover_100_101 ⟨ha.1,hl⟩ hz
  · exact cover_102_103 ⟨hr,ha.2⟩ hz
theorem cover_96_103 {a z : ℝ} (ha : a ∈ Set.Icc (399 / 2500) (401 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4 / 25):ℝ) with hl | hr
  · exact cover_96_99 ⟨ha.1,hl⟩ hz
  · exact cover_100_103 ⟨hr,ha.2⟩ hz
theorem cover_104_105 {a z : ℝ} (ha : a ∈ Set.Icc (401 / 2500) (803 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((321 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_104 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_105 ⟨hr,ha.2⟩ hz
theorem cover_106_107 {a z : ℝ} (ha : a ∈ Set.Icc (803 / 5000) (201 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1607 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_106 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_107 ⟨hr,ha.2⟩ hz
theorem cover_104_107 {a z : ℝ} (ha : a ∈ Set.Icc (401 / 2500) (201 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((803 / 5000):ℝ) with hl | hr
  · exact cover_104_105 ⟨ha.1,hl⟩ hz
  · exact cover_106_107 ⟨hr,ha.2⟩ hz
theorem cover_108_109 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 1250) (161 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1609 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_108 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_109 ⟨hr,ha.2⟩ hz
theorem cover_110_111 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 1000) (403 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1611 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_110 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_111 ⟨hr,ha.2⟩ hz
theorem cover_108_111 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 1250) (403 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((161 / 1000):ℝ) with hl | hr
  · exact cover_108_109 ⟨ha.1,hl⟩ hz
  · exact cover_110_111 ⟨hr,ha.2⟩ hz
theorem cover_104_111 {a z : ℝ} (ha : a ∈ Set.Icc (401 / 2500) (403 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((201 / 1250):ℝ) with hl | hr
  · exact cover_104_107 ⟨ha.1,hl⟩ hz
  · exact cover_108_111 ⟨hr,ha.2⟩ hz
theorem cover_96_111 {a z : ℝ} (ha : a ∈ Set.Icc (399 / 2500) (403 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((401 / 2500):ℝ) with hl | hr
  · exact cover_96_103 ⟨ha.1,hl⟩ hz
  · exact cover_104_111 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

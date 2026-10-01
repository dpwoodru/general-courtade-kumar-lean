import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0128
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0129
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0130
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0131
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0132
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0133
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0134
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0135
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0136
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0137
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0138
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0139
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0140
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0141
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0142
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0143
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_128_129 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (163 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1629 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_128 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_129 ⟨hr,ha.2⟩ hz
theorem cover_130_131 {a z : ℝ} (ha : a ∈ Set.Icc (163 / 1000) (102 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1631 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_130 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_131 ⟨hr,ha.2⟩ hz
theorem cover_128_131 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (102 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((163 / 1000):ℝ) with hl | hr
  · exact cover_128_129 ⟨ha.1,hl⟩ hz
  · exact cover_130_131 ⟨hr,ha.2⟩ hz
theorem cover_132_133 {a z : ℝ} (ha : a ∈ Set.Icc (102 / 625) (817 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1633 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_132 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_133 ⟨hr,ha.2⟩ hz
theorem cover_134_135 {a z : ℝ} (ha : a ∈ Set.Icc (817 / 5000) (409 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((327 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_134 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_135 ⟨hr,ha.2⟩ hz
theorem cover_132_135 {a z : ℝ} (ha : a ∈ Set.Icc (102 / 625) (409 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((817 / 5000):ℝ) with hl | hr
  · exact cover_132_133 ⟨ha.1,hl⟩ hz
  · exact cover_134_135 ⟨hr,ha.2⟩ hz
theorem cover_128_135 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (409 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((102 / 625):ℝ) with hl | hr
  · exact cover_128_131 ⟨ha.1,hl⟩ hz
  · exact cover_132_135 ⟨hr,ha.2⟩ hz
theorem cover_136_137 {a z : ℝ} (ha : a ∈ Set.Icc (409 / 2500) (819 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1637 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_136 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_137 ⟨hr,ha.2⟩ hz
theorem cover_138_139 {a z : ℝ} (ha : a ∈ Set.Icc (819 / 5000) (41 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1639 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_138 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_139 ⟨hr,ha.2⟩ hz
theorem cover_136_139 {a z : ℝ} (ha : a ∈ Set.Icc (409 / 2500) (41 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((819 / 5000):ℝ) with hl | hr
  · exact cover_136_137 ⟨ha.1,hl⟩ hz
  · exact cover_138_139 ⟨hr,ha.2⟩ hz
theorem cover_140_141 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 250) (821 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1641 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_140 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_141 ⟨hr,ha.2⟩ hz
theorem cover_142_143 {a z : ℝ} (ha : a ∈ Set.Icc (821 / 5000) (411 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1643 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_142 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_143 ⟨hr,ha.2⟩ hz
theorem cover_140_143 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 250) (411 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((821 / 5000):ℝ) with hl | hr
  · exact cover_140_141 ⟨ha.1,hl⟩ hz
  · exact cover_142_143 ⟨hr,ha.2⟩ hz
theorem cover_136_143 {a z : ℝ} (ha : a ∈ Set.Icc (409 / 2500) (411 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 250):ℝ) with hl | hr
  · exact cover_136_139 ⟨ha.1,hl⟩ hz
  · exact cover_140_143 ⟨hr,ha.2⟩ hz
theorem cover_128_143 {a z : ℝ} (ha : a ∈ Set.Icc (407 / 2500) (411 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 2500):ℝ) with hl | hr
  · exact cover_128_135 ⟨ha.1,hl⟩ hz
  · exact cover_136_143 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

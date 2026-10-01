import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0144
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0145
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0146
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0147
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0148
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0149
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0150
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0151
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0152
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0153
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0154
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0155
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0156
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0157
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0158
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0159
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_144_145 {a z : ℝ} (ha : a ∈ Set.Icc (411 / 2500) (823 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((329 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_144 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_145 ⟨hr,ha.2⟩ hz
theorem cover_146_147 {a z : ℝ} (ha : a ∈ Set.Icc (823 / 5000) (103 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1647 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_146 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_147 ⟨hr,ha.2⟩ hz
theorem cover_144_147 {a z : ℝ} (ha : a ∈ Set.Icc (411 / 2500) (103 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((823 / 5000):ℝ) with hl | hr
  · exact cover_144_145 ⟨ha.1,hl⟩ hz
  · exact cover_146_147 ⟨hr,ha.2⟩ hz
theorem cover_148_149 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 625) (33 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1649 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_148 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_149 ⟨hr,ha.2⟩ hz
theorem cover_150_151 {a z : ℝ} (ha : a ∈ Set.Icc (33 / 200) (413 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1651 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_150 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_151 ⟨hr,ha.2⟩ hz
theorem cover_148_151 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 625) (413 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((33 / 200):ℝ) with hl | hr
  · exact cover_148_149 ⟨ha.1,hl⟩ hz
  · exact cover_150_151 ⟨hr,ha.2⟩ hz
theorem cover_144_151 {a z : ℝ} (ha : a ∈ Set.Icc (411 / 2500) (413 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 625):ℝ) with hl | hr
  · exact cover_144_147 ⟨ha.1,hl⟩ hz
  · exact cover_148_151 ⟨hr,ha.2⟩ hz
theorem cover_152_153 {a z : ℝ} (ha : a ∈ Set.Icc (413 / 2500) (827 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1653 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_152 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_153 ⟨hr,ha.2⟩ hz
theorem cover_154_155 {a z : ℝ} (ha : a ∈ Set.Icc (827 / 5000) (207 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((331 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_154 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_155 ⟨hr,ha.2⟩ hz
theorem cover_152_155 {a z : ℝ} (ha : a ∈ Set.Icc (413 / 2500) (207 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((827 / 5000):ℝ) with hl | hr
  · exact cover_152_153 ⟨ha.1,hl⟩ hz
  · exact cover_154_155 ⟨hr,ha.2⟩ hz
theorem cover_156_157 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 1250) (829 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1657 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_156 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_157 ⟨hr,ha.2⟩ hz
theorem cover_158_159 {a z : ℝ} (ha : a ∈ Set.Icc (829 / 5000) (83 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1659 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_158 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_159 ⟨hr,ha.2⟩ hz
theorem cover_156_159 {a z : ℝ} (ha : a ∈ Set.Icc (207 / 1250) (83 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((829 / 5000):ℝ) with hl | hr
  · exact cover_156_157 ⟨ha.1,hl⟩ hz
  · exact cover_158_159 ⟨hr,ha.2⟩ hz
theorem cover_152_159 {a z : ℝ} (ha : a ∈ Set.Icc (413 / 2500) (83 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((207 / 1250):ℝ) with hl | hr
  · exact cover_152_155 ⟨ha.1,hl⟩ hz
  · exact cover_156_159 ⟨hr,ha.2⟩ hz
theorem cover_144_159 {a z : ℝ} (ha : a ∈ Set.Icc (411 / 2500) (83 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((413 / 2500):ℝ) with hl | hr
  · exact cover_144_151 ⟨ha.1,hl⟩ hz
  · exact cover_152_159 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

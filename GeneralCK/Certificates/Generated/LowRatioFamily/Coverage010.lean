import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0160
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0161
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0162
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0163
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0164
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0165
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0166
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0167
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0168
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0169
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0170
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0171
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0172
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0173
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0174
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0175
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_160_161 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (831 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1661 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_160 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_161 ⟨hr,ha.2⟩ hz
theorem cover_162_163 {a z : ℝ} (ha : a ∈ Set.Icc (831 / 5000) (104 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1663 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_162 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_163 ⟨hr,ha.2⟩ hz
theorem cover_160_163 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (104 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((831 / 5000):ℝ) with hl | hr
  · exact cover_160_161 ⟨ha.1,hl⟩ hz
  · exact cover_162_163 ⟨hr,ha.2⟩ hz
theorem cover_164_165 {a z : ℝ} (ha : a ∈ Set.Icc (104 / 625) (833 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((333 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_164 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_165 ⟨hr,ha.2⟩ hz
theorem cover_166_167 {a z : ℝ} (ha : a ∈ Set.Icc (833 / 5000) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1667 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_166 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_167 ⟨hr,ha.2⟩ hz
theorem cover_164_167 {a z : ℝ} (ha : a ∈ Set.Icc (104 / 625) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((833 / 5000):ℝ) with hl | hr
  · exact cover_164_165 ⟨ha.1,hl⟩ hz
  · exact cover_166_167 ⟨hr,ha.2⟩ hz
theorem cover_160_167 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (417 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((104 / 625):ℝ) with hl | hr
  · exact cover_160_163 ⟨ha.1,hl⟩ hz
  · exact cover_164_167 ⟨hr,ha.2⟩ hz
theorem cover_168_169 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (167 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1669 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_168 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_169 ⟨hr,ha.2⟩ hz
theorem cover_170_171 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 1000) (209 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1671 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_170 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_171 ⟨hr,ha.2⟩ hz
theorem cover_168_171 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (209 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((167 / 1000):ℝ) with hl | hr
  · exact cover_168_169 ⟨ha.1,hl⟩ hz
  · exact cover_170_171 ⟨hr,ha.2⟩ hz
theorem cover_172_173 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1250) (837 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1673 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_172 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_173 ⟨hr,ha.2⟩ hz
theorem cover_174_175 {a z : ℝ} (ha : a ∈ Set.Icc (837 / 5000) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((67 / 400):ℝ) with hl | hr
  · exact curvature_leaf_174 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_175 ⟨hr,ha.2⟩ hz
theorem cover_172_175 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 1250) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((837 / 5000):ℝ) with hl | hr
  · exact cover_172_173 ⟨ha.1,hl⟩ hz
  · exact cover_174_175 ⟨hr,ha.2⟩ hz
theorem cover_168_175 {a z : ℝ} (ha : a ∈ Set.Icc (417 / 2500) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 1250):ℝ) with hl | hr
  · exact cover_168_171 ⟨ha.1,hl⟩ hz
  · exact cover_172_175 ⟨hr,ha.2⟩ hz
theorem cover_160_175 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 500) (419 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((417 / 2500):ℝ) with hl | hr
  · exact cover_160_167 ⟨ha.1,hl⟩ hz
  · exact cover_168_175 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

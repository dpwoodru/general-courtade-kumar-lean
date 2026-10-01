import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0176
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0177
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0178
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0179
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0180
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0181
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0182
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0183
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0184
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0185
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0186
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0187
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0188
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0189
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0190
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0191
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_176_177 {a z : ℝ} (ha : a ∈ Set.Icc (419 / 2500) (839 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1677 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_176 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_177 ⟨hr,ha.2⟩ hz
theorem cover_178_179 {a z : ℝ} (ha : a ∈ Set.Icc (839 / 5000) (21 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1679 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_178 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_179 ⟨hr,ha.2⟩ hz
theorem cover_176_179 {a z : ℝ} (ha : a ∈ Set.Icc (419 / 2500) (21 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((839 / 5000):ℝ) with hl | hr
  · exact cover_176_177 ⟨ha.1,hl⟩ hz
  · exact cover_178_179 ⟨hr,ha.2⟩ hz
theorem cover_180_181 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 125) (841 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1681 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_180 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_181 ⟨hr,ha.2⟩ hz
theorem cover_182_183 {a z : ℝ} (ha : a ∈ Set.Icc (841 / 5000) (421 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1683 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_182 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_183 ⟨hr,ha.2⟩ hz
theorem cover_180_183 {a z : ℝ} (ha : a ∈ Set.Icc (21 / 125) (421 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((841 / 5000):ℝ) with hl | hr
  · exact cover_180_181 ⟨ha.1,hl⟩ hz
  · exact cover_182_183 ⟨hr,ha.2⟩ hz
theorem cover_176_183 {a z : ℝ} (ha : a ∈ Set.Icc (419 / 2500) (421 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((21 / 125):ℝ) with hl | hr
  · exact cover_176_179 ⟨ha.1,hl⟩ hz
  · exact cover_180_183 ⟨hr,ha.2⟩ hz
theorem cover_184_185 {a z : ℝ} (ha : a ∈ Set.Icc (421 / 2500) (843 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((337 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_184 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_185 ⟨hr,ha.2⟩ hz
theorem cover_186_187 {a z : ℝ} (ha : a ∈ Set.Icc (843 / 5000) (211 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1687 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_186 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_187 ⟨hr,ha.2⟩ hz
theorem cover_184_187 {a z : ℝ} (ha : a ∈ Set.Icc (421 / 2500) (211 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((843 / 5000):ℝ) with hl | hr
  · exact cover_184_185 ⟨ha.1,hl⟩ hz
  · exact cover_186_187 ⟨hr,ha.2⟩ hz
theorem cover_188_189 {a z : ℝ} (ha : a ∈ Set.Icc (211 / 1250) (169 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1689 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_188 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_189 ⟨hr,ha.2⟩ hz
theorem cover_190_191 {a z : ℝ} (ha : a ∈ Set.Icc (169 / 1000) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1691 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_190 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_191 ⟨hr,ha.2⟩ hz
theorem cover_188_191 {a z : ℝ} (ha : a ∈ Set.Icc (211 / 1250) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((169 / 1000):ℝ) with hl | hr
  · exact cover_188_189 ⟨ha.1,hl⟩ hz
  · exact cover_190_191 ⟨hr,ha.2⟩ hz
theorem cover_184_191 {a z : ℝ} (ha : a ∈ Set.Icc (421 / 2500) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((211 / 1250):ℝ) with hl | hr
  · exact cover_184_187 ⟨ha.1,hl⟩ hz
  · exact cover_188_191 ⟨hr,ha.2⟩ hz
theorem cover_176_191 {a z : ℝ} (ha : a ∈ Set.Icc (419 / 2500) (423 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 2500):ℝ) with hl | hr
  · exact cover_176_183 ⟨ha.1,hl⟩ hz
  · exact cover_184_191 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

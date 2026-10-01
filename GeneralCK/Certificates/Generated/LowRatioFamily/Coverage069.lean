import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1104
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1105
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1106
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1107
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1108
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1109
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1110
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1111
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1112
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1113
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1114
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1115
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1116
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1117
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1118
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1119
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1104_1105 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (2483 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((993 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1104 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1105 ⟨hr,ha.2⟩ hz
theorem cover_1106_1107 {a z : ℝ} (ha : a ∈ Set.Icc (2483 / 2500) (621 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4967 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1106 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1107 ⟨hr,ha.2⟩ hz
theorem cover_1104_1107 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (621 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2483 / 2500):ℝ) with hl | hr
  · exact cover_1104_1105 ⟨ha.1,hl⟩ hz
  · exact cover_1106_1107 ⟨hr,ha.2⟩ hz
theorem cover_1108_1109 {a z : ℝ} (ha : a ∈ Set.Icc (621 / 625) (497 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4969 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1108 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1109 ⟨hr,ha.2⟩ hz
theorem cover_1110_1111 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 500) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4971 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1110 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1111 ⟨hr,ha.2⟩ hz
theorem cover_1108_1111 {a z : ℝ} (ha : a ∈ Set.Icc (621 / 625) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 500):ℝ) with hl | hr
  · exact cover_1108_1109 ⟨ha.1,hl⟩ hz
  · exact cover_1110_1111 ⟨hr,ha.2⟩ hz
theorem cover_1104_1111 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (1243 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((621 / 625):ℝ) with hl | hr
  · exact cover_1104_1107 ⟨ha.1,hl⟩ hz
  · exact cover_1108_1111 ⟨hr,ha.2⟩ hz
theorem cover_1112_1113 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (2487 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4973 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1112 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1113 ⟨hr,ha.2⟩ hz
theorem cover_1114_1115 {a z : ℝ} (ha : a ∈ Set.Icc (2487 / 2500) (622 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1114 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1115 ⟨hr,ha.2⟩ hz
theorem cover_1112_1115 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (622 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2487 / 2500):ℝ) with hl | hr
  · exact cover_1112_1113 ⟨ha.1,hl⟩ hz
  · exact cover_1114_1115 ⟨hr,ha.2⟩ hz
theorem cover_1116_1117 {a z : ℝ} (ha : a ∈ Set.Icc (622 / 625) (2489 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4977 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1116 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1117 ⟨hr,ha.2⟩ hz
theorem cover_1118_1119 {a z : ℝ} (ha : a ∈ Set.Icc (2489 / 2500) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4979 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1118 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1119 ⟨hr,ha.2⟩ hz
theorem cover_1116_1119 {a z : ℝ} (ha : a ∈ Set.Icc (622 / 625) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2489 / 2500):ℝ) with hl | hr
  · exact cover_1116_1117 ⟨ha.1,hl⟩ hz
  · exact cover_1118_1119 ⟨hr,ha.2⟩ hz
theorem cover_1112_1119 {a z : ℝ} (ha : a ∈ Set.Icc (1243 / 1250) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((622 / 625):ℝ) with hl | hr
  · exact cover_1112_1115 ⟨ha.1,hl⟩ hz
  · exact cover_1116_1119 ⟨hr,ha.2⟩ hz
theorem cover_1104_1119 {a z : ℝ} (ha : a ∈ Set.Icc (1241 / 1250) (249 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1243 / 1250):ℝ) with hl | hr
  · exact cover_1104_1111 ⟨ha.1,hl⟩ hz
  · exact cover_1112_1119 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

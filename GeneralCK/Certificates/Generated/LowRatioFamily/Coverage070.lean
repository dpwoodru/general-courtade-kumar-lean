import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1120
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1121
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1122
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1123
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1124
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1125
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1126
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1127
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1128
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1129
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1130
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1131
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1132
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1133
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1134
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1121_1122 {a z : ℝ} (ha : a ∈ Set.Icc (4981 / 5000) (4983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2491 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1121 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1122 ⟨hr,ha.2⟩ hz
theorem cover_1120_1122 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (4983 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4981 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1120 ⟨ha.1,hl⟩ hz
  · exact cover_1121_1122 ⟨hr,ha.2⟩ hz
theorem cover_1123_1124 {a z : ℝ} (ha : a ∈ Set.Icc (4983 / 5000) (997 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((623 / 625):ℝ) with hl | hr
  · exact curvature_leaf_1123 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1124 ⟨hr,ha.2⟩ hz
theorem cover_1125_1126 {a z : ℝ} (ha : a ∈ Set.Icc (997 / 1000) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2493 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1125 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1126 ⟨hr,ha.2⟩ hz
theorem cover_1123_1126 {a z : ℝ} (ha : a ∈ Set.Icc (4983 / 5000) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((997 / 1000):ℝ) with hl | hr
  · exact cover_1123_1124 ⟨ha.1,hl⟩ hz
  · exact cover_1125_1126 ⟨hr,ha.2⟩ hz
theorem cover_1120_1126 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (4987 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4983 / 5000):ℝ) with hl | hr
  · exact cover_1120_1122 ⟨ha.1,hl⟩ hz
  · exact cover_1123_1126 ⟨hr,ha.2⟩ hz
theorem cover_1127_1128 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (4989 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1247 / 1250):ℝ) with hl | hr
  · exact curvature_leaf_1127 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1128 ⟨hr,ha.2⟩ hz
theorem cover_1129_1130 {a z : ℝ} (ha : a ∈ Set.Icc (4989 / 5000) (4991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 500):ℝ) with hl | hr
  · exact curvature_leaf_1129 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1130 ⟨hr,ha.2⟩ hz
theorem cover_1127_1130 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (4991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4989 / 5000):ℝ) with hl | hr
  · exact cover_1127_1128 ⟨ha.1,hl⟩ hz
  · exact cover_1129_1130 ⟨hr,ha.2⟩ hz
theorem cover_1131_1132 {a z : ℝ} (ha : a ∈ Set.Icc (4991 / 5000) (4993 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((624 / 625):ℝ) with hl | hr
  · exact curvature_leaf_1131 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1132 ⟨hr,ha.2⟩ hz
theorem cover_1133_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4993 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2497 / 2500):ℝ) with hl | hr
  · exact curvature_leaf_1133 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1134 ⟨hr,ha.2⟩ hz
theorem cover_1131_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4991 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4993 / 5000):ℝ) with hl | hr
  · exact cover_1131_1132 ⟨ha.1,hl⟩ hz
  · exact cover_1133_1134 ⟨hr,ha.2⟩ hz
theorem cover_1127_1134 {a z : ℝ} (ha : a ∈ Set.Icc (4987 / 5000) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4991 / 5000):ℝ) with hl | hr
  · exact cover_1127_1130 ⟨ha.1,hl⟩ hz
  · exact cover_1131_1134 ⟨hr,ha.2⟩ hz
theorem cover_1120_1134 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 250) (999 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4987 / 5000):ℝ) with hl | hr
  · exact cover_1120_1126 ⟨ha.1,hl⟩ hz
  · exact cover_1127_1134 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

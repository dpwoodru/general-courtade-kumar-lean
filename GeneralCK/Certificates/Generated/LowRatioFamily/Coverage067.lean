import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1072
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1073
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1074
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1075
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1076
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1077
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1078
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1079
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1080
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1081
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1082
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1083
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1084
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1085
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1086
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1087
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1072_1073 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (487 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((973 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1072 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1073 ⟨hr,ha.2⟩ hz
theorem cover_1074_1075 {a z : ℝ} (ha : a ∈ Set.Icc (487 / 500) (122 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 40):ℝ) with hl | hr
  · exact curvature_leaf_1074 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1075 ⟨hr,ha.2⟩ hz
theorem cover_1072_1075 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (122 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 500):ℝ) with hl | hr
  · exact cover_1072_1073 ⟨ha.1,hl⟩ hz
  · exact cover_1074_1075 ⟨hr,ha.2⟩ hz
theorem cover_1076_1077 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 125) (489 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((977 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1076 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1077 ⟨hr,ha.2⟩ hz
theorem cover_1078_1079 {a z : ℝ} (ha : a ∈ Set.Icc (489 / 500) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((979 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1078 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1079 ⟨hr,ha.2⟩ hz
theorem cover_1076_1079 {a z : ℝ} (ha : a ∈ Set.Icc (122 / 125) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 500):ℝ) with hl | hr
  · exact cover_1076_1077 ⟨ha.1,hl⟩ hz
  · exact cover_1078_1079 ⟨hr,ha.2⟩ hz
theorem cover_1072_1079 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (49 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((122 / 125):ℝ) with hl | hr
  · exact cover_1072_1075 ⟨ha.1,hl⟩ hz
  · exact cover_1076_1079 ⟨hr,ha.2⟩ hz
theorem cover_1080_1081 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (491 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((981 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1080 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1081 ⟨hr,ha.2⟩ hz
theorem cover_1082_1083 {a z : ℝ} (ha : a ∈ Set.Icc (491 / 500) (123 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((983 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1082 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1083 ⟨hr,ha.2⟩ hz
theorem cover_1080_1083 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (123 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 500):ℝ) with hl | hr
  · exact cover_1080_1081 ⟨ha.1,hl⟩ hz
  · exact cover_1082_1083 ⟨hr,ha.2⟩ hz
theorem cover_1084_1085 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 125) (493 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1084 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1085 ⟨hr,ha.2⟩ hz
theorem cover_1086_1087 {a z : ℝ} (ha : a ∈ Set.Icc (493 / 500) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((987 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1086 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1087 ⟨hr,ha.2⟩ hz
theorem cover_1084_1087 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 125) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 500):ℝ) with hl | hr
  · exact cover_1084_1085 ⟨ha.1,hl⟩ hz
  · exact cover_1086_1087 ⟨hr,ha.2⟩ hz
theorem cover_1080_1087 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 50) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 125):ℝ) with hl | hr
  · exact cover_1080_1083 ⟨ha.1,hl⟩ hz
  · exact cover_1084_1087 ⟨hr,ha.2⟩ hz
theorem cover_1072_1087 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 250) (247 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 50):ℝ) with hl | hr
  · exact cover_1072_1079 ⟨ha.1,hl⟩ hz
  · exact cover_1080_1087 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

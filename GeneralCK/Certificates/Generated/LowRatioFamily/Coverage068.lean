import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1088
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1089
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1090
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1091
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1092
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1093
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1094
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1095
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1096
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1097
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1098
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1099
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1100
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1101
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1102
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1103
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1088_1089 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (99 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((989 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1088 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1089 ⟨hr,ha.2⟩ hz
theorem cover_1090_1091 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 100) (619 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4951 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1090 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1091 ⟨hr,ha.2⟩ hz
theorem cover_1088_1091 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (619 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 100):ℝ) with hl | hr
  · exact cover_1088_1089 ⟨ha.1,hl⟩ hz
  · exact cover_1090_1091 ⟨hr,ha.2⟩ hz
theorem cover_1092_1093 {a z : ℝ} (ha : a ∈ Set.Icc (619 / 625) (2477 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4953 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1092 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1093 ⟨hr,ha.2⟩ hz
theorem cover_1094_1095 {a z : ℝ} (ha : a ∈ Set.Icc (2477 / 2500) (1239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((991 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1094 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1095 ⟨hr,ha.2⟩ hz
theorem cover_1092_1095 {a z : ℝ} (ha : a ∈ Set.Icc (619 / 625) (1239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2477 / 2500):ℝ) with hl | hr
  · exact cover_1092_1093 ⟨ha.1,hl⟩ hz
  · exact cover_1094_1095 ⟨hr,ha.2⟩ hz
theorem cover_1088_1095 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (1239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((619 / 625):ℝ) with hl | hr
  · exact cover_1088_1091 ⟨ha.1,hl⟩ hz
  · exact cover_1092_1095 ⟨hr,ha.2⟩ hz
theorem cover_1096_1097 {a z : ℝ} (ha : a ∈ Set.Icc (1239 / 1250) (2479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4957 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1096 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1097 ⟨hr,ha.2⟩ hz
theorem cover_1098_1099 {a z : ℝ} (ha : a ∈ Set.Icc (2479 / 2500) (124 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4959 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1098 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1099 ⟨hr,ha.2⟩ hz
theorem cover_1096_1099 {a z : ℝ} (ha : a ∈ Set.Icc (1239 / 1250) (124 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2479 / 2500):ℝ) with hl | hr
  · exact cover_1096_1097 ⟨ha.1,hl⟩ hz
  · exact cover_1098_1099 ⟨hr,ha.2⟩ hz
theorem cover_1100_1101 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 125) (2481 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4961 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1100 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1101 ⟨hr,ha.2⟩ hz
theorem cover_1102_1103 {a z : ℝ} (ha : a ∈ Set.Icc (2481 / 2500) (1241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4963 / 5000):ℝ) with hl | hr
  · exact curvature_leaf_1102 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1103 ⟨hr,ha.2⟩ hz
theorem cover_1100_1103 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 125) (1241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((2481 / 2500):ℝ) with hl | hr
  · exact cover_1100_1101 ⟨ha.1,hl⟩ hz
  · exact cover_1102_1103 ⟨hr,ha.2⟩ hz
theorem cover_1096_1103 {a z : ℝ} (ha : a ∈ Set.Icc (1239 / 1250) (1241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((124 / 125):ℝ) with hl | hr
  · exact cover_1096_1099 ⟨ha.1,hl⟩ hz
  · exact cover_1100_1103 ⟨hr,ha.2⟩ hz
theorem cover_1088_1103 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 250) (1241 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1239 / 1250):ℝ) with hl | hr
  · exact cover_1088_1095 ⟨ha.1,hl⟩ hz
  · exact cover_1096_1103 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

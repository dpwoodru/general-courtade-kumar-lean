import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1056
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1057
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1058
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1059
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1060
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1061
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1062
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1063
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1064
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1065
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1066
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1067
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1068
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1069
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1070
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1071
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1056_1057 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (479 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((957 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1056 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1057 ⟨hr,ha.2⟩ hz
theorem cover_1058_1059 {a z : ℝ} (ha : a ∈ Set.Icc (479 / 500) (24 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((959 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1058 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1059 ⟨hr,ha.2⟩ hz
theorem cover_1056_1059 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (24 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 500):ℝ) with hl | hr
  · exact cover_1056_1057 ⟨ha.1,hl⟩ hz
  · exact cover_1058_1059 ⟨hr,ha.2⟩ hz
theorem cover_1060_1061 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 25) (481 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((961 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1060 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1061 ⟨hr,ha.2⟩ hz
theorem cover_1062_1063 {a z : ℝ} (ha : a ∈ Set.Icc (481 / 500) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((963 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1062 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1063 ⟨hr,ha.2⟩ hz
theorem cover_1060_1063 {a z : ℝ} (ha : a ∈ Set.Icc (24 / 25) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 500):ℝ) with hl | hr
  · exact cover_1060_1061 ⟨ha.1,hl⟩ hz
  · exact cover_1062_1063 ⟨hr,ha.2⟩ hz
theorem cover_1056_1063 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (241 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((24 / 25):ℝ) with hl | hr
  · exact cover_1056_1059 ⟨ha.1,hl⟩ hz
  · exact cover_1060_1063 ⟨hr,ha.2⟩ hz
theorem cover_1064_1065 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (483 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((193 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1064 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1065 ⟨hr,ha.2⟩ hz
theorem cover_1066_1067 {a z : ℝ} (ha : a ∈ Set.Icc (483 / 500) (121 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((967 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1066 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1067 ⟨hr,ha.2⟩ hz
theorem cover_1064_1067 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (121 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 500):ℝ) with hl | hr
  · exact cover_1064_1065 ⟨ha.1,hl⟩ hz
  · exact cover_1066_1067 ⟨hr,ha.2⟩ hz
theorem cover_1068_1069 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 125) (97 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((969 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1068 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1069 ⟨hr,ha.2⟩ hz
theorem cover_1070_1071 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 100) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((971 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1070 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1071 ⟨hr,ha.2⟩ hz
theorem cover_1068_1071 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 125) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 100):ℝ) with hl | hr
  · exact cover_1068_1069 ⟨ha.1,hl⟩ hz
  · exact cover_1070_1071 ⟨hr,ha.2⟩ hz
theorem cover_1064_1071 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 250) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 125):ℝ) with hl | hr
  · exact cover_1064_1067 ⟨ha.1,hl⟩ hz
  · exact cover_1068_1071 ⟨hr,ha.2⟩ hz
theorem cover_1056_1071 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 250) (243 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 250):ℝ) with hl | hr
  · exact cover_1056_1063 ⟨ha.1,hl⟩ hz
  · exact cover_1064_1071 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

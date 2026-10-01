import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1040
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1041
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1042
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1043
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1044
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1045
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1046
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1047
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1048
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1049
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1050
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1051
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1052
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1053
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1054
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1055
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1040_1041 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 25) (463 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((923 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1040 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1041 ⟨hr,ha.2⟩ hz
theorem cover_1042_1043 {a z : ℝ} (ha : a ∈ Set.Icc (463 / 500) (233 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((929 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1042 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1043 ⟨hr,ha.2⟩ hz
theorem cover_1040_1043 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 25) (233 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 500):ℝ) with hl | hr
  · exact cover_1040_1041 ⟨ha.1,hl⟩ hz
  · exact cover_1042_1043 ⟨hr,ha.2⟩ hz
theorem cover_1044_1045 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 250) (469 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((187 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1044 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1045 ⟨hr,ha.2⟩ hz
theorem cover_1046_1047 {a z : ℝ} (ha : a ∈ Set.Icc (469 / 500) (118 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((941 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1046 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1047 ⟨hr,ha.2⟩ hz
theorem cover_1044_1047 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 250) (118 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 500):ℝ) with hl | hr
  · exact cover_1044_1045 ⟨ha.1,hl⟩ hz
  · exact cover_1046_1047 ⟨hr,ha.2⟩ hz
theorem cover_1040_1047 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 25) (118 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 250):ℝ) with hl | hr
  · exact cover_1040_1043 ⟨ha.1,hl⟩ hz
  · exact cover_1044_1047 ⟨hr,ha.2⟩ hz
theorem cover_1048_1049 {a z : ℝ} (ha : a ∈ Set.Icc (118 / 125) (19 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((947 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1048 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1049 ⟨hr,ha.2⟩ hz
theorem cover_1050_1051 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 20) (119 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((951 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1050 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1051 ⟨hr,ha.2⟩ hz
theorem cover_1048_1051 {a z : ℝ} (ha : a ∈ Set.Icc (118 / 125) (119 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 20):ℝ) with hl | hr
  · exact cover_1048_1049 ⟨ha.1,hl⟩ hz
  · exact cover_1050_1051 ⟨hr,ha.2⟩ hz
theorem cover_1052_1053 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 125) (477 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((953 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1052 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1053 ⟨hr,ha.2⟩ hz
theorem cover_1054_1055 {a z : ℝ} (ha : a ∈ Set.Icc (477 / 500) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1054 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1055 ⟨hr,ha.2⟩ hz
theorem cover_1052_1055 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 125) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 500):ℝ) with hl | hr
  · exact cover_1052_1053 ⟨ha.1,hl⟩ hz
  · exact cover_1054_1055 ⟨hr,ha.2⟩ hz
theorem cover_1048_1055 {a z : ℝ} (ha : a ∈ Set.Icc (118 / 125) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 125):ℝ) with hl | hr
  · exact cover_1048_1051 ⟨ha.1,hl⟩ hz
  · exact cover_1052_1055 ⟨hr,ha.2⟩ hz
theorem cover_1040_1055 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 25) (239 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((118 / 125):ℝ) with hl | hr
  · exact cover_1040_1047 ⟨ha.1,hl⟩ hz
  · exact cover_1048_1055 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

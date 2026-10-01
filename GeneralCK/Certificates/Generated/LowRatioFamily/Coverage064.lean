import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1024
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1025
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1026
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1027
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1028
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1029
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1030
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1031
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1032
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1033
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1034
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1035
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1036
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1037
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1038
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1039
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1024_1025 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (439 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 8):ℝ) with hl | hr
  · exact curvature_leaf_1024 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1025 ⟨hr,ha.2⟩ hz
theorem cover_1026_1027 {a z : ℝ} (ha : a ∈ Set.Icc (439 / 500) (221 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((881 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1026 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1027 ⟨hr,ha.2⟩ hz
theorem cover_1024_1027 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (221 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 500):ℝ) with hl | hr
  · exact cover_1024_1025 ⟨ha.1,hl⟩ hz
  · exact cover_1026_1027 ⟨hr,ha.2⟩ hz
theorem cover_1028_1029 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 250) (89 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((887 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1028 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1029 ⟨hr,ha.2⟩ hz
theorem cover_1030_1031 {a z : ℝ} (ha : a ∈ Set.Icc (89 / 100) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((893 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1030 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1031 ⟨hr,ha.2⟩ hz
theorem cover_1028_1031 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 250) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 100):ℝ) with hl | hr
  · exact cover_1028_1029 ⟨ha.1,hl⟩ hz
  · exact cover_1030_1031 ⟨hr,ha.2⟩ hz
theorem cover_1024_1031 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (112 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 250):ℝ) with hl | hr
  · exact cover_1024_1027 ⟨ha.1,hl⟩ hz
  · exact cover_1028_1031 ⟨hr,ha.2⟩ hz
theorem cover_1032_1033 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (451 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((899 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1032 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1033 ⟨hr,ha.2⟩ hz
theorem cover_1034_1035 {a z : ℝ} (ha : a ∈ Set.Icc (451 / 500) (227 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((181 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1034 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1035 ⟨hr,ha.2⟩ hz
theorem cover_1032_1035 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (227 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 500):ℝ) with hl | hr
  · exact cover_1032_1033 ⟨ha.1,hl⟩ hz
  · exact cover_1034_1035 ⟨hr,ha.2⟩ hz
theorem cover_1036_1037 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 250) (457 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((911 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1036 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1037 ⟨hr,ha.2⟩ hz
theorem cover_1038_1039 {a z : ℝ} (ha : a ∈ Set.Icc (457 / 500) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((917 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1038 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1039 ⟨hr,ha.2⟩ hz
theorem cover_1036_1039 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 250) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 500):ℝ) with hl | hr
  · exact cover_1036_1037 ⟨ha.1,hl⟩ hz
  · exact cover_1038_1039 ⟨hr,ha.2⟩ hz
theorem cover_1032_1039 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 125) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 250):ℝ) with hl | hr
  · exact cover_1032_1035 ⟨ha.1,hl⟩ hz
  · exact cover_1036_1039 ⟨hr,ha.2⟩ hz
theorem cover_1024_1039 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 125) (23 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((112 / 125):ℝ) with hl | hr
  · exact cover_1024_1031 ⟨ha.1,hl⟩ hz
  · exact cover_1032_1039 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

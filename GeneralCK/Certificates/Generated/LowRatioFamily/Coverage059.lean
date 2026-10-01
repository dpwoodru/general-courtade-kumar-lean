import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0944
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0945
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0946
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0947
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0948
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0949
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0950
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0951
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0952
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0953
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0954
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0955
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0956
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0957
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0958
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0959
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_944_945 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (319 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((127 / 200):ℝ) with hl | hr
  · exact curvature_leaf_944 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_945 ⟨hr,ha.2⟩ hz
theorem cover_946_947 {a z : ℝ} (ha : a ∈ Set.Icc (319 / 500) (161 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((641 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_946 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_947 ⟨hr,ha.2⟩ hz
theorem cover_944_947 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (161 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((319 / 500):ℝ) with hl | hr
  · exact cover_944_945 ⟨ha.1,hl⟩ hz
  · exact cover_946_947 ⟨hr,ha.2⟩ hz
theorem cover_948_949 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 250) (13 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((647 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_948 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_949 ⟨hr,ha.2⟩ hz
theorem cover_950_951 {a z : ℝ} (ha : a ∈ Set.Icc (13 / 20) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((653 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_950 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_951 ⟨hr,ha.2⟩ hz
theorem cover_948_951 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 250) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 20):ℝ) with hl | hr
  · exact cover_948_949 ⟨ha.1,hl⟩ hz
  · exact cover_950_951 ⟨hr,ha.2⟩ hz
theorem cover_944_951 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (82 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((161 / 250):ℝ) with hl | hr
  · exact cover_944_947 ⟨ha.1,hl⟩ hz
  · exact cover_948_951 ⟨hr,ha.2⟩ hz
theorem cover_952_953 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (331 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((659 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_952 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_953 ⟨hr,ha.2⟩ hz
theorem cover_954_955 {a z : ℝ} (ha : a ∈ Set.Icc (331 / 500) (167 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((133 / 200):ℝ) with hl | hr
  · exact curvature_leaf_954 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_955 ⟨hr,ha.2⟩ hz
theorem cover_952_955 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (167 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((331 / 500):ℝ) with hl | hr
  · exact cover_952_953 ⟨ha.1,hl⟩ hz
  · exact cover_954_955 ⟨hr,ha.2⟩ hz
theorem cover_956_957 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 250) (337 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((671 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_956 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_957 ⟨hr,ha.2⟩ hz
theorem cover_958_959 {a z : ℝ} (ha : a ∈ Set.Icc (337 / 500) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((677 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_958 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_959 ⟨hr,ha.2⟩ hz
theorem cover_956_959 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 250) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((337 / 500):ℝ) with hl | hr
  · exact cover_956_957 ⟨ha.1,hl⟩ hz
  · exact cover_958_959 ⟨hr,ha.2⟩ hz
theorem cover_952_959 {a z : ℝ} (ha : a ∈ Set.Icc (82 / 125) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((167 / 250):ℝ) with hl | hr
  · exact cover_952_955 ⟨ha.1,hl⟩ hz
  · exact cover_956_959 ⟨hr,ha.2⟩ hz
theorem cover_944_959 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 125) (17 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((82 / 125):ℝ) with hl | hr
  · exact cover_944_951 ⟨ha.1,hl⟩ hz
  · exact cover_952_959 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

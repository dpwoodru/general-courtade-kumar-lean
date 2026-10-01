import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0896
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0897
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0898
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0899
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0900
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0901
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0902
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0903
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0904
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0905
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0906
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0907
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0908
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0909
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0910
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0911
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_896_897 {a z : ℝ} (ha : a ∈ Set.Icc (62 / 125) (249 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_896 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_897 ⟨hr,ha.2⟩ hz
theorem cover_898_899 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 500) (1 / 2))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((499 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_898 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_899 ⟨hr,ha.2⟩ hz
theorem cover_896_899 {a z : ℝ} (ha : a ∈ Set.Icc (62 / 125) (1 / 2))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 500):ℝ) with hl | hr
  · exact cover_896_897 ⟨ha.1,hl⟩ hz
  · exact cover_898_899 ⟨hr,ha.2⟩ hz
theorem cover_900_901 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 2) (253 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((503 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_900 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_901 ⟨hr,ha.2⟩ hz
theorem cover_902_903 {a z : ℝ} (ha : a ∈ Set.Icc (253 / 500) (64 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((509 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_902 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_903 ⟨hr,ha.2⟩ hz
theorem cover_900_903 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 2) (64 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((253 / 500):ℝ) with hl | hr
  · exact cover_900_901 ⟨ha.1,hl⟩ hz
  · exact cover_902_903 ⟨hr,ha.2⟩ hz
theorem cover_896_903 {a z : ℝ} (ha : a ∈ Set.Icc (62 / 125) (64 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1 / 2):ℝ) with hl | hr
  · exact cover_896_899 ⟨ha.1,hl⟩ hz
  · exact cover_900_903 ⟨hr,ha.2⟩ hz
theorem cover_904_905 {a z : ℝ} (ha : a ∈ Set.Icc (64 / 125) (259 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((103 / 200):ℝ) with hl | hr
  · exact curvature_leaf_904 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_905 ⟨hr,ha.2⟩ hz
theorem cover_906_907 {a z : ℝ} (ha : a ∈ Set.Icc (259 / 500) (131 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((521 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_906 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_907 ⟨hr,ha.2⟩ hz
theorem cover_904_907 {a z : ℝ} (ha : a ∈ Set.Icc (64 / 125) (131 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((259 / 500):ℝ) with hl | hr
  · exact cover_904_905 ⟨ha.1,hl⟩ hz
  · exact cover_906_907 ⟨hr,ha.2⟩ hz
theorem cover_908_909 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 250) (53 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((527 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_908 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_909 ⟨hr,ha.2⟩ hz
theorem cover_910_911 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 100) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((533 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_910 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_911 ⟨hr,ha.2⟩ hz
theorem cover_908_911 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 250) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((53 / 100):ℝ) with hl | hr
  · exact cover_908_909 ⟨ha.1,hl⟩ hz
  · exact cover_910_911 ⟨hr,ha.2⟩ hz
theorem cover_904_911 {a z : ℝ} (ha : a ∈ Set.Icc (64 / 125) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((131 / 250):ℝ) with hl | hr
  · exact cover_904_907 ⟨ha.1,hl⟩ hz
  · exact cover_908_911 ⟨hr,ha.2⟩ hz
theorem cover_896_911 {a z : ℝ} (ha : a ∈ Set.Icc (62 / 125) (67 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((64 / 125):ℝ) with hl | hr
  · exact cover_896_903 ⟨ha.1,hl⟩ hz
  · exact cover_904_911 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

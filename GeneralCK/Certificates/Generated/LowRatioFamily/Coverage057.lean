import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0912
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0913
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0914
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0915
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0916
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0917
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0918
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0919
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0920
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0921
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0922
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0923
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0924
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0925
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0926
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0927
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_912_913 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (271 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((539 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_912 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_913 ⟨hr,ha.2⟩ hz
theorem cover_914_915 {a z : ℝ} (ha : a ∈ Set.Icc (271 / 500) (137 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 200):ℝ) with hl | hr
  · exact curvature_leaf_914 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_915 ⟨hr,ha.2⟩ hz
theorem cover_912_915 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (137 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((271 / 500):ℝ) with hl | hr
  · exact cover_912_913 ⟨ha.1,hl⟩ hz
  · exact cover_914_915 ⟨hr,ha.2⟩ hz
theorem cover_916_917 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 250) (277 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((551 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_916 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_917 ⟨hr,ha.2⟩ hz
theorem cover_918_919 {a z : ℝ} (ha : a ∈ Set.Icc (277 / 500) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((557 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_918 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_919 ⟨hr,ha.2⟩ hz
theorem cover_916_919 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 250) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((277 / 500):ℝ) with hl | hr
  · exact cover_916_917 ⟨ha.1,hl⟩ hz
  · exact cover_918_919 ⟨hr,ha.2⟩ hz
theorem cover_912_919 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (14 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((137 / 250):ℝ) with hl | hr
  · exact cover_912_915 ⟨ha.1,hl⟩ hz
  · exact cover_916_919 ⟨hr,ha.2⟩ hz
theorem cover_920_921 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (283 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((563 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_920 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_921 ⟨hr,ha.2⟩ hz
theorem cover_922_923 {a z : ℝ} (ha : a ∈ Set.Icc (283 / 500) (143 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((569 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_922 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_923 ⟨hr,ha.2⟩ hz
theorem cover_920_923 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (143 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((283 / 500):ℝ) with hl | hr
  · exact cover_920_921 ⟨ha.1,hl⟩ hz
  · exact cover_922_923 ⟨hr,ha.2⟩ hz
theorem cover_924_925 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 250) (289 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 40):ℝ) with hl | hr
  · exact curvature_leaf_924 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_925 ⟨hr,ha.2⟩ hz
theorem cover_926_927 {a z : ℝ} (ha : a ∈ Set.Icc (289 / 500) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((581 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_926 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_927 ⟨hr,ha.2⟩ hz
theorem cover_924_927 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 250) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((289 / 500):ℝ) with hl | hr
  · exact cover_924_925 ⟨ha.1,hl⟩ hz
  · exact cover_926_927 ⟨hr,ha.2⟩ hz
theorem cover_920_927 {a z : ℝ} (ha : a ∈ Set.Icc (14 / 25) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((143 / 250):ℝ) with hl | hr
  · exact cover_920_923 ⟨ha.1,hl⟩ hz
  · exact cover_924_927 ⟨hr,ha.2⟩ hz
theorem cover_912_927 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 125) (73 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((14 / 25):ℝ) with hl | hr
  · exact cover_912_919 ⟨ha.1,hl⟩ hz
  · exact cover_920_927 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0960
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0961
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0962
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0963
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0964
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0965
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0966
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0967
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0968
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0969
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0970
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0971
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0972
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0973
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0974
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0975
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_960_961 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (343 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((683 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_960 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_961 ⟨hr,ha.2⟩ hz
theorem cover_962_963 {a z : ℝ} (ha : a ∈ Set.Icc (343 / 500) (173 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((689 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_962 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_963 ⟨hr,ha.2⟩ hz
theorem cover_960_963 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (173 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((343 / 500):ℝ) with hl | hr
  · exact cover_960_961 ⟨ha.1,hl⟩ hz
  · exact cover_962_963 ⟨hr,ha.2⟩ hz
theorem cover_964_965 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 250) (349 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((139 / 200):ℝ) with hl | hr
  · exact curvature_leaf_964 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_965 ⟨hr,ha.2⟩ hz
theorem cover_966_967 {a z : ℝ} (ha : a ∈ Set.Icc (349 / 500) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((701 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_966 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_967 ⟨hr,ha.2⟩ hz
theorem cover_964_967 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 250) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((349 / 500):ℝ) with hl | hr
  · exact cover_964_965 ⟨ha.1,hl⟩ hz
  · exact cover_966_967 ⟨hr,ha.2⟩ hz
theorem cover_960_967 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (88 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((173 / 250):ℝ) with hl | hr
  · exact cover_960_963 ⟨ha.1,hl⟩ hz
  · exact cover_964_967 ⟨hr,ha.2⟩ hz
theorem cover_968_969 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (71 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((707 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_968 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_969 ⟨hr,ha.2⟩ hz
theorem cover_970_971 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 100) (179 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((713 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_970 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_971 ⟨hr,ha.2⟩ hz
theorem cover_968_971 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (179 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 100):ℝ) with hl | hr
  · exact cover_968_969 ⟨ha.1,hl⟩ hz
  · exact cover_970_971 ⟨hr,ha.2⟩ hz
theorem cover_972_973 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 250) (361 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((719 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_972 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_973 ⟨hr,ha.2⟩ hz
theorem cover_974_975 {a z : ℝ} (ha : a ∈ Set.Icc (361 / 500) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 40):ℝ) with hl | hr
  · exact curvature_leaf_974 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_975 ⟨hr,ha.2⟩ hz
theorem cover_972_975 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 250) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((361 / 500):ℝ) with hl | hr
  · exact cover_972_973 ⟨ha.1,hl⟩ hz
  · exact cover_974_975 ⟨hr,ha.2⟩ hz
theorem cover_968_975 {a z : ℝ} (ha : a ∈ Set.Icc (88 / 125) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 250):ℝ) with hl | hr
  · exact cover_968_971 ⟨ha.1,hl⟩ hz
  · exact cover_972_975 ⟨hr,ha.2⟩ hz
theorem cover_960_975 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 25) (91 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((88 / 125):ℝ) with hl | hr
  · exact cover_960_967 ⟨ha.1,hl⟩ hz
  · exact cover_968_975 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

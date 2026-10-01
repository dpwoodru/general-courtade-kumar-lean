import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0992
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0993
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0994
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0995
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0996
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0997
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0998
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0999
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1000
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1001
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1002
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1003
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1004
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1005
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1006
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1007
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_992_993 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (391 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((779 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_992 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_993 ⟨hr,ha.2⟩ hz
theorem cover_994_995 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 500) (197 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((157 / 200):ℝ) with hl | hr
  · exact curvature_leaf_994 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_995 ⟨hr,ha.2⟩ hz
theorem cover_992_995 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (197 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((391 / 500):ℝ) with hl | hr
  · exact cover_992_993 ⟨ha.1,hl⟩ hz
  · exact cover_994_995 ⟨hr,ha.2⟩ hz
theorem cover_996_997 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 250) (397 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((791 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_996 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_997 ⟨hr,ha.2⟩ hz
theorem cover_998_999 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 500) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((797 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_998 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_999 ⟨hr,ha.2⟩ hz
theorem cover_996_999 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 250) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 500):ℝ) with hl | hr
  · exact cover_996_997 ⟨ha.1,hl⟩ hz
  · exact cover_998_999 ⟨hr,ha.2⟩ hz
theorem cover_992_999 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (4 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 250):ℝ) with hl | hr
  · exact cover_992_995 ⟨ha.1,hl⟩ hz
  · exact cover_996_999 ⟨hr,ha.2⟩ hz
theorem cover_1000_1001 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (403 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((803 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1000 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1001 ⟨hr,ha.2⟩ hz
theorem cover_1002_1003 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 500) (203 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((809 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1002 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1003 ⟨hr,ha.2⟩ hz
theorem cover_1000_1003 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (203 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 500):ℝ) with hl | hr
  · exact cover_1000_1001 ⟨ha.1,hl⟩ hz
  · exact cover_1002_1003 ⟨hr,ha.2⟩ hz
theorem cover_1004_1005 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 250) (409 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((163 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1004 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1005 ⟨hr,ha.2⟩ hz
theorem cover_1006_1007 {a z : ℝ} (ha : a ∈ Set.Icc (409 / 500) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((821 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1006 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1007 ⟨hr,ha.2⟩ hz
theorem cover_1004_1007 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 250) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 500):ℝ) with hl | hr
  · exact cover_1004_1005 ⟨ha.1,hl⟩ hz
  · exact cover_1006_1007 ⟨hr,ha.2⟩ hz
theorem cover_1000_1007 {a z : ℝ} (ha : a ∈ Set.Icc (4 / 5) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 250):ℝ) with hl | hr
  · exact cover_1000_1003 ⟨ha.1,hl⟩ hz
  · exact cover_1004_1007 ⟨hr,ha.2⟩ hz
theorem cover_992_1007 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 125) (103 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((4 / 5):ℝ) with hl | hr
  · exact cover_992_999 ⟨ha.1,hl⟩ hz
  · exact cover_1000_1007 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

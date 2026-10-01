import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0976
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0977
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0978
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0979
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0980
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0981
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0982
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0983
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0984
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0985
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0986
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0987
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0988
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0989
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0990
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0991
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_976_977 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (367 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((731 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_976 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_977 ⟨hr,ha.2⟩ hz
theorem cover_978_979 {a z : ℝ} (ha : a ∈ Set.Icc (367 / 500) (37 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((737 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_978 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_979 ⟨hr,ha.2⟩ hz
theorem cover_976_979 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (37 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((367 / 500):ℝ) with hl | hr
  · exact cover_976_977 ⟨ha.1,hl⟩ hz
  · exact cover_978_979 ⟨hr,ha.2⟩ hz
theorem cover_980_981 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 50) (373 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((743 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_980 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_981 ⟨hr,ha.2⟩ hz
theorem cover_982_983 {a z : ℝ} (ha : a ∈ Set.Icc (373 / 500) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((749 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_982 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_983 ⟨hr,ha.2⟩ hz
theorem cover_980_983 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 50) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((373 / 500):ℝ) with hl | hr
  · exact cover_980_981 ⟨ha.1,hl⟩ hz
  · exact cover_982_983 ⟨hr,ha.2⟩ hz
theorem cover_976_983 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (94 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 50):ℝ) with hl | hr
  · exact cover_976_979 ⟨ha.1,hl⟩ hz
  · exact cover_980_983 ⟨hr,ha.2⟩ hz
theorem cover_984_985 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (379 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((151 / 200):ℝ) with hl | hr
  · exact curvature_leaf_984 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_985 ⟨hr,ha.2⟩ hz
theorem cover_986_987 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 500) (191 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((761 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_986 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_987 ⟨hr,ha.2⟩ hz
theorem cover_984_987 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (191 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 500):ℝ) with hl | hr
  · exact cover_984_985 ⟨ha.1,hl⟩ hz
  · exact cover_986_987 ⟨hr,ha.2⟩ hz
theorem cover_988_989 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 250) (77 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((767 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_988 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_989 ⟨hr,ha.2⟩ hz
theorem cover_990_991 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 100) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((773 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_990 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_991 ⟨hr,ha.2⟩ hz
theorem cover_988_991 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 250) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 100):ℝ) with hl | hr
  · exact cover_988_989 ⟨ha.1,hl⟩ hz
  · exact cover_990_991 ⟨hr,ha.2⟩ hz
theorem cover_984_991 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 250):ℝ) with hl | hr
  · exact cover_984_987 ⟨ha.1,hl⟩ hz
  · exact cover_988_991 ⟨hr,ha.2⟩ hz
theorem cover_976_991 {a z : ℝ} (ha : a ∈ Set.Icc (91 / 125) (97 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((94 / 125):ℝ) with hl | hr
  · exact cover_976_983 ⟨ha.1,hl⟩ hz
  · exact cover_984_991 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

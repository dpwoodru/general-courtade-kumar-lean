import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0864
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0865
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0866
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0867
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0868
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0869
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0870
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0871
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0872
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0873
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0874
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0875
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0876
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0877
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0878
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0879
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_864_865 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (233 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 200):ℝ) with hl | hr
  · exact curvature_leaf_864 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_865 ⟨hr,ha.2⟩ hz
theorem cover_866_867 {a z : ℝ} (ha : a ∈ Set.Icc (233 / 500) (117 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((467 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_866 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_867 ⟨hr,ha.2⟩ hz
theorem cover_864_867 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (117 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((233 / 500):ℝ) with hl | hr
  · exact cover_864_865 ⟨ha.1,hl⟩ hz
  · exact cover_866_867 ⟨hr,ha.2⟩ hz
theorem cover_868_869 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 250) (47 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((469 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_868 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_869 ⟨hr,ha.2⟩ hz
theorem cover_870_871 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 100) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((471 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_870 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_871 ⟨hr,ha.2⟩ hz
theorem cover_868_871 {a z : ℝ} (ha : a ∈ Set.Icc (117 / 250) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 100):ℝ) with hl | hr
  · exact cover_868_869 ⟨ha.1,hl⟩ hz
  · exact cover_870_871 ⟨hr,ha.2⟩ hz
theorem cover_864_871 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (59 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 250):ℝ) with hl | hr
  · exact cover_864_867 ⟨ha.1,hl⟩ hz
  · exact cover_868_871 ⟨hr,ha.2⟩ hz
theorem cover_872_873 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (237 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((473 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_872 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_873 ⟨hr,ha.2⟩ hz
theorem cover_874_875 {a z : ℝ} (ha : a ∈ Set.Icc (237 / 500) (119 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 40):ℝ) with hl | hr
  · exact curvature_leaf_874 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_875 ⟨hr,ha.2⟩ hz
theorem cover_872_875 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (119 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((237 / 500):ℝ) with hl | hr
  · exact cover_872_873 ⟨ha.1,hl⟩ hz
  · exact cover_874_875 ⟨hr,ha.2⟩ hz
theorem cover_876_877 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 250) (239 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_876 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_877 ⟨hr,ha.2⟩ hz
theorem cover_878_879 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 500) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_878 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_879 ⟨hr,ha.2⟩ hz
theorem cover_876_879 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 250) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 500):ℝ) with hl | hr
  · exact cover_876_877 ⟨ha.1,hl⟩ hz
  · exact cover_878_879 ⟨hr,ha.2⟩ hz
theorem cover_872_879 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 125) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 250):ℝ) with hl | hr
  · exact cover_872_875 ⟨ha.1,hl⟩ hz
  · exact cover_876_879 ⟨hr,ha.2⟩ hz
theorem cover_864_879 {a z : ℝ} (ha : a ∈ Set.Icc (58 / 125) (12 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 125):ℝ) with hl | hr
  · exact cover_864_871 ⟨ha.1,hl⟩ hz
  · exact cover_872_879 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

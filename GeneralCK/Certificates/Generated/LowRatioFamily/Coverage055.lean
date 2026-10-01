import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0880
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0881
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0882
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0883
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0884
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0885
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0886
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0887
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0888
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0889
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0890
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0891
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0892
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0893
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0894
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0895
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_880_881 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (241 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_880 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_881 ⟨hr,ha.2⟩ hz
theorem cover_882_883 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 500) (121 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_882 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_883 ⟨hr,ha.2⟩ hz
theorem cover_880_883 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (121 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 500):ℝ) with hl | hr
  · exact cover_880_881 ⟨ha.1,hl⟩ hz
  · exact cover_882_883 ⟨hr,ha.2⟩ hz
theorem cover_884_885 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 250) (243 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 200):ℝ) with hl | hr
  · exact curvature_leaf_884 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_885 ⟨hr,ha.2⟩ hz
theorem cover_886_887 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 500) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_886 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_887 ⟨hr,ha.2⟩ hz
theorem cover_884_887 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 250) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 500):ℝ) with hl | hr
  · exact cover_884_885 ⟨ha.1,hl⟩ hz
  · exact cover_886_887 ⟨hr,ha.2⟩ hz
theorem cover_880_887 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (61 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 250):ℝ) with hl | hr
  · exact cover_880_883 ⟨ha.1,hl⟩ hz
  · exact cover_884_887 ⟨hr,ha.2⟩ hz
theorem cover_888_889 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (49 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_888 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_889 ⟨hr,ha.2⟩ hz
theorem cover_890_891 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 100) (123 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_890 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_891 ⟨hr,ha.2⟩ hz
theorem cover_888_891 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (123 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 100):ℝ) with hl | hr
  · exact cover_888_889 ⟨ha.1,hl⟩ hz
  · exact cover_890_891 ⟨hr,ha.2⟩ hz
theorem cover_892_893 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 250) (247 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((493 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_892 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_893 ⟨hr,ha.2⟩ hz
theorem cover_894_895 {a z : ℝ} (ha : a ∈ Set.Icc (247 / 500) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 200):ℝ) with hl | hr
  · exact curvature_leaf_894 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_895 ⟨hr,ha.2⟩ hz
theorem cover_892_895 {a z : ℝ} (ha : a ∈ Set.Icc (123 / 250) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((247 / 500):ℝ) with hl | hr
  · exact cover_892_893 ⟨ha.1,hl⟩ hz
  · exact cover_894_895 ⟨hr,ha.2⟩ hz
theorem cover_888_895 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 125) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((123 / 250):ℝ) with hl | hr
  · exact cover_888_891 ⟨ha.1,hl⟩ hz
  · exact cover_892_895 ⟨hr,ha.2⟩ hz
theorem cover_880_895 {a z : ℝ} (ha : a ∈ Set.Icc (12 / 25) (62 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 125):ℝ) with hl | hr
  · exact cover_880_887 ⟨ha.1,hl⟩ hz
  · exact cover_888_895 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

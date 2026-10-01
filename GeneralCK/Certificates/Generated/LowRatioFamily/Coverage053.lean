import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0848
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0849
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0850
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0851
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0852
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0853
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0854
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0855
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0856
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0857
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0858
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0859
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0860
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0861
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0862
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0863
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_848_849 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (9 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_848 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_849 ⟨hr,ha.2⟩ hz
theorem cover_850_851 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 20) (113 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_850 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_851 ⟨hr,ha.2⟩ hz
theorem cover_848_851 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (113 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 20):ℝ) with hl | hr
  · exact cover_848_849 ⟨ha.1,hl⟩ hz
  · exact cover_850_851 ⟨hr,ha.2⟩ hz
theorem cover_852_853 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 250) (227 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((453 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_852 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_853 ⟨hr,ha.2⟩ hz
theorem cover_854_855 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 500) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 200):ℝ) with hl | hr
  · exact curvature_leaf_854 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_855 ⟨hr,ha.2⟩ hz
theorem cover_852_855 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 250) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 500):ℝ) with hl | hr
  · exact cover_852_853 ⟨ha.1,hl⟩ hz
  · exact cover_854_855 ⟨hr,ha.2⟩ hz
theorem cover_848_855 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (57 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 250):ℝ) with hl | hr
  · exact cover_848_851 ⟨ha.1,hl⟩ hz
  · exact cover_852_855 ⟨hr,ha.2⟩ hz
theorem cover_856_857 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (229 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_856 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_857 ⟨hr,ha.2⟩ hz
theorem cover_858_859 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 500) (23 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((459 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_858 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_859 ⟨hr,ha.2⟩ hz
theorem cover_856_859 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (23 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((229 / 500):ℝ) with hl | hr
  · exact cover_856_857 ⟨ha.1,hl⟩ hz
  · exact cover_858_859 ⟨hr,ha.2⟩ hz
theorem cover_860_861 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 50) (231 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((461 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_860 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_861 ⟨hr,ha.2⟩ hz
theorem cover_862_863 {a z : ℝ} (ha : a ∈ Set.Icc (231 / 500) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((463 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_862 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_863 ⟨hr,ha.2⟩ hz
theorem cover_860_863 {a z : ℝ} (ha : a ∈ Set.Icc (23 / 50) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((231 / 500):ℝ) with hl | hr
  · exact cover_860_861 ⟨ha.1,hl⟩ hz
  · exact cover_862_863 ⟨hr,ha.2⟩ hz
theorem cover_856_863 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 125) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 50):ℝ) with hl | hr
  · exact cover_856_859 ⟨ha.1,hl⟩ hz
  · exact cover_860_863 ⟨hr,ha.2⟩ hz
theorem cover_848_863 {a z : ℝ} (ha : a ∈ Set.Icc (56 / 125) (58 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 125):ℝ) with hl | hr
  · exact cover_848_855 ⟨ha.1,hl⟩ hz
  · exact cover_856_863 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

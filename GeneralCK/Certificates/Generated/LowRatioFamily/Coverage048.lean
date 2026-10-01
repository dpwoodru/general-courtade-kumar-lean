import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0768
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0769
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0770
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0771
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0772
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0773
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0774
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0775
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0776
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0777
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0778
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0779
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0780
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0781
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0782
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0783
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_768_769 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (37 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((369 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_768 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_769 ⟨hr,ha.2⟩ hz
theorem cover_770_771 {a z : ℝ} (ha : a ∈ Set.Icc (37 / 100) (93 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((371 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_770 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_771 ⟨hr,ha.2⟩ hz
theorem cover_768_771 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (93 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((37 / 100):ℝ) with hl | hr
  · exact cover_768_769 ⟨ha.1,hl⟩ hz
  · exact cover_770_771 ⟨hr,ha.2⟩ hz
theorem cover_772_773 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 250) (187 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((373 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_772 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_773 ⟨hr,ha.2⟩ hz
theorem cover_774_775 {a z : ℝ} (ha : a ∈ Set.Icc (187 / 500) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((3 / 8):ℝ) with hl | hr
  · exact curvature_leaf_774 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_775 ⟨hr,ha.2⟩ hz
theorem cover_772_775 {a z : ℝ} (ha : a ∈ Set.Icc (93 / 250) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((187 / 500):ℝ) with hl | hr
  · exact cover_772_773 ⟨ha.1,hl⟩ hz
  · exact cover_774_775 ⟨hr,ha.2⟩ hz
theorem cover_768_775 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (47 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((93 / 250):ℝ) with hl | hr
  · exact cover_768_771 ⟨ha.1,hl⟩ hz
  · exact cover_772_775 ⟨hr,ha.2⟩ hz
theorem cover_776_777 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (189 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((377 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_776 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_777 ⟨hr,ha.2⟩ hz
theorem cover_778_779 {a z : ℝ} (ha : a ∈ Set.Icc (189 / 500) (19 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((379 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_778 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_779 ⟨hr,ha.2⟩ hz
theorem cover_776_779 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (19 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((189 / 500):ℝ) with hl | hr
  · exact cover_776_777 ⟨ha.1,hl⟩ hz
  · exact cover_778_779 ⟨hr,ha.2⟩ hz
theorem cover_780_781 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 50) (191 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((381 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_780 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_781 ⟨hr,ha.2⟩ hz
theorem cover_782_783 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 500) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((383 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_782 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_783 ⟨hr,ha.2⟩ hz
theorem cover_780_783 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 50) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 500):ℝ) with hl | hr
  · exact cover_780_781 ⟨ha.1,hl⟩ hz
  · exact cover_782_783 ⟨hr,ha.2⟩ hz
theorem cover_776_783 {a z : ℝ} (ha : a ∈ Set.Icc (47 / 125) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 50):ℝ) with hl | hr
  · exact cover_776_779 ⟨ha.1,hl⟩ hz
  · exact cover_780_783 ⟨hr,ha.2⟩ hz
theorem cover_768_783 {a z : ℝ} (ha : a ∈ Set.Icc (46 / 125) (48 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((47 / 125):ℝ) with hl | hr
  · exact cover_768_775 ⟨ha.1,hl⟩ hz
  · exact cover_776_783 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

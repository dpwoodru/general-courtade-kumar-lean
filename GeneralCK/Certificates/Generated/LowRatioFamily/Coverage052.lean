import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0832
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0833
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0834
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0835
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0836
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0837
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0838
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0839
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0840
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0841
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0842
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0843
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0844
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0845
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0846
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0847
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_832_833 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (217 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_832 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_833 ⟨hr,ha.2⟩ hz
theorem cover_834_835 {a z : ℝ} (ha : a ∈ Set.Icc (217 / 500) (109 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((87 / 200):ℝ) with hl | hr
  · exact curvature_leaf_834 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_835 ⟨hr,ha.2⟩ hz
theorem cover_832_835 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (109 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((217 / 500):ℝ) with hl | hr
  · exact cover_832_833 ⟨ha.1,hl⟩ hz
  · exact cover_834_835 ⟨hr,ha.2⟩ hz
theorem cover_836_837 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 250) (219 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((437 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_836 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_837 ⟨hr,ha.2⟩ hz
theorem cover_838_839 {a z : ℝ} (ha : a ∈ Set.Icc (219 / 500) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_838 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_839 ⟨hr,ha.2⟩ hz
theorem cover_836_839 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 250) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((219 / 500):ℝ) with hl | hr
  · exact cover_836_837 ⟨ha.1,hl⟩ hz
  · exact cover_838_839 ⟨hr,ha.2⟩ hz
theorem cover_832_839 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (11 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 250):ℝ) with hl | hr
  · exact cover_832_835 ⟨ha.1,hl⟩ hz
  · exact cover_836_839 ⟨hr,ha.2⟩ hz
theorem cover_840_841 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (221 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((441 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_840 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_841 ⟨hr,ha.2⟩ hz
theorem cover_842_843 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 500) (111 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((443 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_842 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_843 ⟨hr,ha.2⟩ hz
theorem cover_840_843 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (111 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 500):ℝ) with hl | hr
  · exact cover_840_841 ⟨ha.1,hl⟩ hz
  · exact cover_842_843 ⟨hr,ha.2⟩ hz
theorem cover_844_845 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 250) (223 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 200):ℝ) with hl | hr
  · exact curvature_leaf_844 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_845 ⟨hr,ha.2⟩ hz
theorem cover_846_847 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 500) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((447 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_846 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_847 ⟨hr,ha.2⟩ hz
theorem cover_844_847 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 250) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((223 / 500):ℝ) with hl | hr
  · exact cover_844_845 ⟨ha.1,hl⟩ hz
  · exact cover_846_847 ⟨hr,ha.2⟩ hz
theorem cover_840_847 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 25) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((111 / 250):ℝ) with hl | hr
  · exact cover_840_843 ⟨ha.1,hl⟩ hz
  · exact cover_844_847 ⟨hr,ha.2⟩ hz
theorem cover_832_847 {a z : ℝ} (ha : a ∈ Set.Icc (54 / 125) (56 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((11 / 25):ℝ) with hl | hr
  · exact cover_832_839 ⟨ha.1,hl⟩ hz
  · exact cover_840_847 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

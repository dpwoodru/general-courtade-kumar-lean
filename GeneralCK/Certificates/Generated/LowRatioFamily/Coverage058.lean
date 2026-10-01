import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0928
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0929
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0930
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0931
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0932
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0933
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0934
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0935
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0936
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0937
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0938
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0939
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0940
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0941
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0942
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0943
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_928_929 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (59 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((587 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_928 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_929 ⟨hr,ha.2⟩ hz
theorem cover_930_931 {a z : ℝ} (ha : a ∈ Set.Icc (59 / 100) (149 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((593 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_930 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_931 ⟨hr,ha.2⟩ hz
theorem cover_928_931 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (149 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((59 / 100):ℝ) with hl | hr
  · exact cover_928_929 ⟨ha.1,hl⟩ hz
  · exact cover_930_931 ⟨hr,ha.2⟩ hz
theorem cover_932_933 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 250) (301 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((599 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_932 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_933 ⟨hr,ha.2⟩ hz
theorem cover_934_935 {a z : ℝ} (ha : a ∈ Set.Icc (301 / 500) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 200):ℝ) with hl | hr
  · exact curvature_leaf_934 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_935 ⟨hr,ha.2⟩ hz
theorem cover_932_935 {a z : ℝ} (ha : a ∈ Set.Icc (149 / 250) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((301 / 500):ℝ) with hl | hr
  · exact cover_932_933 ⟨ha.1,hl⟩ hz
  · exact cover_934_935 ⟨hr,ha.2⟩ hz
theorem cover_928_935 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (76 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((149 / 250):ℝ) with hl | hr
  · exact cover_928_931 ⟨ha.1,hl⟩ hz
  · exact cover_932_935 ⟨hr,ha.2⟩ hz
theorem cover_936_937 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (307 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((611 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_936 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_937 ⟨hr,ha.2⟩ hz
theorem cover_938_939 {a z : ℝ} (ha : a ∈ Set.Icc (307 / 500) (31 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((617 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_938 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_939 ⟨hr,ha.2⟩ hz
theorem cover_936_939 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (31 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((307 / 500):ℝ) with hl | hr
  · exact cover_936_937 ⟨ha.1,hl⟩ hz
  · exact cover_938_939 ⟨hr,ha.2⟩ hz
theorem cover_940_941 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 50) (313 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((623 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_940 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_941 ⟨hr,ha.2⟩ hz
theorem cover_942_943 {a z : ℝ} (ha : a ∈ Set.Icc (313 / 500) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((629 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_942 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_943 ⟨hr,ha.2⟩ hz
theorem cover_940_943 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 50) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((313 / 500):ℝ) with hl | hr
  · exact cover_940_941 ⟨ha.1,hl⟩ hz
  · exact cover_942_943 ⟨hr,ha.2⟩ hz
theorem cover_936_943 {a z : ℝ} (ha : a ∈ Set.Icc (76 / 125) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 50):ℝ) with hl | hr
  · exact cover_936_939 ⟨ha.1,hl⟩ hz
  · exact cover_940_943 ⟨hr,ha.2⟩ hz
theorem cover_928_943 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 125) (79 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((76 / 125):ℝ) with hl | hr
  · exact cover_928_935 ⟨ha.1,hl⟩ hz
  · exact cover_936_943 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

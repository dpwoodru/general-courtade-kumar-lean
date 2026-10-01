import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0736
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0737
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0738
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0739
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0740
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0741
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0742
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0743
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0744
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0745
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0746
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0747
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0748
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0749
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0750
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0751
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_736_737 {a z : ℝ} (ha : a ∈ Set.Icc (42 / 125) (169 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((337 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_736 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_737 ⟨hr,ha.2⟩ hz
theorem cover_738_739 {a z : ℝ} (ha : a ∈ Set.Icc (169 / 500) (17 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((339 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_738 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_739 ⟨hr,ha.2⟩ hz
theorem cover_736_739 {a z : ℝ} (ha : a ∈ Set.Icc (42 / 125) (17 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((169 / 500):ℝ) with hl | hr
  · exact cover_736_737 ⟨ha.1,hl⟩ hz
  · exact cover_738_739 ⟨hr,ha.2⟩ hz
theorem cover_740_741 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 50) (171 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((341 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_740 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_741 ⟨hr,ha.2⟩ hz
theorem cover_742_743 {a z : ℝ} (ha : a ∈ Set.Icc (171 / 500) (43 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((343 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_742 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_743 ⟨hr,ha.2⟩ hz
theorem cover_740_743 {a z : ℝ} (ha : a ∈ Set.Icc (17 / 50) (43 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((171 / 500):ℝ) with hl | hr
  · exact cover_740_741 ⟨ha.1,hl⟩ hz
  · exact cover_742_743 ⟨hr,ha.2⟩ hz
theorem cover_736_743 {a z : ℝ} (ha : a ∈ Set.Icc (42 / 125) (43 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((17 / 50):ℝ) with hl | hr
  · exact cover_736_739 ⟨ha.1,hl⟩ hz
  · exact cover_740_743 ⟨hr,ha.2⟩ hz
theorem cover_744_745 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 125) (173 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((69 / 200):ℝ) with hl | hr
  · exact curvature_leaf_744 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_745 ⟨hr,ha.2⟩ hz
theorem cover_746_747 {a z : ℝ} (ha : a ∈ Set.Icc (173 / 500) (87 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((347 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_746 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_747 ⟨hr,ha.2⟩ hz
theorem cover_744_747 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 125) (87 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((173 / 500):ℝ) with hl | hr
  · exact cover_744_745 ⟨ha.1,hl⟩ hz
  · exact cover_746_747 ⟨hr,ha.2⟩ hz
theorem cover_748_749 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 250) (7 / 20))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((349 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_748 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_749 ⟨hr,ha.2⟩ hz
theorem cover_750_751 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 20) (44 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((351 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_750 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_751 ⟨hr,ha.2⟩ hz
theorem cover_748_751 {a z : ℝ} (ha : a ∈ Set.Icc (87 / 250) (44 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 20):ℝ) with hl | hr
  · exact cover_748_749 ⟨ha.1,hl⟩ hz
  · exact cover_750_751 ⟨hr,ha.2⟩ hz
theorem cover_744_751 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 125) (44 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((87 / 250):ℝ) with hl | hr
  · exact cover_744_747 ⟨ha.1,hl⟩ hz
  · exact cover_748_751 ⟨hr,ha.2⟩ hz
theorem cover_736_751 {a z : ℝ} (ha : a ∈ Set.Icc (42 / 125) (44 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 125):ℝ) with hl | hr
  · exact cover_736_743 ⟨ha.1,hl⟩ hz
  · exact cover_744_751 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

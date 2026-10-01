import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0640
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0641
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0642
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0643
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0644
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0645
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0646
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0647
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0648
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0649
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0650
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0651
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0652
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0653
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0654
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0655
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_640_641 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 100) (271 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((541 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_640 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_641 ⟨hr,ha.2⟩ hz
theorem cover_642_643 {a z : ℝ} (ha : a ∈ Set.Icc (271 / 1000) (34 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((543 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_642 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_643 ⟨hr,ha.2⟩ hz
theorem cover_640_643 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 100) (34 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((271 / 1000):ℝ) with hl | hr
  · exact cover_640_641 ⟨ha.1,hl⟩ hz
  · exact cover_642_643 ⟨hr,ha.2⟩ hz
theorem cover_644_645 {a z : ℝ} (ha : a ∈ Set.Icc (34 / 125) (273 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 400):ℝ) with hl | hr
  · exact curvature_leaf_644 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_645 ⟨hr,ha.2⟩ hz
theorem cover_646_647 {a z : ℝ} (ha : a ∈ Set.Icc (273 / 1000) (137 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((547 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_646 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_647 ⟨hr,ha.2⟩ hz
theorem cover_644_647 {a z : ℝ} (ha : a ∈ Set.Icc (34 / 125) (137 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((273 / 1000):ℝ) with hl | hr
  · exact cover_644_645 ⟨ha.1,hl⟩ hz
  · exact cover_646_647 ⟨hr,ha.2⟩ hz
theorem cover_640_647 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 100) (137 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((34 / 125):ℝ) with hl | hr
  · exact cover_640_643 ⟨ha.1,hl⟩ hz
  · exact cover_644_647 ⟨hr,ha.2⟩ hz
theorem cover_648_649 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 500) (11 / 40))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((549 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_648 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_649 ⟨hr,ha.2⟩ hz
theorem cover_650_651 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 40) (69 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((551 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_650 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_651 ⟨hr,ha.2⟩ hz
theorem cover_648_651 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 500) (69 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((11 / 40):ℝ) with hl | hr
  · exact cover_648_649 ⟨ha.1,hl⟩ hz
  · exact cover_650_651 ⟨hr,ha.2⟩ hz
theorem cover_652_653 {a z : ℝ} (ha : a ∈ Set.Icc (69 / 250) (277 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((553 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_652 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_653 ⟨hr,ha.2⟩ hz
theorem cover_654_655 {a z : ℝ} (ha : a ∈ Set.Icc (277 / 1000) (139 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((111 / 400):ℝ) with hl | hr
  · exact curvature_leaf_654 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_655 ⟨hr,ha.2⟩ hz
theorem cover_652_655 {a z : ℝ} (ha : a ∈ Set.Icc (69 / 250) (139 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((277 / 1000):ℝ) with hl | hr
  · exact cover_652_653 ⟨ha.1,hl⟩ hz
  · exact cover_654_655 ⟨hr,ha.2⟩ hz
theorem cover_648_655 {a z : ℝ} (ha : a ∈ Set.Icc (137 / 500) (139 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((69 / 250):ℝ) with hl | hr
  · exact cover_648_651 ⟨ha.1,hl⟩ hz
  · exact cover_652_655 ⟨hr,ha.2⟩ hz
theorem cover_640_655 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 100) (139 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((137 / 500):ℝ) with hl | hr
  · exact cover_640_647 ⟨ha.1,hl⟩ hz
  · exact cover_648_655 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0656
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0657
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0658
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0659
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0660
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0661
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0662
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0663
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0664
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0665
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0666
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0667
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0668
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0669
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0670
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0671
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_656_657 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (279 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((557 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_656 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_657 ⟨hr,ha.2⟩ hz
theorem cover_658_659 {a z : ℝ} (ha : a ∈ Set.Icc (279 / 1000) (7 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((559 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_658 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_659 ⟨hr,ha.2⟩ hz
theorem cover_656_659 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (7 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((279 / 1000):ℝ) with hl | hr
  · exact cover_656_657 ⟨ha.1,hl⟩ hz
  · exact cover_658_659 ⟨hr,ha.2⟩ hz
theorem cover_660_661 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 25) (281 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((561 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_660 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_661 ⟨hr,ha.2⟩ hz
theorem cover_662_663 {a z : ℝ} (ha : a ∈ Set.Icc (281 / 1000) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((563 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_662 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_663 ⟨hr,ha.2⟩ hz
theorem cover_660_663 {a z : ℝ} (ha : a ∈ Set.Icc (7 / 25) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((281 / 1000):ℝ) with hl | hr
  · exact cover_660_661 ⟨ha.1,hl⟩ hz
  · exact cover_662_663 ⟨hr,ha.2⟩ hz
theorem cover_656_663 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (141 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((7 / 25):ℝ) with hl | hr
  · exact cover_656_659 ⟨ha.1,hl⟩ hz
  · exact cover_660_663 ⟨hr,ha.2⟩ hz
theorem cover_664_665 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (283 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 400):ℝ) with hl | hr
  · exact curvature_leaf_664 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_665 ⟨hr,ha.2⟩ hz
theorem cover_666_667 {a z : ℝ} (ha : a ∈ Set.Icc (283 / 1000) (71 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((567 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_666 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_667 ⟨hr,ha.2⟩ hz
theorem cover_664_667 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (71 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((283 / 1000):ℝ) with hl | hr
  · exact cover_664_665 ⟨ha.1,hl⟩ hz
  · exact cover_666_667 ⟨hr,ha.2⟩ hz
theorem cover_668_669 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 250) (57 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((569 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_668 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_669 ⟨hr,ha.2⟩ hz
theorem cover_670_671 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 200) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((571 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_670 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_671 ⟨hr,ha.2⟩ hz
theorem cover_668_671 {a z : ℝ} (ha : a ∈ Set.Icc (71 / 250) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 200):ℝ) with hl | hr
  · exact cover_668_669 ⟨ha.1,hl⟩ hz
  · exact cover_670_671 ⟨hr,ha.2⟩ hz
theorem cover_664_671 {a z : ℝ} (ha : a ∈ Set.Icc (141 / 500) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((71 / 250):ℝ) with hl | hr
  · exact cover_664_667 ⟨ha.1,hl⟩ hz
  · exact cover_668_671 ⟨hr,ha.2⟩ hz
theorem cover_656_671 {a z : ℝ} (ha : a ∈ Set.Icc (139 / 500) (143 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((141 / 500):ℝ) with hl | hr
  · exact cover_656_663 ⟨ha.1,hl⟩ hz
  · exact cover_664_671 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

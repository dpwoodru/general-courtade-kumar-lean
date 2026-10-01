import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0720
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0721
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0722
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0723
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0724
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0725
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0726
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0727
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0728
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0729
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0730
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0731
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0732
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0733
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0734
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0735
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_720_721 {a z : ℝ} (ha : a ∈ Set.Icc (8 / 25) (161 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((321 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_720 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_721 ⟨hr,ha.2⟩ hz
theorem cover_722_723 {a z : ℝ} (ha : a ∈ Set.Icc (161 / 500) (81 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((323 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_722 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_723 ⟨hr,ha.2⟩ hz
theorem cover_720_723 {a z : ℝ} (ha : a ∈ Set.Icc (8 / 25) (81 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((161 / 500):ℝ) with hl | hr
  · exact cover_720_721 ⟨ha.1,hl⟩ hz
  · exact cover_722_723 ⟨hr,ha.2⟩ hz
theorem cover_724_725 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 250) (163 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 40):ℝ) with hl | hr
  · exact curvature_leaf_724 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_725 ⟨hr,ha.2⟩ hz
theorem cover_726_727 {a z : ℝ} (ha : a ∈ Set.Icc (163 / 500) (41 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((327 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_726 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_727 ⟨hr,ha.2⟩ hz
theorem cover_724_727 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 250) (41 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((163 / 500):ℝ) with hl | hr
  · exact cover_724_725 ⟨ha.1,hl⟩ hz
  · exact cover_726_727 ⟨hr,ha.2⟩ hz
theorem cover_720_727 {a z : ℝ} (ha : a ∈ Set.Icc (8 / 25) (41 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 250):ℝ) with hl | hr
  · exact cover_720_723 ⟨ha.1,hl⟩ hz
  · exact cover_724_727 ⟨hr,ha.2⟩ hz
theorem cover_728_729 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 125) (33 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((329 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_728 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_729 ⟨hr,ha.2⟩ hz
theorem cover_730_731 {a z : ℝ} (ha : a ∈ Set.Icc (33 / 100) (83 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((331 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_730 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_731 ⟨hr,ha.2⟩ hz
theorem cover_728_731 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 125) (83 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((33 / 100):ℝ) with hl | hr
  · exact cover_728_729 ⟨ha.1,hl⟩ hz
  · exact cover_730_731 ⟨hr,ha.2⟩ hz
theorem cover_732_733 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 250) (167 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((333 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_732 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_733 ⟨hr,ha.2⟩ hz
theorem cover_734_735 {a z : ℝ} (ha : a ∈ Set.Icc (167 / 500) (42 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((67 / 200):ℝ) with hl | hr
  · exact curvature_leaf_734 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_735 ⟨hr,ha.2⟩ hz
theorem cover_732_735 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 250) (42 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((167 / 500):ℝ) with hl | hr
  · exact cover_732_733 ⟨ha.1,hl⟩ hz
  · exact cover_734_735 ⟨hr,ha.2⟩ hz
theorem cover_728_735 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 125) (42 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 250):ℝ) with hl | hr
  · exact cover_728_731 ⟨ha.1,hl⟩ hz
  · exact cover_732_735 ⟨hr,ha.2⟩ hz
theorem cover_720_735 {a z : ℝ} (ha : a ∈ Set.Icc (8 / 25) (42 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 125):ℝ) with hl | hr
  · exact cover_720_727 ⟨ha.1,hl⟩ hz
  · exact cover_728_735 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

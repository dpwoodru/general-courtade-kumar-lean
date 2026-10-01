import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0624
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0625
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0626
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0627
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0628
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0629
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0630
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0631
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0632
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0633
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0634
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0635
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0636
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0637
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0638
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0639
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_624_625 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (263 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((21 / 80):ℝ) with hl | hr
  · exact curvature_leaf_624 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_625 ⟨hr,ha.2⟩ hz
theorem cover_626_627 {a z : ℝ} (ha : a ∈ Set.Icc (263 / 1000) (33 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((527 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_626 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_627 ⟨hr,ha.2⟩ hz
theorem cover_624_627 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (33 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((263 / 1000):ℝ) with hl | hr
  · exact cover_624_625 ⟨ha.1,hl⟩ hz
  · exact cover_626_627 ⟨hr,ha.2⟩ hz
theorem cover_628_629 {a z : ℝ} (ha : a ∈ Set.Icc (33 / 125) (53 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((529 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_628 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_629 ⟨hr,ha.2⟩ hz
theorem cover_630_631 {a z : ℝ} (ha : a ∈ Set.Icc (53 / 200) (133 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((531 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_630 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_631 ⟨hr,ha.2⟩ hz
theorem cover_628_631 {a z : ℝ} (ha : a ∈ Set.Icc (33 / 125) (133 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((53 / 200):ℝ) with hl | hr
  · exact cover_628_629 ⟨ha.1,hl⟩ hz
  · exact cover_630_631 ⟨hr,ha.2⟩ hz
theorem cover_624_631 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (133 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((33 / 125):ℝ) with hl | hr
  · exact cover_624_627 ⟨ha.1,hl⟩ hz
  · exact cover_628_631 ⟨hr,ha.2⟩ hz
theorem cover_632_633 {a z : ℝ} (ha : a ∈ Set.Icc (133 / 500) (267 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((533 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_632 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_633 ⟨hr,ha.2⟩ hz
theorem cover_634_635 {a z : ℝ} (ha : a ∈ Set.Icc (267 / 1000) (67 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((107 / 400):ℝ) with hl | hr
  · exact curvature_leaf_634 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_635 ⟨hr,ha.2⟩ hz
theorem cover_632_635 {a z : ℝ} (ha : a ∈ Set.Icc (133 / 500) (67 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((267 / 1000):ℝ) with hl | hr
  · exact cover_632_633 ⟨ha.1,hl⟩ hz
  · exact cover_634_635 ⟨hr,ha.2⟩ hz
theorem cover_636_637 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 250) (269 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((537 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_636 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_637 ⟨hr,ha.2⟩ hz
theorem cover_638_639 {a z : ℝ} (ha : a ∈ Set.Icc (269 / 1000) (27 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((539 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_638 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_639 ⟨hr,ha.2⟩ hz
theorem cover_636_639 {a z : ℝ} (ha : a ∈ Set.Icc (67 / 250) (27 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((269 / 1000):ℝ) with hl | hr
  · exact cover_636_637 ⟨ha.1,hl⟩ hz
  · exact cover_638_639 ⟨hr,ha.2⟩ hz
theorem cover_632_639 {a z : ℝ} (ha : a ∈ Set.Icc (133 / 500) (27 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((67 / 250):ℝ) with hl | hr
  · exact cover_632_635 ⟨ha.1,hl⟩ hz
  · exact cover_636_639 ⟨hr,ha.2⟩ hz
theorem cover_624_639 {a z : ℝ} (ha : a ∈ Set.Icc (131 / 500) (27 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((133 / 500):ℝ) with hl | hr
  · exact cover_624_631 ⟨ha.1,hl⟩ hz
  · exact cover_632_639 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0672
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0673
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0674
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0675
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0676
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0677
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0678
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0679
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0680
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0681
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0682
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0683
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0684
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0685
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0686
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0687
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_672_673 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (287 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((573 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_672 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_673 ⟨hr,ha.2⟩ hz
theorem cover_674_675 {a z : ℝ} (ha : a ∈ Set.Icc (287 / 1000) (36 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((23 / 80):ℝ) with hl | hr
  · exact curvature_leaf_674 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_675 ⟨hr,ha.2⟩ hz
theorem cover_672_675 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (36 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((287 / 1000):ℝ) with hl | hr
  · exact cover_672_673 ⟨ha.1,hl⟩ hz
  · exact cover_674_675 ⟨hr,ha.2⟩ hz
theorem cover_676_677 {a z : ℝ} (ha : a ∈ Set.Icc (36 / 125) (289 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((577 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_676 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_677 ⟨hr,ha.2⟩ hz
theorem cover_678_679 {a z : ℝ} (ha : a ∈ Set.Icc (289 / 1000) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((579 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_678 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_679 ⟨hr,ha.2⟩ hz
theorem cover_676_679 {a z : ℝ} (ha : a ∈ Set.Icc (36 / 125) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((289 / 1000):ℝ) with hl | hr
  · exact cover_676_677 ⟨ha.1,hl⟩ hz
  · exact cover_678_679 ⟨hr,ha.2⟩ hz
theorem cover_672_679 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (29 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((36 / 125):ℝ) with hl | hr
  · exact cover_672_675 ⟨ha.1,hl⟩ hz
  · exact cover_676_679 ⟨hr,ha.2⟩ hz
theorem cover_680_681 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (291 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((581 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_680 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_681 ⟨hr,ha.2⟩ hz
theorem cover_682_683 {a z : ℝ} (ha : a ∈ Set.Icc (291 / 1000) (73 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((583 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_682 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_683 ⟨hr,ha.2⟩ hz
theorem cover_680_683 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (73 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((291 / 1000):ℝ) with hl | hr
  · exact cover_680_681 ⟨ha.1,hl⟩ hz
  · exact cover_682_683 ⟨hr,ha.2⟩ hz
theorem cover_684_685 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 250) (293 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((117 / 400):ℝ) with hl | hr
  · exact curvature_leaf_684 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_685 ⟨hr,ha.2⟩ hz
theorem cover_686_687 {a z : ℝ} (ha : a ∈ Set.Icc (293 / 1000) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((587 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_686 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_687 ⟨hr,ha.2⟩ hz
theorem cover_684_687 {a z : ℝ} (ha : a ∈ Set.Icc (73 / 250) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((293 / 1000):ℝ) with hl | hr
  · exact cover_684_685 ⟨ha.1,hl⟩ hz
  · exact cover_686_687 ⟨hr,ha.2⟩ hz
theorem cover_680_687 {a z : ℝ} (ha : a ∈ Set.Icc (29 / 100) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((73 / 250):ℝ) with hl | hr
  · exact cover_680_683 ⟨ha.1,hl⟩ hz
  · exact cover_684_687 ⟨hr,ha.2⟩ hz
theorem cover_672_687 {a z : ℝ} (ha : a ∈ Set.Icc (143 / 500) (147 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((29 / 100):ℝ) with hl | hr
  · exact cover_672_679 ⟨ha.1,hl⟩ hz
  · exact cover_680_687 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

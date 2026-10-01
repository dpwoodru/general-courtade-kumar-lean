import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0576
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0577
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0578
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0579
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0580
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0581
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0582
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0583
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0584
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0585
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0586
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0587
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0588
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0589
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0590
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0591
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_576_577 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (239 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_576 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_577 ⟨hr,ha.2⟩ hz
theorem cover_578_579 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 1000) (6 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((479 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_578 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_579 ⟨hr,ha.2⟩ hz
theorem cover_576_579 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (6 / 25))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 1000):ℝ) with hl | hr
  · exact cover_576_577 ⟨ha.1,hl⟩ hz
  · exact cover_578_579 ⟨hr,ha.2⟩ hz
theorem cover_580_581 {a z : ℝ} (ha : a ∈ Set.Icc (6 / 25) (241 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((481 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_580 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_581 ⟨hr,ha.2⟩ hz
theorem cover_582_583 {a z : ℝ} (ha : a ∈ Set.Icc (241 / 1000) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((483 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_582 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_583 ⟨hr,ha.2⟩ hz
theorem cover_580_583 {a z : ℝ} (ha : a ∈ Set.Icc (6 / 25) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((241 / 1000):ℝ) with hl | hr
  · exact cover_580_581 ⟨ha.1,hl⟩ hz
  · exact cover_582_583 ⟨hr,ha.2⟩ hz
theorem cover_576_583 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (121 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((6 / 25):ℝ) with hl | hr
  · exact cover_576_579 ⟨ha.1,hl⟩ hz
  · exact cover_580_583 ⟨hr,ha.2⟩ hz
theorem cover_584_585 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (243 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 400):ℝ) with hl | hr
  · exact curvature_leaf_584 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_585 ⟨hr,ha.2⟩ hz
theorem cover_586_587 {a z : ℝ} (ha : a ∈ Set.Icc (243 / 1000) (61 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((487 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_586 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_587 ⟨hr,ha.2⟩ hz
theorem cover_584_587 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (61 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((243 / 1000):ℝ) with hl | hr
  · exact cover_584_585 ⟨ha.1,hl⟩ hz
  · exact cover_586_587 ⟨hr,ha.2⟩ hz
theorem cover_588_589 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 250) (49 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((489 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_588 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_589 ⟨hr,ha.2⟩ hz
theorem cover_590_591 {a z : ℝ} (ha : a ∈ Set.Icc (49 / 200) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((491 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_590 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_591 ⟨hr,ha.2⟩ hz
theorem cover_588_591 {a z : ℝ} (ha : a ∈ Set.Icc (61 / 250) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((49 / 200):ℝ) with hl | hr
  · exact cover_588_589 ⟨ha.1,hl⟩ hz
  · exact cover_590_591 ⟨hr,ha.2⟩ hz
theorem cover_584_591 {a z : ℝ} (ha : a ∈ Set.Icc (121 / 500) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 250):ℝ) with hl | hr
  · exact cover_584_587 ⟨ha.1,hl⟩ hz
  · exact cover_588_591 ⟨hr,ha.2⟩ hz
theorem cover_576_591 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 500) (123 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((121 / 500):ℝ) with hl | hr
  · exact cover_576_583 ⟨ha.1,hl⟩ hz
  · exact cover_584_591 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

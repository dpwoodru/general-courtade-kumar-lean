import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0544
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0545
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0546
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0547
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0548
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0549
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0550
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0551
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0552
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0553
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0554
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0555
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0556
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0557
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0558
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0559
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_544_545 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (223 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((89 / 400):ℝ) with hl | hr
  · exact curvature_leaf_544 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_545 ⟨hr,ha.2⟩ hz
theorem cover_546_547 {a z : ℝ} (ha : a ∈ Set.Icc (223 / 1000) (28 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((447 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_546 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_547 ⟨hr,ha.2⟩ hz
theorem cover_544_547 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (28 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((223 / 1000):ℝ) with hl | hr
  · exact cover_544_545 ⟨ha.1,hl⟩ hz
  · exact cover_546_547 ⟨hr,ha.2⟩ hz
theorem cover_548_549 {a z : ℝ} (ha : a ∈ Set.Icc (28 / 125) (9 / 40))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_548 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_549 ⟨hr,ha.2⟩ hz
theorem cover_550_551 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 40) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((451 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_550 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_551 ⟨hr,ha.2⟩ hz
theorem cover_548_551 {a z : ℝ} (ha : a ∈ Set.Icc (28 / 125) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 40):ℝ) with hl | hr
  · exact cover_548_549 ⟨ha.1,hl⟩ hz
  · exact cover_550_551 ⟨hr,ha.2⟩ hz
theorem cover_544_551 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (113 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((28 / 125):ℝ) with hl | hr
  · exact cover_544_547 ⟨ha.1,hl⟩ hz
  · exact cover_548_551 ⟨hr,ha.2⟩ hz
theorem cover_552_553 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (227 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((453 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_552 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_553 ⟨hr,ha.2⟩ hz
theorem cover_554_555 {a z : ℝ} (ha : a ∈ Set.Icc (227 / 1000) (57 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((91 / 400):ℝ) with hl | hr
  · exact curvature_leaf_554 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_555 ⟨hr,ha.2⟩ hz
theorem cover_552_555 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (57 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((227 / 1000):ℝ) with hl | hr
  · exact cover_552_553 ⟨ha.1,hl⟩ hz
  · exact cover_554_555 ⟨hr,ha.2⟩ hz
theorem cover_556_557 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 250) (229 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((457 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_556 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_557 ⟨hr,ha.2⟩ hz
theorem cover_558_559 {a z : ℝ} (ha : a ∈ Set.Icc (229 / 1000) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((459 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_558 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_559 ⟨hr,ha.2⟩ hz
theorem cover_556_559 {a z : ℝ} (ha : a ∈ Set.Icc (57 / 250) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((229 / 1000):ℝ) with hl | hr
  · exact cover_556_557 ⟨ha.1,hl⟩ hz
  · exact cover_558_559 ⟨hr,ha.2⟩ hz
theorem cover_552_559 {a z : ℝ} (ha : a ∈ Set.Icc (113 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((57 / 250):ℝ) with hl | hr
  · exact cover_552_555 ⟨ha.1,hl⟩ hz
  · exact cover_556_559 ⟨hr,ha.2⟩ hz
theorem cover_544_559 {a z : ℝ} (ha : a ∈ Set.Icc (111 / 500) (23 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((113 / 500):ℝ) with hl | hr
  · exact cover_544_551 ⟨ha.1,hl⟩ hz
  · exact cover_552_559 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0528
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0529
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0530
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0531
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0532
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0533
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0534
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0535
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0536
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0537
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0538
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0539
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0540
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0541
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0542
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0543
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_528_529 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 500) (43 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((429 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_528 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_529 ⟨hr,ha.2⟩ hz
theorem cover_530_531 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 200) (27 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((431 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_530 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_531 ⟨hr,ha.2⟩ hz
theorem cover_528_531 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 500) (27 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 200):ℝ) with hl | hr
  · exact cover_528_529 ⟨ha.1,hl⟩ hz
  · exact cover_530_531 ⟨hr,ha.2⟩ hz
theorem cover_532_533 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 125) (217 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_532 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_533 ⟨hr,ha.2⟩ hz
theorem cover_534_535 {a z : ℝ} (ha : a ∈ Set.Icc (217 / 1000) (109 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((87 / 400):ℝ) with hl | hr
  · exact curvature_leaf_534 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_535 ⟨hr,ha.2⟩ hz
theorem cover_532_535 {a z : ℝ} (ha : a ∈ Set.Icc (27 / 125) (109 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((217 / 1000):ℝ) with hl | hr
  · exact cover_532_533 ⟨ha.1,hl⟩ hz
  · exact cover_534_535 ⟨hr,ha.2⟩ hz
theorem cover_528_535 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 500) (109 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((27 / 125):ℝ) with hl | hr
  · exact cover_528_531 ⟨ha.1,hl⟩ hz
  · exact cover_532_535 ⟨hr,ha.2⟩ hz
theorem cover_536_537 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 500) (219 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((437 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_536 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_537 ⟨hr,ha.2⟩ hz
theorem cover_538_539 {a z : ℝ} (ha : a ∈ Set.Icc (219 / 1000) (11 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((439 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_538 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_539 ⟨hr,ha.2⟩ hz
theorem cover_536_539 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 500) (11 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((219 / 1000):ℝ) with hl | hr
  · exact cover_536_537 ⟨ha.1,hl⟩ hz
  · exact cover_538_539 ⟨hr,ha.2⟩ hz
theorem cover_540_541 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 50) (221 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((441 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_540 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_541 ⟨hr,ha.2⟩ hz
theorem cover_542_543 {a z : ℝ} (ha : a ∈ Set.Icc (221 / 1000) (111 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((443 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_542 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_543 ⟨hr,ha.2⟩ hz
theorem cover_540_543 {a z : ℝ} (ha : a ∈ Set.Icc (11 / 50) (111 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((221 / 1000):ℝ) with hl | hr
  · exact cover_540_541 ⟨ha.1,hl⟩ hz
  · exact cover_542_543 ⟨hr,ha.2⟩ hz
theorem cover_536_543 {a z : ℝ} (ha : a ∈ Set.Icc (109 / 500) (111 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((11 / 50):ℝ) with hl | hr
  · exact cover_536_539 ⟨ha.1,hl⟩ hz
  · exact cover_540_543 ⟨hr,ha.2⟩ hz
theorem cover_528_543 {a z : ℝ} (ha : a ∈ Set.Icc (107 / 500) (111 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((109 / 500):ℝ) with hl | hr
  · exact cover_528_535 ⟨ha.1,hl⟩ hz
  · exact cover_536_543 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

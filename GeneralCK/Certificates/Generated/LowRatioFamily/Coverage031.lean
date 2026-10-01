import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0496
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0497
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0498
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0499
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0500
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0501
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0502
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0503
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0504
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0505
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0506
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0507
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0508
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0509
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0510
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0511
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_496_497 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (999 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1997 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_496 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_497 ⟨hr,ha.2⟩ hz
theorem cover_498_499 {a z : ℝ} (ha : a ∈ Set.Icc (999 / 5000) (1 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1999 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_498 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_499 ⟨hr,ha.2⟩ hz
theorem cover_496_499 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (1 / 5))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((999 / 5000):ℝ) with hl | hr
  · exact cover_496_497 ⟨ha.1,hl⟩ hz
  · exact cover_498_499 ⟨hr,ha.2⟩ hz
theorem cover_500_501 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 5) (201 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((401 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_500 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_501 ⟨hr,ha.2⟩ hz
theorem cover_502_503 {a z : ℝ} (ha : a ∈ Set.Icc (201 / 1000) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((403 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_502 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_503 ⟨hr,ha.2⟩ hz
theorem cover_500_503 {a z : ℝ} (ha : a ∈ Set.Icc (1 / 5) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((201 / 1000):ℝ) with hl | hr
  · exact cover_500_501 ⟨ha.1,hl⟩ hz
  · exact cover_502_503 ⟨hr,ha.2⟩ hz
theorem cover_496_503 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (101 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1 / 5):ℝ) with hl | hr
  · exact cover_496_499 ⟨ha.1,hl⟩ hz
  · exact cover_500_503 ⟨hr,ha.2⟩ hz
theorem cover_504_505 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (203 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 400):ℝ) with hl | hr
  · exact curvature_leaf_504 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_505 ⟨hr,ha.2⟩ hz
theorem cover_506_507 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1000) (51 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((407 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_506 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_507 ⟨hr,ha.2⟩ hz
theorem cover_504_507 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (51 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 1000):ℝ) with hl | hr
  · exact cover_504_505 ⟨ha.1,hl⟩ hz
  · exact cover_506_507 ⟨hr,ha.2⟩ hz
theorem cover_508_509 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 250) (41 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((409 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_508 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_509 ⟨hr,ha.2⟩ hz
theorem cover_510_511 {a z : ℝ} (ha : a ∈ Set.Icc (41 / 200) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((411 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_510 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_511 ⟨hr,ha.2⟩ hz
theorem cover_508_511 {a z : ℝ} (ha : a ∈ Set.Icc (51 / 250) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((41 / 200):ℝ) with hl | hr
  · exact cover_508_509 ⟨ha.1,hl⟩ hz
  · exact cover_510_511 ⟨hr,ha.2⟩ hz
theorem cover_504_511 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 500) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((51 / 250):ℝ) with hl | hr
  · exact cover_504_507 ⟨ha.1,hl⟩ hz
  · exact cover_508_511 ⟨hr,ha.2⟩ hz
theorem cover_496_511 {a z : ℝ} (ha : a ∈ Set.Icc (499 / 2500) (103 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 500):ℝ) with hl | hr
  · exact cover_496_503 ⟨ha.1,hl⟩ hz
  · exact cover_504_511 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

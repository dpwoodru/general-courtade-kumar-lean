import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0016
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0017
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0018
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0019
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0020
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0021
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0022
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0023
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0024
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0025
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0026
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0027
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0028
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0029
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0030
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0031
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_16_17 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 2500) (759 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1517 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_16 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_17 ⟨hr,ha.2⟩ hz
theorem cover_18_19 {a z : ℝ} (ha : a ∈ Set.Icc (759 / 5000) (19 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1519 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_18 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_19 ⟨hr,ha.2⟩ hz
theorem cover_16_19 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 2500) (19 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((759 / 5000):ℝ) with hl | hr
  · exact cover_16_17 ⟨ha.1,hl⟩ hz
  · exact cover_18_19 ⟨hr,ha.2⟩ hz
theorem cover_20_21 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 125) (761 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1521 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_20 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_21 ⟨hr,ha.2⟩ hz
theorem cover_22_23 {a z : ℝ} (ha : a ∈ Set.Icc (761 / 5000) (381 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1523 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_22 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_23 ⟨hr,ha.2⟩ hz
theorem cover_20_23 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 125) (381 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((761 / 5000):ℝ) with hl | hr
  · exact cover_20_21 ⟨ha.1,hl⟩ hz
  · exact cover_22_23 ⟨hr,ha.2⟩ hz
theorem cover_16_23 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 2500) (381 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((19 / 125):ℝ) with hl | hr
  · exact cover_16_19 ⟨ha.1,hl⟩ hz
  · exact cover_20_23 ⟨hr,ha.2⟩ hz
theorem cover_24_25 {a z : ℝ} (ha : a ∈ Set.Icc (381 / 2500) (763 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((61 / 400):ℝ) with hl | hr
  · exact curvature_leaf_24 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_25 ⟨hr,ha.2⟩ hz
theorem cover_26_27 {a z : ℝ} (ha : a ∈ Set.Icc (763 / 5000) (191 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1527 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_26 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_27 ⟨hr,ha.2⟩ hz
theorem cover_24_27 {a z : ℝ} (ha : a ∈ Set.Icc (381 / 2500) (191 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((763 / 5000):ℝ) with hl | hr
  · exact cover_24_25 ⟨ha.1,hl⟩ hz
  · exact cover_26_27 ⟨hr,ha.2⟩ hz
theorem cover_28_29 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 1250) (153 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1529 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_28 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_29 ⟨hr,ha.2⟩ hz
theorem cover_30_31 {a z : ℝ} (ha : a ∈ Set.Icc (153 / 1000) (383 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1531 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_30 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_31 ⟨hr,ha.2⟩ hz
theorem cover_28_31 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 1250) (383 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((153 / 1000):ℝ) with hl | hr
  · exact cover_28_29 ⟨ha.1,hl⟩ hz
  · exact cover_30_31 ⟨hr,ha.2⟩ hz
theorem cover_24_31 {a z : ℝ} (ha : a ∈ Set.Icc (381 / 2500) (383 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 1250):ℝ) with hl | hr
  · exact cover_24_27 ⟨ha.1,hl⟩ hz
  · exact cover_28_31 ⟨hr,ha.2⟩ hz
theorem cover_16_31 {a z : ℝ} (ha : a ∈ Set.Icc (379 / 2500) (383 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((381 / 2500):ℝ) with hl | hr
  · exact cover_16_23 ⟨ha.1,hl⟩ hz
  · exact cover_24_31 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

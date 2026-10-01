import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0000
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0001
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0002
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0003
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0004
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0005
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0006
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0007
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0008
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0009
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0010
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0011
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0012
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0013
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0014
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0015
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_0_1 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (751 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1501 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_0 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1 ⟨hr,ha.2⟩ hz
theorem cover_2_3 {a z : ℝ} (ha : a ∈ Set.Icc (751 / 5000) (94 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1503 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_2 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_3 ⟨hr,ha.2⟩ hz
theorem cover_0_3 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (94 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((751 / 5000):ℝ) with hl | hr
  · exact cover_0_1 ⟨ha.1,hl⟩ hz
  · exact cover_2_3 ⟨hr,ha.2⟩ hz
theorem cover_4_5 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 625) (753 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((301 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_4 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_5 ⟨hr,ha.2⟩ hz
theorem cover_6_7 {a z : ℝ} (ha : a ∈ Set.Icc (753 / 5000) (377 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1507 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_6 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_7 ⟨hr,ha.2⟩ hz
theorem cover_4_7 {a z : ℝ} (ha : a ∈ Set.Icc (94 / 625) (377 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((753 / 5000):ℝ) with hl | hr
  · exact cover_4_5 ⟨ha.1,hl⟩ hz
  · exact cover_6_7 ⟨hr,ha.2⟩ hz
theorem cover_0_7 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (377 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((94 / 625):ℝ) with hl | hr
  · exact cover_0_3 ⟨ha.1,hl⟩ hz
  · exact cover_4_7 ⟨hr,ha.2⟩ hz
theorem cover_8_9 {a z : ℝ} (ha : a ∈ Set.Icc (377 / 2500) (151 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1509 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_8 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_9 ⟨hr,ha.2⟩ hz
theorem cover_10_11 {a z : ℝ} (ha : a ∈ Set.Icc (151 / 1000) (189 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1511 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_10 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_11 ⟨hr,ha.2⟩ hz
theorem cover_8_11 {a z : ℝ} (ha : a ∈ Set.Icc (377 / 2500) (189 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((151 / 1000):ℝ) with hl | hr
  · exact cover_8_9 ⟨ha.1,hl⟩ hz
  · exact cover_10_11 ⟨hr,ha.2⟩ hz
theorem cover_12_13 {a z : ℝ} (ha : a ∈ Set.Icc (189 / 1250) (757 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1513 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_12 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_13 ⟨hr,ha.2⟩ hz
theorem cover_14_15 {a z : ℝ} (ha : a ∈ Set.Icc (757 / 5000) (379 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((303 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_14 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_15 ⟨hr,ha.2⟩ hz
theorem cover_12_15 {a z : ℝ} (ha : a ∈ Set.Icc (189 / 1250) (379 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((757 / 5000):ℝ) with hl | hr
  · exact cover_12_13 ⟨ha.1,hl⟩ hz
  · exact cover_14_15 ⟨hr,ha.2⟩ hz
theorem cover_8_15 {a z : ℝ} (ha : a ∈ Set.Icc (377 / 2500) (379 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((189 / 1250):ℝ) with hl | hr
  · exact cover_8_11 ⟨ha.1,hl⟩ hz
  · exact cover_12_15 ⟨hr,ha.2⟩ hz
theorem cover_0_15 {a z : ℝ} (ha : a ∈ Set.Icc (3 / 20) (379 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((377 / 2500):ℝ) with hl | hr
  · exact cover_0_7 ⟨ha.1,hl⟩ hz
  · exact cover_8_15 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0080
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0081
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0082
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0083
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0084
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0085
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0086
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0087
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0088
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0089
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0090
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0091
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0092
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0093
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0094
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0095
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_80_81 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (791 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1581 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_80 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_81 ⟨hr,ha.2⟩ hz
theorem cover_82_83 {a z : ℝ} (ha : a ∈ Set.Icc (791 / 5000) (99 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1583 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_82 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_83 ⟨hr,ha.2⟩ hz
theorem cover_80_83 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (99 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((791 / 5000):ℝ) with hl | hr
  · exact cover_80_81 ⟨ha.1,hl⟩ hz
  · exact cover_82_83 ⟨hr,ha.2⟩ hz
theorem cover_84_85 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 625) (793 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((317 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_84 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_85 ⟨hr,ha.2⟩ hz
theorem cover_86_87 {a z : ℝ} (ha : a ∈ Set.Icc (793 / 5000) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1587 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_86 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_87 ⟨hr,ha.2⟩ hz
theorem cover_84_87 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 625) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((793 / 5000):ℝ) with hl | hr
  · exact cover_84_85 ⟨ha.1,hl⟩ hz
  · exact cover_86_87 ⟨hr,ha.2⟩ hz
theorem cover_80_87 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (397 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((99 / 625):ℝ) with hl | hr
  · exact cover_80_83 ⟨ha.1,hl⟩ hz
  · exact cover_84_87 ⟨hr,ha.2⟩ hz
theorem cover_88_89 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (159 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1589 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_88 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_89 ⟨hr,ha.2⟩ hz
theorem cover_90_91 {a z : ℝ} (ha : a ∈ Set.Icc (159 / 1000) (199 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1591 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_90 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_91 ⟨hr,ha.2⟩ hz
theorem cover_88_91 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (199 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((159 / 1000):ℝ) with hl | hr
  · exact cover_88_89 ⟨ha.1,hl⟩ hz
  · exact cover_90_91 ⟨hr,ha.2⟩ hz
theorem cover_92_93 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1250) (797 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1593 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_92 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_93 ⟨hr,ha.2⟩ hz
theorem cover_94_95 {a z : ℝ} (ha : a ∈ Set.Icc (797 / 5000) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((319 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_94 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_95 ⟨hr,ha.2⟩ hz
theorem cover_92_95 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1250) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((797 / 5000):ℝ) with hl | hr
  · exact cover_92_93 ⟨ha.1,hl⟩ hz
  · exact cover_94_95 ⟨hr,ha.2⟩ hz
theorem cover_88_95 {a z : ℝ} (ha : a ∈ Set.Icc (397 / 2500) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 1250):ℝ) with hl | hr
  · exact cover_88_91 ⟨ha.1,hl⟩ hz
  · exact cover_92_95 ⟨hr,ha.2⟩ hz
theorem cover_80_95 {a z : ℝ} (ha : a ∈ Set.Icc (79 / 500) (399 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 2500):ℝ) with hl | hr
  · exact cover_80_87 ⟨ha.1,hl⟩ hz
  · exact cover_88_95 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

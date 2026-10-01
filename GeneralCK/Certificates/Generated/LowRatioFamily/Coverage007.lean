import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0112
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0113
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0114
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0115
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0116
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0117
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0118
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0119
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0120
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0121
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0122
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0123
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0124
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0125
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0126
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0127
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_112_113 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (807 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1613 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_112 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_113 ⟨hr,ha.2⟩ hz
theorem cover_114_115 {a z : ℝ} (ha : a ∈ Set.Icc (807 / 5000) (101 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((323 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_114 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_115 ⟨hr,ha.2⟩ hz
theorem cover_112_115 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (101 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((807 / 5000):ℝ) with hl | hr
  · exact cover_112_113 ⟨ha.1,hl⟩ hz
  · exact cover_114_115 ⟨hr,ha.2⟩ hz
theorem cover_116_117 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 625) (809 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1617 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_116 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_117 ⟨hr,ha.2⟩ hz
theorem cover_118_119 {a z : ℝ} (ha : a ∈ Set.Icc (809 / 5000) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1619 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_118 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_119 ⟨hr,ha.2⟩ hz
theorem cover_116_119 {a z : ℝ} (ha : a ∈ Set.Icc (101 / 625) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((809 / 5000):ℝ) with hl | hr
  · exact cover_116_117 ⟨ha.1,hl⟩ hz
  · exact cover_118_119 ⟨hr,ha.2⟩ hz
theorem cover_112_119 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (81 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((101 / 625):ℝ) with hl | hr
  · exact cover_112_115 ⟨ha.1,hl⟩ hz
  · exact cover_116_119 ⟨hr,ha.2⟩ hz
theorem cover_120_121 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (811 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1621 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_120 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_121 ⟨hr,ha.2⟩ hz
theorem cover_122_123 {a z : ℝ} (ha : a ∈ Set.Icc (811 / 5000) (203 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1623 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_122 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_123 ⟨hr,ha.2⟩ hz
theorem cover_120_123 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (203 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((811 / 5000):ℝ) with hl | hr
  · exact cover_120_121 ⟨ha.1,hl⟩ hz
  · exact cover_122_123 ⟨hr,ha.2⟩ hz
theorem cover_124_125 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1250) (813 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((13 / 80):ℝ) with hl | hr
  · exact curvature_leaf_124 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_125 ⟨hr,ha.2⟩ hz
theorem cover_126_127 {a z : ℝ} (ha : a ∈ Set.Icc (813 / 5000) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1627 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_126 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_127 ⟨hr,ha.2⟩ hz
theorem cover_124_127 {a z : ℝ} (ha : a ∈ Set.Icc (203 / 1250) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((813 / 5000):ℝ) with hl | hr
  · exact cover_124_125 ⟨ha.1,hl⟩ hz
  · exact cover_126_127 ⟨hr,ha.2⟩ hz
theorem cover_120_127 {a z : ℝ} (ha : a ∈ Set.Icc (81 / 500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((203 / 1250):ℝ) with hl | hr
  · exact cover_120_123 ⟨ha.1,hl⟩ hz
  · exact cover_124_127 ⟨hr,ha.2⟩ hz
theorem cover_112_127 {a z : ℝ} (ha : a ∈ Set.Icc (403 / 2500) (407 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((81 / 500):ℝ) with hl | hr
  · exact cover_112_119 ⟨ha.1,hl⟩ hz
  · exact cover_120_127 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

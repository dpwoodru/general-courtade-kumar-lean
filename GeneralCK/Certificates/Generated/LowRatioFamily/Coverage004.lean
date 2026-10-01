import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0064
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0065
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0066
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0067
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0068
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0069
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0070
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0071
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0072
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0073
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0074
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0075
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0076
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0077
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0078
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0079
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_64_65 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (783 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((313 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_64 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_65 ⟨hr,ha.2⟩ hz
theorem cover_66_67 {a z : ℝ} (ha : a ∈ Set.Icc (783 / 5000) (98 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1567 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_66 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_67 ⟨hr,ha.2⟩ hz
theorem cover_64_67 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (98 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((783 / 5000):ℝ) with hl | hr
  · exact cover_64_65 ⟨ha.1,hl⟩ hz
  · exact cover_66_67 ⟨hr,ha.2⟩ hz
theorem cover_68_69 {a z : ℝ} (ha : a ∈ Set.Icc (98 / 625) (157 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1569 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_68 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_69 ⟨hr,ha.2⟩ hz
theorem cover_70_71 {a z : ℝ} (ha : a ∈ Set.Icc (157 / 1000) (393 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1571 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_70 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_71 ⟨hr,ha.2⟩ hz
theorem cover_68_71 {a z : ℝ} (ha : a ∈ Set.Icc (98 / 625) (393 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((157 / 1000):ℝ) with hl | hr
  · exact cover_68_69 ⟨ha.1,hl⟩ hz
  · exact cover_70_71 ⟨hr,ha.2⟩ hz
theorem cover_64_71 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (393 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((98 / 625):ℝ) with hl | hr
  · exact cover_64_67 ⟨ha.1,hl⟩ hz
  · exact cover_68_71 ⟨hr,ha.2⟩ hz
theorem cover_72_73 {a z : ℝ} (ha : a ∈ Set.Icc (393 / 2500) (787 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1573 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_72 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_73 ⟨hr,ha.2⟩ hz
theorem cover_74_75 {a z : ℝ} (ha : a ∈ Set.Icc (787 / 5000) (197 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((63 / 400):ℝ) with hl | hr
  · exact curvature_leaf_74 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_75 ⟨hr,ha.2⟩ hz
theorem cover_72_75 {a z : ℝ} (ha : a ∈ Set.Icc (393 / 2500) (197 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((787 / 5000):ℝ) with hl | hr
  · exact cover_72_73 ⟨ha.1,hl⟩ hz
  · exact cover_74_75 ⟨hr,ha.2⟩ hz
theorem cover_76_77 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 1250) (789 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1577 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_76 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_77 ⟨hr,ha.2⟩ hz
theorem cover_78_79 {a z : ℝ} (ha : a ∈ Set.Icc (789 / 5000) (79 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1579 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_78 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_79 ⟨hr,ha.2⟩ hz
theorem cover_76_79 {a z : ℝ} (ha : a ∈ Set.Icc (197 / 1250) (79 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((789 / 5000):ℝ) with hl | hr
  · exact cover_76_77 ⟨ha.1,hl⟩ hz
  · exact cover_78_79 ⟨hr,ha.2⟩ hz
theorem cover_72_79 {a z : ℝ} (ha : a ∈ Set.Icc (393 / 2500) (79 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((197 / 1250):ℝ) with hl | hr
  · exact cover_72_75 ⟨ha.1,hl⟩ hz
  · exact cover_76_79 ⟨hr,ha.2⟩ hz
theorem cover_64_79 {a z : ℝ} (ha : a ∈ Set.Icc (391 / 2500) (79 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((393 / 2500):ℝ) with hl | hr
  · exact cover_64_71 ⟨ha.1,hl⟩ hz
  · exact cover_72_79 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

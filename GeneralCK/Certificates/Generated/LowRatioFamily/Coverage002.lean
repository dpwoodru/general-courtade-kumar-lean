import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0032
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0033
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0034
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0035
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0036
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0037
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0038
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0039
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0040
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0041
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0042
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0043
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0044
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0045
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0046
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0047
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_32_33 {a z : ℝ} (ha : a ∈ Set.Icc (383 / 2500) (767 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1533 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_32 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_33 ⟨hr,ha.2⟩ hz
theorem cover_34_35 {a z : ℝ} (ha : a ∈ Set.Icc (767 / 5000) (96 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((307 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_34 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_35 ⟨hr,ha.2⟩ hz
theorem cover_32_35 {a z : ℝ} (ha : a ∈ Set.Icc (383 / 2500) (96 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((767 / 5000):ℝ) with hl | hr
  · exact cover_32_33 ⟨ha.1,hl⟩ hz
  · exact cover_34_35 ⟨hr,ha.2⟩ hz
theorem cover_36_37 {a z : ℝ} (ha : a ∈ Set.Icc (96 / 625) (769 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1537 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_36 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_37 ⟨hr,ha.2⟩ hz
theorem cover_38_39 {a z : ℝ} (ha : a ∈ Set.Icc (769 / 5000) (77 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1539 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_38 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_39 ⟨hr,ha.2⟩ hz
theorem cover_36_39 {a z : ℝ} (ha : a ∈ Set.Icc (96 / 625) (77 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((769 / 5000):ℝ) with hl | hr
  · exact cover_36_37 ⟨ha.1,hl⟩ hz
  · exact cover_38_39 ⟨hr,ha.2⟩ hz
theorem cover_32_39 {a z : ℝ} (ha : a ∈ Set.Icc (383 / 2500) (77 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((96 / 625):ℝ) with hl | hr
  · exact cover_32_35 ⟨ha.1,hl⟩ hz
  · exact cover_36_39 ⟨hr,ha.2⟩ hz
theorem cover_40_41 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 500) (771 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1541 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_40 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_41 ⟨hr,ha.2⟩ hz
theorem cover_42_43 {a z : ℝ} (ha : a ∈ Set.Icc (771 / 5000) (193 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1543 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_42 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_43 ⟨hr,ha.2⟩ hz
theorem cover_40_43 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 500) (193 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((771 / 5000):ℝ) with hl | hr
  · exact cover_40_41 ⟨ha.1,hl⟩ hz
  · exact cover_42_43 ⟨hr,ha.2⟩ hz
theorem cover_44_45 {a z : ℝ} (ha : a ∈ Set.Icc (193 / 1250) (773 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((309 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_44 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_45 ⟨hr,ha.2⟩ hz
theorem cover_46_47 {a z : ℝ} (ha : a ∈ Set.Icc (773 / 5000) (387 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1547 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_46 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_47 ⟨hr,ha.2⟩ hz
theorem cover_44_47 {a z : ℝ} (ha : a ∈ Set.Icc (193 / 1250) (387 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((773 / 5000):ℝ) with hl | hr
  · exact cover_44_45 ⟨ha.1,hl⟩ hz
  · exact cover_46_47 ⟨hr,ha.2⟩ hz
theorem cover_40_47 {a z : ℝ} (ha : a ∈ Set.Icc (77 / 500) (387 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((193 / 1250):ℝ) with hl | hr
  · exact cover_40_43 ⟨ha.1,hl⟩ hz
  · exact cover_44_47 ⟨hr,ha.2⟩ hz
theorem cover_32_47 {a z : ℝ} (ha : a ∈ Set.Icc (383 / 2500) (387 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((77 / 500):ℝ) with hl | hr
  · exact cover_32_39 ⟨ha.1,hl⟩ hz
  · exact cover_40_47 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

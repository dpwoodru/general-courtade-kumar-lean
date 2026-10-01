import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0048
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0049
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0050
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0051
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0052
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0053
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0054
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0055
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0056
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0057
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0058
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0059
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0060
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0061
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0062
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0063
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_48_49 {a z : ℝ} (ha : a ∈ Set.Icc (387 / 2500) (31 / 200))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1549 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_48 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_49 ⟨hr,ha.2⟩ hz
theorem cover_50_51 {a z : ℝ} (ha : a ∈ Set.Icc (31 / 200) (97 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1551 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_50 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_51 ⟨hr,ha.2⟩ hz
theorem cover_48_51 {a z : ℝ} (ha : a ∈ Set.Icc (387 / 2500) (97 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((31 / 200):ℝ) with hl | hr
  · exact cover_48_49 ⟨ha.1,hl⟩ hz
  · exact cover_50_51 ⟨hr,ha.2⟩ hz
theorem cover_52_53 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 625) (777 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1553 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_52 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_53 ⟨hr,ha.2⟩ hz
theorem cover_54_55 {a z : ℝ} (ha : a ∈ Set.Icc (777 / 5000) (389 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((311 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_54 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_55 ⟨hr,ha.2⟩ hz
theorem cover_52_55 {a z : ℝ} (ha : a ∈ Set.Icc (97 / 625) (389 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((777 / 5000):ℝ) with hl | hr
  · exact cover_52_53 ⟨ha.1,hl⟩ hz
  · exact cover_54_55 ⟨hr,ha.2⟩ hz
theorem cover_48_55 {a z : ℝ} (ha : a ∈ Set.Icc (387 / 2500) (389 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((97 / 625):ℝ) with hl | hr
  · exact cover_48_51 ⟨ha.1,hl⟩ hz
  · exact cover_52_55 ⟨hr,ha.2⟩ hz
theorem cover_56_57 {a z : ℝ} (ha : a ∈ Set.Icc (389 / 2500) (779 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1557 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_56 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_57 ⟨hr,ha.2⟩ hz
theorem cover_58_59 {a z : ℝ} (ha : a ∈ Set.Icc (779 / 5000) (39 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1559 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_58 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_59 ⟨hr,ha.2⟩ hz
theorem cover_56_59 {a z : ℝ} (ha : a ∈ Set.Icc (389 / 2500) (39 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((779 / 5000):ℝ) with hl | hr
  · exact cover_56_57 ⟨ha.1,hl⟩ hz
  · exact cover_58_59 ⟨hr,ha.2⟩ hz
theorem cover_60_61 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 250) (781 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1561 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_60 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_61 ⟨hr,ha.2⟩ hz
theorem cover_62_63 {a z : ℝ} (ha : a ∈ Set.Icc (781 / 5000) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1563 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_62 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_63 ⟨hr,ha.2⟩ hz
theorem cover_60_63 {a z : ℝ} (ha : a ∈ Set.Icc (39 / 250) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((781 / 5000):ℝ) with hl | hr
  · exact cover_60_61 ⟨ha.1,hl⟩ hz
  · exact cover_62_63 ⟨hr,ha.2⟩ hz
theorem cover_56_63 {a z : ℝ} (ha : a ∈ Set.Icc (389 / 2500) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((39 / 250):ℝ) with hl | hr
  · exact cover_56_59 ⟨ha.1,hl⟩ hz
  · exact cover_60_63 ⟨hr,ha.2⟩ hz
theorem cover_48_63 {a z : ℝ} (ha : a ∈ Set.Icc (387 / 2500) (391 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((389 / 2500):ℝ) with hl | hr
  · exact cover_48_55 ⟨ha.1,hl⟩ hz
  · exact cover_56_63 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

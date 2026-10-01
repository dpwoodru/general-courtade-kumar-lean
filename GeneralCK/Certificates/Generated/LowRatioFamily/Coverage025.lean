import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0400
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0401
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0402
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0403
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0404
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0405
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0406
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0407
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0408
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0409
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0410
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0411
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0412
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0413
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0414
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0415
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_400_401 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 100) (951 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1901 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_400 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_401 ⟨hr,ha.2⟩ hz
theorem cover_402_403 {a z : ℝ} (ha : a ∈ Set.Icc (951 / 5000) (119 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1903 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_402 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_403 ⟨hr,ha.2⟩ hz
theorem cover_400_403 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 100) (119 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((951 / 5000):ℝ) with hl | hr
  · exact cover_400_401 ⟨ha.1,hl⟩ hz
  · exact cover_402_403 ⟨hr,ha.2⟩ hz
theorem cover_404_405 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 625) (953 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((381 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_404 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_405 ⟨hr,ha.2⟩ hz
theorem cover_406_407 {a z : ℝ} (ha : a ∈ Set.Icc (953 / 5000) (477 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1907 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_406 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_407 ⟨hr,ha.2⟩ hz
theorem cover_404_407 {a z : ℝ} (ha : a ∈ Set.Icc (119 / 625) (477 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((953 / 5000):ℝ) with hl | hr
  · exact cover_404_405 ⟨ha.1,hl⟩ hz
  · exact cover_406_407 ⟨hr,ha.2⟩ hz
theorem cover_400_407 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 100) (477 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((119 / 625):ℝ) with hl | hr
  · exact cover_400_403 ⟨ha.1,hl⟩ hz
  · exact cover_404_407 ⟨hr,ha.2⟩ hz
theorem cover_408_409 {a z : ℝ} (ha : a ∈ Set.Icc (477 / 2500) (191 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1909 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_408 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_409 ⟨hr,ha.2⟩ hz
theorem cover_410_411 {a z : ℝ} (ha : a ∈ Set.Icc (191 / 1000) (239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1911 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_410 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_411 ⟨hr,ha.2⟩ hz
theorem cover_408_411 {a z : ℝ} (ha : a ∈ Set.Icc (477 / 2500) (239 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((191 / 1000):ℝ) with hl | hr
  · exact cover_408_409 ⟨ha.1,hl⟩ hz
  · exact cover_410_411 ⟨hr,ha.2⟩ hz
theorem cover_412_413 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 1250) (957 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1913 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_412 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_413 ⟨hr,ha.2⟩ hz
theorem cover_414_415 {a z : ℝ} (ha : a ∈ Set.Icc (957 / 5000) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((383 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_414 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_415 ⟨hr,ha.2⟩ hz
theorem cover_412_415 {a z : ℝ} (ha : a ∈ Set.Icc (239 / 1250) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((957 / 5000):ℝ) with hl | hr
  · exact cover_412_413 ⟨ha.1,hl⟩ hz
  · exact cover_414_415 ⟨hr,ha.2⟩ hz
theorem cover_408_415 {a z : ℝ} (ha : a ∈ Set.Icc (477 / 2500) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((239 / 1250):ℝ) with hl | hr
  · exact cover_408_411 ⟨ha.1,hl⟩ hz
  · exact cover_412_415 ⟨hr,ha.2⟩ hz
theorem cover_400_415 {a z : ℝ} (ha : a ∈ Set.Icc (19 / 100) (479 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((477 / 2500):ℝ) with hl | hr
  · exact cover_400_407 ⟨ha.1,hl⟩ hz
  · exact cover_408_415 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

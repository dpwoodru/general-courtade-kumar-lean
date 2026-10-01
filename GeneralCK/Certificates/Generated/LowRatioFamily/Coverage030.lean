import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0480
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0481
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0482
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0483
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0484
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0485
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0486
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0487
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0488
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0489
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0490
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0491
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0492
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0493
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0494
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0495
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_480_481 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (991 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1981 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_480 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_481 ⟨hr,ha.2⟩ hz
theorem cover_482_483 {a z : ℝ} (ha : a ∈ Set.Icc (991 / 5000) (124 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1983 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_482 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_483 ⟨hr,ha.2⟩ hz
theorem cover_480_483 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (124 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((991 / 5000):ℝ) with hl | hr
  · exact cover_480_481 ⟨ha.1,hl⟩ hz
  · exact cover_482_483 ⟨hr,ha.2⟩ hz
theorem cover_484_485 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 625) (993 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((397 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_484 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_485 ⟨hr,ha.2⟩ hz
theorem cover_486_487 {a z : ℝ} (ha : a ∈ Set.Icc (993 / 5000) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1987 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_486 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_487 ⟨hr,ha.2⟩ hz
theorem cover_484_487 {a z : ℝ} (ha : a ∈ Set.Icc (124 / 625) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((993 / 5000):ℝ) with hl | hr
  · exact cover_484_485 ⟨ha.1,hl⟩ hz
  · exact cover_486_487 ⟨hr,ha.2⟩ hz
theorem cover_480_487 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (497 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((124 / 625):ℝ) with hl | hr
  · exact cover_480_483 ⟨ha.1,hl⟩ hz
  · exact cover_484_487 ⟨hr,ha.2⟩ hz
theorem cover_488_489 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (199 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1989 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_488 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_489 ⟨hr,ha.2⟩ hz
theorem cover_490_491 {a z : ℝ} (ha : a ∈ Set.Icc (199 / 1000) (249 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1991 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_490 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_491 ⟨hr,ha.2⟩ hz
theorem cover_488_491 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (249 / 1250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((199 / 1000):ℝ) with hl | hr
  · exact cover_488_489 ⟨ha.1,hl⟩ hz
  · exact cover_490_491 ⟨hr,ha.2⟩ hz
theorem cover_492_493 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1250) (997 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1993 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_492 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_493 ⟨hr,ha.2⟩ hz
theorem cover_494_495 {a z : ℝ} (ha : a ∈ Set.Icc (997 / 5000) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((399 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_494 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_495 ⟨hr,ha.2⟩ hz
theorem cover_492_495 {a z : ℝ} (ha : a ∈ Set.Icc (249 / 1250) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((997 / 5000):ℝ) with hl | hr
  · exact cover_492_493 ⟨ha.1,hl⟩ hz
  · exact cover_494_495 ⟨hr,ha.2⟩ hz
theorem cover_488_495 {a z : ℝ} (ha : a ∈ Set.Icc (497 / 2500) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((249 / 1250):ℝ) with hl | hr
  · exact cover_488_491 ⟨ha.1,hl⟩ hz
  · exact cover_492_495 ⟨hr,ha.2⟩ hz
theorem cover_480_495 {a z : ℝ} (ha : a ∈ Set.Icc (99 / 500) (499 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((497 / 2500):ℝ) with hl | hr
  · exact cover_480_487 ⟨ha.1,hl⟩ hz
  · exact cover_488_495 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0288
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0289
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0290
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0291
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0292
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0293
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0294
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0295
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0296
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0297
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0298
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0299
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0300
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0301
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0302
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell0303
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_288_289 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (179 / 1000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1789 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_288 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_289 ⟨hr,ha.2⟩ hz
theorem cover_290_291 {a z : ℝ} (ha : a ∈ Set.Icc (179 / 1000) (112 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1791 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_290 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_291 ⟨hr,ha.2⟩ hz
theorem cover_288_291 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (112 / 625))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((179 / 1000):ℝ) with hl | hr
  · exact cover_288_289 ⟨ha.1,hl⟩ hz
  · exact cover_290_291 ⟨hr,ha.2⟩ hz
theorem cover_292_293 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 625) (897 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1793 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_292 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_293 ⟨hr,ha.2⟩ hz
theorem cover_294_295 {a z : ℝ} (ha : a ∈ Set.Icc (897 / 5000) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((359 / 2000):ℝ) with hl | hr
  · exact curvature_leaf_294 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_295 ⟨hr,ha.2⟩ hz
theorem cover_292_295 {a z : ℝ} (ha : a ∈ Set.Icc (112 / 625) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((897 / 5000):ℝ) with hl | hr
  · exact cover_292_293 ⟨ha.1,hl⟩ hz
  · exact cover_294_295 ⟨hr,ha.2⟩ hz
theorem cover_288_295 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (449 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((112 / 625):ℝ) with hl | hr
  · exact cover_288_291 ⟨ha.1,hl⟩ hz
  · exact cover_292_295 ⟨hr,ha.2⟩ hz
theorem cover_296_297 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (899 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1797 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_296 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_297 ⟨hr,ha.2⟩ hz
theorem cover_298_299 {a z : ℝ} (ha : a ∈ Set.Icc (899 / 5000) (9 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1799 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_298 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_299 ⟨hr,ha.2⟩ hz
theorem cover_296_299 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (9 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((899 / 5000):ℝ) with hl | hr
  · exact cover_296_297 ⟨ha.1,hl⟩ hz
  · exact cover_298_299 ⟨hr,ha.2⟩ hz
theorem cover_300_301 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 50) (901 / 5000))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1801 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_300 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_301 ⟨hr,ha.2⟩ hz
theorem cover_302_303 {a z : ℝ} (ha : a ∈ Set.Icc (901 / 5000) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((1803 / 10000):ℝ) with hl | hr
  · exact curvature_leaf_302 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_303 ⟨hr,ha.2⟩ hz
theorem cover_300_303 {a z : ℝ} (ha : a ∈ Set.Icc (9 / 50) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((901 / 5000):ℝ) with hl | hr
  · exact cover_300_301 ⟨ha.1,hl⟩ hz
  · exact cover_302_303 ⟨hr,ha.2⟩ hz
theorem cover_296_303 {a z : ℝ} (ha : a ∈ Set.Icc (449 / 2500) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((9 / 50):ℝ) with hl | hr
  · exact cover_296_299 ⟨ha.1,hl⟩ hz
  · exact cover_300_303 ⟨hr,ha.2⟩ hz
theorem cover_288_303 {a z : ℝ} (ha : a ∈ Set.Icc (447 / 2500) (451 / 2500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((449 / 2500):ℝ) with hl | hr
  · exact cover_288_295 ⟨ha.1,hl⟩ hz
  · exact cover_296_303 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

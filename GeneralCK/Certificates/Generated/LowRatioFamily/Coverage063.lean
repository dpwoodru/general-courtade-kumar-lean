import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1008
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1009
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1010
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1011
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1012
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1013
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1014
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1015
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1016
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1017
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1018
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1019
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1020
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1021
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1022
import GeneralCK.Certificates.Generated.LowRatioFamily.Cell1023
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
theorem cover_1008_1009 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (83 / 100))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((827 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1008 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1009 ⟨hr,ha.2⟩ hz
theorem cover_1010_1011 {a z : ℝ} (ha : a ∈ Set.Icc (83 / 100) (209 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((833 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1010 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1011 ⟨hr,ha.2⟩ hz
theorem cover_1008_1011 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (209 / 250))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((83 / 100):ℝ) with hl | hr
  · exact cover_1008_1009 ⟨ha.1,hl⟩ hz
  · exact cover_1010_1011 ⟨hr,ha.2⟩ hz
theorem cover_1012_1013 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 250) (421 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((839 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1012 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1013 ⟨hr,ha.2⟩ hz
theorem cover_1014_1015 {a z : ℝ} (ha : a ∈ Set.Icc (421 / 500) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((169 / 200):ℝ) with hl | hr
  · exact curvature_leaf_1014 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1015 ⟨hr,ha.2⟩ hz
theorem cover_1012_1015 {a z : ℝ} (ha : a ∈ Set.Icc (209 / 250) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((421 / 500):ℝ) with hl | hr
  · exact cover_1012_1013 ⟨ha.1,hl⟩ hz
  · exact cover_1014_1015 ⟨hr,ha.2⟩ hz
theorem cover_1008_1015 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (106 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((209 / 250):ℝ) with hl | hr
  · exact cover_1008_1011 ⟨ha.1,hl⟩ hz
  · exact cover_1012_1015 ⟨hr,ha.2⟩ hz
theorem cover_1016_1017 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (427 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((851 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1016 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1017 ⟨hr,ha.2⟩ hz
theorem cover_1018_1019 {a z : ℝ} (ha : a ∈ Set.Icc (427 / 500) (43 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((857 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1018 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1019 ⟨hr,ha.2⟩ hz
theorem cover_1016_1019 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (43 / 50))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((427 / 500):ℝ) with hl | hr
  · exact cover_1016_1017 ⟨ha.1,hl⟩ hz
  · exact cover_1018_1019 ⟨hr,ha.2⟩ hz
theorem cover_1020_1021 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 50) (433 / 500))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((863 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1020 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1021 ⟨hr,ha.2⟩ hz
theorem cover_1022_1023 {a z : ℝ} (ha : a ∈ Set.Icc (433 / 500) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((869 / 1000):ℝ) with hl | hr
  · exact curvature_leaf_1022 ⟨ha.1,hl⟩ hz
  · exact curvature_leaf_1023 ⟨hr,ha.2⟩ hz
theorem cover_1020_1023 {a z : ℝ} (ha : a ∈ Set.Icc (43 / 50) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((433 / 500):ℝ) with hl | hr
  · exact cover_1020_1021 ⟨ha.1,hl⟩ hz
  · exact cover_1022_1023 ⟨hr,ha.2⟩ hz
theorem cover_1016_1023 {a z : ℝ} (ha : a ∈ Set.Icc (106 / 125) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((43 / 50):ℝ) with hl | hr
  · exact cover_1016_1019 ⟨ha.1,hl⟩ hz
  · exact cover_1020_1023 ⟨hr,ha.2⟩ hz
theorem cover_1008_1023 {a z : ℝ} (ha : a ∈ Set.Icc (103 / 125) (109 / 125))
    (hz : z ∈ Set.Ioc (0:ℝ) (1/1000)) : 0 < GeneralCK.Reflection.curvature a (a*z) := by
  rcases le_total a ((106 / 125):ℝ) with hl | hr
  · exact cover_1008_1015 ⟨ha.1,hl⟩ hz
  · exact cover_1016_1023 ⟨hr,ha.2⟩ hz

end GeneralCK.Certificates.LowRatioFamily

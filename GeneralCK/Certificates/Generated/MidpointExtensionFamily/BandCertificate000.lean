import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage000
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage001
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage002
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage003
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage004
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage005
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage006
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage007
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage008
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage009
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage010
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage011
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage012
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage013
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage014
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage015
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage016
import GeneralCK.Certificates.Generated.MidpointExtensionFamily.Coverage017
namespace GeneralCK.Certificates.ReflectionMidpointExtensionFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem bandcertificate000 {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (1/20) (81/1000) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (479/2500:ℝ)
  · by_cases h1 : a ≤ (813/5000:ℝ)
    · by_cases h2 : a ≤ (781/5000:ℝ)
      · by_cases h3 : a ≤ (153/1000:ℝ)
        · exact coverage000 ⟨ha.1,h3⟩ hz
        · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h3)),h2⟩ hz
      · by_cases h4 : a ≤ (797/5000:ℝ)
        · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h2)),h4⟩ hz
        · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h4)),h1⟩ hz
    · by_cases h5 : a ≤ (106/625:ℝ)
      · by_cases h6 : a ≤ (829/5000:ℝ)
        · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h1)),h6⟩ hz
        · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h6)),h5⟩ hz
      · by_cases h7 : a ≤ (22/125:ℝ)
        · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h5)),h7⟩ hz
        · by_cases h8 : a ≤ (114/625:ℝ)
          · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h7)),h8⟩ hz
          · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h8)),h0⟩ hz
  · by_cases h9 : a ≤ (127/500:ℝ)
    · by_cases h10 : a ≤ (427/2000:ℝ)
      · by_cases h11 : a ≤ (101/500:ℝ)
        · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h0)),h11⟩ hz
        · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h11)),h10⟩ hz
      · by_cases h12 : a ≤ (459/2000:ℝ)
        · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h10)),h12⟩ hz
        · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h12)),h9⟩ hz
    · by_cases h13 : a ≤ (44/125:ℝ)
      · by_cases h14 : a ≤ (73/250:ℝ)
        · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h9)),h14⟩ hz
        · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h14)),h13⟩ hz
      · by_cases h15 : a ≤ (239/500:ℝ)
        · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h13)),h15⟩ hz
        · by_cases h16 : a ≤ (163/200:ℝ)
          · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h15)),h16⟩ hz
          · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h16)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointExtensionFamily

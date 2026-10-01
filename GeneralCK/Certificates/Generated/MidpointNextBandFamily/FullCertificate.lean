import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage000
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage001
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage002
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage003
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage004
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage005
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage006
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage007
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage008
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage009
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage010
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage011
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage012
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage013
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage014
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage015
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage016
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage017
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage018
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage019
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage020
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage021
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage022
import GeneralCK.Certificates.Generated.MidpointNextBandFamily.Coverage023
namespace GeneralCK.Certificates.ReflectionMidpointNextBandFamily
open GeneralCK.Reflection GeneralCK.Certificates.Reflection
set_option maxRecDepth 10000
theorem full_midpoint_next_band {a z : ℝ} (ha : Bounds (3/20) (999/1000) a)
    (hz : Bounds (406621/5000000) (17/200) z) : 0 < curvature a (a*z) := by
  by_cases h0 : a ≤ (113/625:ℝ)
  · by_cases h1 : a ≤ (399/2500:ℝ)
    · by_cases h2 : a ≤ (387/2500:ℝ)
      · by_cases h3 : a ≤ (379/2500:ℝ)
        · exact coverage000 ⟨ha.1,h3⟩ hz
        · by_cases h4 : a ≤ (383/2500:ℝ)
          · exact coverage001 ⟨(le_of_lt (lt_of_not_ge h3)),h4⟩ hz
          · exact coverage002 ⟨(le_of_lt (lt_of_not_ge h4)),h2⟩ hz
      · by_cases h5 : a ≤ (391/2500:ℝ)
        · exact coverage003 ⟨(le_of_lt (lt_of_not_ge h2)),h5⟩ hz
        · by_cases h6 : a ≤ (79/500:ℝ)
          · exact coverage004 ⟨(le_of_lt (lt_of_not_ge h5)),h6⟩ hz
          · exact coverage005 ⟨(le_of_lt (lt_of_not_ge h6)),h1⟩ hz
    · by_cases h7 : a ≤ (423/2500:ℝ)
      · by_cases h8 : a ≤ (407/2500:ℝ)
        · exact coverage006 ⟨(le_of_lt (lt_of_not_ge h1)),h8⟩ hz
        · by_cases h9 : a ≤ (83/500:ℝ)
          · exact coverage007 ⟨(le_of_lt (lt_of_not_ge h8)),h9⟩ hz
          · exact coverage008 ⟨(le_of_lt (lt_of_not_ge h9)),h7⟩ hz
      · by_cases h10 : a ≤ (431/2500:ℝ)
        · exact coverage009 ⟨(le_of_lt (lt_of_not_ge h7)),h10⟩ hz
        · by_cases h11 : a ≤ (439/2500:ℝ)
          · exact coverage010 ⟨(le_of_lt (lt_of_not_ge h10)),h11⟩ hz
          · exact coverage011 ⟨(le_of_lt (lt_of_not_ge h11)),h0⟩ hz
  · by_cases h12 : a ≤ (489/2000:ℝ)
    · by_cases h13 : a ≤ (51/250:ℝ)
      · by_cases h14 : a ≤ (117/625:ℝ)
        · exact coverage012 ⟨(le_of_lt (lt_of_not_ge h0)),h14⟩ hz
        · by_cases h15 : a ≤ (39/200:ℝ)
          · exact coverage013 ⟨(le_of_lt (lt_of_not_ge h14)),h15⟩ hz
          · exact coverage014 ⟨(le_of_lt (lt_of_not_ge h15)),h13⟩ hz
      · by_cases h16 : a ≤ (53/250:ℝ)
        · exact coverage015 ⟨(le_of_lt (lt_of_not_ge h13)),h16⟩ hz
        · by_cases h17 : a ≤ (113/500:ℝ)
          · exact coverage016 ⟨(le_of_lt (lt_of_not_ge h16)),h17⟩ hz
          · exact coverage017 ⟨(le_of_lt (lt_of_not_ge h17)),h12⟩ hz
    · by_cases h18 : a ≤ (393/1000:ℝ)
      · by_cases h19 : a ≤ (109/400:ℝ)
        · exact coverage018 ⟨(le_of_lt (lt_of_not_ge h12)),h19⟩ hz
        · by_cases h20 : a ≤ (79/250:ℝ)
          · exact coverage019 ⟨(le_of_lt (lt_of_not_ge h19)),h20⟩ hz
          · exact coverage020 ⟨(le_of_lt (lt_of_not_ge h20)),h18⟩ hz
      · by_cases h21 : a ≤ (141/250:ℝ)
        · exact coverage021 ⟨(le_of_lt (lt_of_not_ge h18)),h21⟩ hz
        · by_cases h22 : a ≤ (499/500:ℝ)
          · exact coverage022 ⟨(le_of_lt (lt_of_not_ge h21)),h22⟩ hz
          · exact coverage023 ⟨(le_of_lt (lt_of_not_ge h22)),ha.2⟩ hz
end GeneralCK.Certificates.ReflectionMidpointNextBandFamily

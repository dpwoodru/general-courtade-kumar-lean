import CKLaneC2R.Cells.S05.B000
import CKLaneC2R.Cells.S05.B001
import CKLaneC2R.Cells.S05.B002
import CKLaneC2R.Cells.S05.B003
import CKLaneC2R.Cells.S05.B004
import CKLaneC2R.Cells.S05.B005
import CKLaneC2R.Cells.S05.B006
import CKLaneC2R.Cells.S05.B007
import CKLaneC2R.Cells.S05.B008
import CKLaneC2R.Cells.S05.B009
import CKLaneC2R.Cells.S05.B010
import CKLaneC2R.Cells.S05.B011
import CKLaneC2R.Cells.S05.B012
import CKLaneC2R.Cells.S05.B013
import CKLaneC2R.Cells.S05.B014
import CKLaneC2R.Cells.S05.B015
import CKLaneC2R.Cells.S05.B016
import CKLaneC2R.Cells.S05.B017
import CKLaneC2R.Cells.S05.B018
import CKLaneC2R.Cells.S05.B019
import CKLaneC2R.Cells.S05.B020
import CKLaneC2R.Cells.S05.B021
import CKLaneC2R.Cells.S05.B022
import CKLaneC2R.Cells.S05.B023
import CKLaneC2R.Cells.S05.B024
import CKLaneC2R.Cells.S05.B025
import CKLaneC2R.Cells.S05.B026
import CKLaneC2R.Cells.S05.B027
import CKLaneC2R.Cells.S05.B028
import CKLaneC2R.Cells.S05.B029
import CKLaneC2R.Cells.S05.B030
import CKLaneC2R.Cells.S05.B031
import CKLaneC2R.Cells.S05.B032
import CKLaneC2R.Cells.S05.B033
import CKLaneC2R.Cells.S05.B034
import CKLaneC2R.Cells.S05.B035
import CKLaneC2R.Cells.S05.B036

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 5: a ∈ [9/10,999/1000], z ∈ [43/500,999/1000] (732 cells, BSP depth 20). -/
theorem strip5 {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((1899/2000 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((3699/4000 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((7299/8000 : ℚ) : ℝ)
      · -- left
        by_cases h3 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h4 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h5 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h6 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h7 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c48_pos ha1 h2 hz1 h7
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c50_pos ha1 h2 (not_le.mp h7).le h6
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c0_pos ha1 h2 (not_le.mp h6).le h5
            · -- right
              by_cases h8 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c4_pos ha1 h2 (not_le.mp h5).le h8
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c6_pos ha1 h2 (not_le.mp h8).le h4
          · -- right
            by_cases h9 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h10 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c12_pos ha1 h2 (not_le.mp h4).le h10
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c14_pos ha1 h2 (not_le.mp h10).le h9
            · -- right
              by_cases h11 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c20_pos ha1 h2 (not_le.mp h9).le h11
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c22_pos ha1 h2 (not_le.mp h11).le h3
        · -- right
          by_cases h12 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h13 : z ≤ ((5253/8000 : ℚ) : ℝ)
            · -- left
              by_cases h14 : z ≤ ((9593/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c34_pos ha1 h2 (not_le.mp h3).le h14
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c36_pos ha1 h2 (not_le.mp h14).le h13
            · -- right
              by_cases h15 : z ≤ ((11419/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B002.c42_pos ha1 h2 (not_le.mp h13).le h15
              · -- right
                by_cases h16 : z ≤ ((23751/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c91_pos ha1 h2 (not_le.mp h15).le h16
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c92_pos ha1 h2 (not_le.mp h16).le h12
          · -- right
            by_cases h17 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h18 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h19 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c115_pos ha1 h2 (not_le.mp h12).le h19
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c116_pos ha1 h2 (not_le.mp h19).le h18
              · -- right
                by_cases h20 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c119_pos ha1 h2 (not_le.mp h18).le h20
                · -- right
                  exact CKLaneC2R.Cells.S05.B006.c120_pos ha1 h2 (not_le.mp h20).le h17
            · -- right
              by_cases h21 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h22 : z ≤ ((29229/32000 : ℚ) : ℝ)
                · -- left
                  by_cases h23 : a ≤ ((14499/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c187_pos ha1 h23 (not_le.mp h17).le h22
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c188_pos (not_le.mp h23).le h2 (not_le.mp h17).le h22
                · -- right
                  by_cases h24 : z ≤ ((59371/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c191_pos ha1 h2 (not_le.mp h22).le h24
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c192_pos ha1 h2 (not_le.mp h24).le h21
              · -- right
                by_cases h25 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h26 : z ≤ ((61197/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B010.c200_pos ha1 h2 (not_le.mp h21).le h26
                  · -- right
                    by_cases h27 : a ≤ ((14499/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c253_pos ha1 h27 (not_le.mp h26).le h25
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c254_pos (not_le.mp h27).le h2 (not_le.mp h26).le h25
                · -- right
                  by_cases h28 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h29 : a ≤ ((14499/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c267_pos ha1 h29 (not_le.mp h25).le h28
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c268_pos (not_le.mp h29).le h2 (not_le.mp h25).le h28
                  · -- right
                    by_cases h30 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h31 : a ≤ ((14499/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c334_pos ha1 h31 (not_le.mp h28).le h30
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c335_pos (not_le.mp h31).le h2 (not_le.mp h28).le h30
                    · -- right
                      by_cases h32 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c338_pos ha1 h2 (not_le.mp h30).le h32
                      · -- right
                        by_cases h33 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c403_pos ha1 h2 (not_le.mp h32).le h33
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c404_pos ha1 h2 (not_le.mp h33).le hz2
      · -- right
        by_cases h34 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h35 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h36 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h37 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h38 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c49_pos (not_le.mp h2).le h1 hz1 h38
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c51_pos (not_le.mp h2).le h1 (not_le.mp h38).le h37
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c1_pos (not_le.mp h2).le h1 (not_le.mp h37).le h36
            · -- right
              by_cases h39 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c5_pos (not_le.mp h2).le h1 (not_le.mp h36).le h39
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c7_pos (not_le.mp h2).le h1 (not_le.mp h39).le h35
          · -- right
            by_cases h40 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h41 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c13_pos (not_le.mp h2).le h1 (not_le.mp h35).le h41
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c15_pos (not_le.mp h2).le h1 (not_le.mp h41).le h40
            · -- right
              by_cases h42 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c21_pos (not_le.mp h2).le h1 (not_le.mp h40).le h42
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c23_pos (not_le.mp h2).le h1 (not_le.mp h42).le h34
        · -- right
          by_cases h43 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h44 : z ≤ ((5253/8000 : ℚ) : ℝ)
            · -- left
              by_cases h45 : z ≤ ((9593/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c35_pos (not_le.mp h2).le h1 (not_le.mp h34).le h45
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c37_pos (not_le.mp h2).le h1 (not_le.mp h45).le h44
            · -- right
              by_cases h46 : z ≤ ((11419/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B002.c43_pos (not_le.mp h2).le h1 (not_le.mp h44).le h46
              · -- right
                by_cases h47 : z ≤ ((23751/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c93_pos (not_le.mp h2).le h1 (not_le.mp h46).le h47
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c94_pos (not_le.mp h2).le h1 (not_le.mp h47).le h43
          · -- right
            by_cases h48 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h49 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h50 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c117_pos (not_le.mp h2).le h1 (not_le.mp h43).le h50
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c118_pos (not_le.mp h2).le h1 (not_le.mp h50).le h49
              · -- right
                by_cases h51 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c121_pos (not_le.mp h2).le h1 (not_le.mp h49).le h51
                · -- right
                  exact CKLaneC2R.Cells.S05.B006.c122_pos (not_le.mp h2).le h1 (not_le.mp h51).le h48
            · -- right
              by_cases h52 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h53 : z ≤ ((29229/32000 : ℚ) : ℝ)
                · -- left
                  by_cases h54 : a ≤ ((14697/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c189_pos (not_le.mp h2).le h54 (not_le.mp h48).le h53
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c190_pos (not_le.mp h54).le h1 (not_le.mp h48).le h53
                · -- right
                  by_cases h55 : z ≤ ((59371/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c193_pos (not_le.mp h2).le h1 (not_le.mp h53).le h55
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c194_pos (not_le.mp h2).le h1 (not_le.mp h55).le h52
              · -- right
                by_cases h56 : a ≤ ((14697/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h57 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h58 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c255_pos (not_le.mp h2).le h56 (not_le.mp h52).le h58
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c257_pos (not_le.mp h2).le h56 (not_le.mp h58).le h57
                  · -- right
                    by_cases h59 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c269_pos (not_le.mp h2).le h56 (not_le.mp h57).le h59
                    · -- right
                      by_cases h60 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c336_pos (not_le.mp h2).le h56 (not_le.mp h59).le h60
                      · -- right
                        by_cases h61 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c401_pos (not_le.mp h2).le h56 (not_le.mp h60).le h61
                        · -- right
                          by_cases h62 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c465_pos (not_le.mp h2).le h56 (not_le.mp h61).le h62
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c467_pos (not_le.mp h2).le h56 (not_le.mp h62).le hz2
                · -- right
                  by_cases h63 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h64 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c256_pos (not_le.mp h56).le h1 (not_le.mp h52).le h64
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c258_pos (not_le.mp h56).le h1 (not_le.mp h64).le h63
                  · -- right
                    by_cases h65 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c270_pos (not_le.mp h56).le h1 (not_le.mp h63).le h65
                    · -- right
                      by_cases h66 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c337_pos (not_le.mp h56).le h1 (not_le.mp h65).le h66
                      · -- right
                        by_cases h67 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c402_pos (not_le.mp h56).le h1 (not_le.mp h66).le h67
                        · -- right
                          by_cases h68 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c466_pos (not_le.mp h56).le h1 (not_le.mp h67).le h68
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c468_pos (not_le.mp h56).le h1 (not_le.mp h68).le hz2
    · -- right
      by_cases h69 : a ≤ ((7497/8000 : ℚ) : ℝ)
      · -- left
        by_cases h70 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h71 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h72 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h73 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h74 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c52_pos (not_le.mp h1).le h69 hz1 h74
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c53_pos (not_le.mp h1).le h69 (not_le.mp h74).le h73
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c2_pos (not_le.mp h1).le h69 (not_le.mp h73).le h72
            · -- right
              by_cases h75 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c8_pos (not_le.mp h1).le h69 (not_le.mp h72).le h75
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c9_pos (not_le.mp h1).le h69 (not_le.mp h75).le h71
          · -- right
            by_cases h76 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h77 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c16_pos (not_le.mp h1).le h69 (not_le.mp h71).le h77
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c18_pos (not_le.mp h1).le h69 (not_le.mp h77).le h76
            · -- right
              by_cases h78 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c24_pos (not_le.mp h1).le h69 (not_le.mp h76).le h78
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c26_pos (not_le.mp h1).le h69 (not_le.mp h78).le h70
        · -- right
          by_cases h79 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h80 : z ≤ ((5253/8000 : ℚ) : ℝ)
            · -- left
              by_cases h81 : z ≤ ((9593/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c38_pos (not_le.mp h1).le h69 (not_le.mp h70).le h81
              · -- right
                exact CKLaneC2R.Cells.S05.B002.c40_pos (not_le.mp h1).le h69 (not_le.mp h81).le h80
            · -- right
              by_cases h82 : z ≤ ((11419/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B002.c44_pos (not_le.mp h1).le h69 (not_le.mp h80).le h82
              · -- right
                by_cases h83 : z ≤ ((23751/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c95_pos (not_le.mp h1).le h69 (not_le.mp h82).le h83
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c96_pos (not_le.mp h1).le h69 (not_le.mp h83).le h79
          · -- right
            by_cases h84 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h85 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h86 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c123_pos (not_le.mp h1).le h69 (not_le.mp h79).le h86
                · -- right
                  exact CKLaneC2R.Cells.S05.B006.c124_pos (not_le.mp h1).le h69 (not_le.mp h86).le h85
              · -- right
                by_cases h87 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c127_pos (not_le.mp h1).le h69 (not_le.mp h85).le h87
                · -- right
                  by_cases h88 : a ≤ ((2979/3200 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c164_pos (not_le.mp h1).le h88 (not_le.mp h87).le h84
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c165_pos (not_le.mp h88).le h69 (not_le.mp h87).le h84
            · -- right
              by_cases h89 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h90 : z ≤ ((29229/32000 : ℚ) : ℝ)
                · -- left
                  by_cases h91 : a ≤ ((2979/3200 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c195_pos (not_le.mp h1).le h91 (not_le.mp h84).le h90
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c196_pos (not_le.mp h91).le h69 (not_le.mp h84).le h90
                · -- right
                  by_cases h92 : z ≤ ((59371/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c199_pos (not_le.mp h1).le h69 (not_le.mp h90).le h92
                  · -- right
                    by_cases h93 : a ≤ ((2979/3200 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c247_pos (not_le.mp h1).le h93 (not_le.mp h92).le h89
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c248_pos (not_le.mp h93).le h69 (not_le.mp h92).le h89
              · -- right
                by_cases h94 : a ≤ ((2979/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h95 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h96 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c259_pos (not_le.mp h1).le h94 (not_le.mp h89).le h96
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c261_pos (not_le.mp h1).le h94 (not_le.mp h96).le h95
                  · -- right
                    by_cases h97 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c271_pos (not_le.mp h1).le h94 (not_le.mp h95).le h97
                    · -- right
                      by_cases h98 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c339_pos (not_le.mp h1).le h94 (not_le.mp h97).le h98
                      · -- right
                        by_cases h99 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c405_pos (not_le.mp h1).le h94 (not_le.mp h98).le h99
                        · -- right
                          by_cases h100 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c469_pos (not_le.mp h1).le h94 (not_le.mp h99).le h100
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c470_pos (not_le.mp h1).le h94 (not_le.mp h100).le hz2
                · -- right
                  by_cases h101 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h102 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c260_pos (not_le.mp h94).le h69 (not_le.mp h89).le h102
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c262_pos (not_le.mp h94).le h69 (not_le.mp h102).le h101
                  · -- right
                    by_cases h103 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c272_pos (not_le.mp h94).le h69 (not_le.mp h101).le h103
                    · -- right
                      by_cases h104 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c340_pos (not_le.mp h94).le h69 (not_le.mp h103).le h104
                      · -- right
                        by_cases h105 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c406_pos (not_le.mp h94).le h69 (not_le.mp h104).le h105
                        · -- right
                          by_cases h106 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c471_pos (not_le.mp h94).le h69 (not_le.mp h105).le h106
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c472_pos (not_le.mp h94).le h69 (not_le.mp h106).le hz2
      · -- right
        by_cases h107 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h108 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h109 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h110 : z ≤ ((2289/16000 : ℚ) : ℝ)
              · -- left
                by_cases h111 : z ≤ ((733/6400 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c54_pos (not_le.mp h69).le h0 hz1 h111
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c55_pos (not_le.mp h69).le h0 (not_le.mp h111).le h110
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c3_pos (not_le.mp h69).le h0 (not_le.mp h110).le h109
            · -- right
              by_cases h112 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c10_pos (not_le.mp h69).le h0 (not_le.mp h109).le h112
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c11_pos (not_le.mp h69).le h0 (not_le.mp h112).le h108
          · -- right
            by_cases h113 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h114 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B000.c17_pos (not_le.mp h69).le h0 (not_le.mp h108).le h114
              · -- right
                exact CKLaneC2R.Cells.S05.B000.c19_pos (not_le.mp h69).le h0 (not_le.mp h114).le h113
            · -- right
              by_cases h115 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c25_pos (not_le.mp h69).le h0 (not_le.mp h113).le h115
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c27_pos (not_le.mp h69).le h0 (not_le.mp h115).le h107
        · -- right
          by_cases h116 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h117 : z ≤ ((5253/8000 : ℚ) : ℝ)
            · -- left
              by_cases h118 : z ≤ ((9593/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c39_pos (not_le.mp h69).le h0 (not_le.mp h107).le h118
              · -- right
                exact CKLaneC2R.Cells.S05.B002.c41_pos (not_le.mp h69).le h0 (not_le.mp h118).le h117
            · -- right
              by_cases h119 : z ≤ ((11419/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B002.c45_pos (not_le.mp h69).le h0 (not_le.mp h117).le h119
              · -- right
                by_cases h120 : z ≤ ((23751/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c97_pos (not_le.mp h69).le h0 (not_le.mp h119).le h120
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c98_pos (not_le.mp h69).le h0 (not_le.mp h120).le h116
          · -- right
            by_cases h121 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h122 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h123 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c125_pos (not_le.mp h69).le h0 (not_le.mp h116).le h123
                · -- right
                  exact CKLaneC2R.Cells.S05.B006.c126_pos (not_le.mp h69).le h0 (not_le.mp h123).le h122
              · -- right
                by_cases h124 : z ≤ ((27403/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c128_pos (not_le.mp h69).le h0 (not_le.mp h122).le h124
                · -- right
                  by_cases h125 : a ≤ ((15093/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c166_pos (not_le.mp h69).le h125 (not_le.mp h124).le h121
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c167_pos (not_le.mp h125).le h0 (not_le.mp h124).le h121
            · -- right
              by_cases h126 : a ≤ ((15093/16000 : ℚ) : ℝ)
              · -- left
                by_cases h127 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h128 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c197_pos (not_le.mp h69).le h126 (not_le.mp h121).le h128
                  · -- right
                    by_cases h129 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c249_pos (not_le.mp h69).le h126 (not_le.mp h128).le h129
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c251_pos (not_le.mp h69).le h126 (not_le.mp h129).le h127
                · -- right
                  by_cases h130 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h131 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c263_pos (not_le.mp h69).le h126 (not_le.mp h127).le h131
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c265_pos (not_le.mp h69).le h126 (not_le.mp h131).le h130
                  · -- right
                    by_cases h132 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h133 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c330_pos (not_le.mp h69).le h126 (not_le.mp h130).le h133
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c331_pos (not_le.mp h69).le h126 (not_le.mp h133).le h132
                    · -- right
                      by_cases h134 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c341_pos (not_le.mp h69).le h126 (not_le.mp h132).le h134
                      · -- right
                        by_cases h135 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c407_pos (not_le.mp h69).le h126 (not_le.mp h134).le h135
                        · -- right
                          by_cases h136 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c473_pos (not_le.mp h69).le h126 (not_le.mp h135).le h136
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c474_pos (not_le.mp h69).le h126 (not_le.mp h136).le hz2
              · -- right
                by_cases h137 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h138 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c198_pos (not_le.mp h126).le h0 (not_le.mp h121).le h138
                  · -- right
                    by_cases h139 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c250_pos (not_le.mp h126).le h0 (not_le.mp h138).le h139
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c252_pos (not_le.mp h126).le h0 (not_le.mp h139).le h137
                · -- right
                  by_cases h140 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h141 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c264_pos (not_le.mp h126).le h0 (not_le.mp h137).le h141
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c266_pos (not_le.mp h126).le h0 (not_le.mp h141).le h140
                  · -- right
                    by_cases h142 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h143 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c332_pos (not_le.mp h126).le h0 (not_le.mp h140).le h143
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c333_pos (not_le.mp h126).le h0 (not_le.mp h143).le h142
                    · -- right
                      by_cases h144 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c342_pos (not_le.mp h126).le h0 (not_le.mp h142).le h144
                      · -- right
                        by_cases h145 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c408_pos (not_le.mp h126).le h0 (not_le.mp h144).le h145
                        · -- right
                          by_cases h146 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c475_pos (not_le.mp h126).le h0 (not_le.mp h145).le h146
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c476_pos (not_le.mp h126).le h0 (not_le.mp h146).le hz2
  · -- right
    by_cases h147 : a ≤ ((3897/4000 : ℚ) : ℝ)
    · -- left
      by_cases h148 : a ≤ ((1539/1600 : ℚ) : ℝ)
      · -- left
        by_cases h149 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h150 : z ≤ ((1257/4000 : ℚ) : ℝ)
          · -- left
            by_cases h151 : z ≤ ((1601/8000 : ℚ) : ℝ)
            · -- left
              by_cases h152 : a ≤ ((15291/16000 : ℚ) : ℝ)
              · -- left
                by_cases h153 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c56_pos (not_le.mp h0).le h152 hz1 h153
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c58_pos (not_le.mp h0).le h152 (not_le.mp h153).le h151
              · -- right
                by_cases h154 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B002.c57_pos (not_le.mp h152).le h148 hz1 h154
                · -- right
                  exact CKLaneC2R.Cells.S05.B002.c59_pos (not_le.mp h152).le h148 (not_le.mp h154).le h151
            · -- right
              by_cases h155 : z ≤ ((823/3200 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c28_pos (not_le.mp h0).le h148 (not_le.mp h151).le h155
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c29_pos (not_le.mp h0).le h148 (not_le.mp h155).le h150
          · -- right
            by_cases h156 : z ≤ ((3427/8000 : ℚ) : ℝ)
            · -- left
              by_cases h157 : z ≤ ((5941/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c30_pos (not_le.mp h0).le h148 (not_le.mp h150).le h157
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c31_pos (not_le.mp h0).le h148 (not_le.mp h157).le h156
            · -- right
              by_cases h158 : z ≤ ((7767/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B001.c32_pos (not_le.mp h0).le h148 (not_le.mp h156).le h158
              · -- right
                exact CKLaneC2R.Cells.S05.B001.c33_pos (not_le.mp h0).le h148 (not_le.mp h158).le h149
        · -- right
          by_cases h159 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h160 : z ≤ ((5253/8000 : ℚ) : ℝ)
            · -- left
              by_cases h161 : z ≤ ((9593/16000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.Cells.S05.B002.c46_pos (not_le.mp h0).le h148 (not_le.mp h149).le h161
              · -- right
                exact CKLaneC2R.Cells.S05.B002.c47_pos (not_le.mp h0).le h148 (not_le.mp h161).le h160
            · -- right
              by_cases h162 : z ≤ ((11419/16000 : ℚ) : ℝ)
              · -- left
                by_cases h163 : a ≤ ((15291/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c103_pos (not_le.mp h0).le h163 (not_le.mp h160).le h162
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c104_pos (not_le.mp h163).le h148 (not_le.mp h160).le h162
              · -- right
                by_cases h164 : z ≤ ((23751/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c107_pos (not_le.mp h0).le h148 (not_le.mp h162).le h164
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c108_pos (not_le.mp h0).le h148 (not_le.mp h164).le h159
          · -- right
            by_cases h165 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h166 : z ≤ ((2649/3200 : ℚ) : ℝ)
              · -- left
                by_cases h167 : z ≤ ((25577/32000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B006.c129_pos (not_le.mp h0).le h148 (not_le.mp h159).le h167
                · -- right
                  by_cases h168 : a ≤ ((15291/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c168_pos (not_le.mp h0).le h168 (not_le.mp h167).le h166
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c169_pos (not_le.mp h168).le h148 (not_le.mp h167).le h166
              · -- right
                by_cases h169 : a ≤ ((15291/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h170 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c174_pos (not_le.mp h0).le h169 (not_le.mp h166).le h170
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c176_pos (not_le.mp h0).le h169 (not_le.mp h170).le h165
                · -- right
                  by_cases h171 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c175_pos (not_le.mp h169).le h148 (not_le.mp h166).le h171
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c177_pos (not_le.mp h169).le h148 (not_le.mp h171).le h165
            · -- right
              by_cases h172 : a ≤ ((15291/16000 : ℚ) : ℝ)
              · -- left
                by_cases h173 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h174 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B010.c201_pos (not_le.mp h0).le h172 (not_le.mp h165).le h174
                  · -- right
                    by_cases h175 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c277_pos (not_le.mp h0).le h172 (not_le.mp h174).le h175
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c278_pos (not_le.mp h0).le h172 (not_le.mp h175).le h173
                · -- right
                  by_cases h176 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h177 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c290_pos (not_le.mp h0).le h172 (not_le.mp h173).le h177
                    · -- right
                      by_cases h178 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c357_pos (not_le.mp h0).le h172 (not_le.mp h177).le h178
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c358_pos (not_le.mp h0).le h172 (not_le.mp h178).le h176
                  · -- right
                    by_cases h179 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h180 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c368_pos (not_le.mp h0).le h172 (not_le.mp h176).le h180
                      · -- right
                        exact CKLaneC2R.Cells.S05.B018.c369_pos (not_le.mp h0).le h172 (not_le.mp h180).le h179
                    · -- right
                      by_cases h181 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h182 : a ≤ ((30483/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c431_pos (not_le.mp h0).le h182 (not_le.mp h179).le h181
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c432_pos (not_le.mp h182).le h172 (not_le.mp h179).le h181
                      · -- right
                        by_cases h183 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c435_pos (not_le.mp h0).le h172 (not_le.mp h181).le h183
                        · -- right
                          by_cases h184 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c491_pos (not_le.mp h0).le h172 (not_le.mp h183).le h184
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c492_pos (not_le.mp h0).le h172 (not_le.mp h184).le hz2
              · -- right
                by_cases h185 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h186 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B010.c202_pos (not_le.mp h172).le h148 (not_le.mp h165).le h186
                  · -- right
                    by_cases h187 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c279_pos (not_le.mp h172).le h148 (not_le.mp h186).le h187
                    · -- right
                      exact CKLaneC2R.Cells.S05.B014.c280_pos (not_le.mp h172).le h148 (not_le.mp h187).le h185
                · -- right
                  by_cases h188 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h189 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c291_pos (not_le.mp h172).le h148 (not_le.mp h185).le h189
                    · -- right
                      by_cases h190 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c359_pos (not_le.mp h172).le h148 (not_le.mp h189).le h190
                      · -- right
                        exact CKLaneC2R.Cells.S05.B018.c360_pos (not_le.mp h172).le h148 (not_le.mp h190).le h188
                  · -- right
                    by_cases h191 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h192 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c370_pos (not_le.mp h172).le h148 (not_le.mp h188).le h192
                      · -- right
                        by_cases h193 : a ≤ ((30681/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c421_pos (not_le.mp h172).le h193 (not_le.mp h192).le h191
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c422_pos (not_le.mp h193).le h148 (not_le.mp h192).le h191
                    · -- right
                      by_cases h194 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h195 : a ≤ ((30681/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c433_pos (not_le.mp h172).le h195 (not_le.mp h191).le h194
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c434_pos (not_le.mp h195).le h148 (not_le.mp h191).le h194
                      · -- right
                        by_cases h196 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h197 : a ≤ ((30681/32000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c489_pos (not_le.mp h172).le h197 (not_le.mp h194).le h196
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c490_pos (not_le.mp h197).le h148 (not_le.mp h194).le h196
                        · -- right
                          by_cases h198 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c493_pos (not_le.mp h172).le h148 (not_le.mp h196).le h198
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c494_pos (not_le.mp h172).le h148 (not_le.mp h198).le hz2
      · -- right
        by_cases h199 : a ≤ ((15489/16000 : ℚ) : ℝ)
        · -- left
          by_cases h200 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h201 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h202 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h203 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c60_pos (not_le.mp h148).le h199 hz1 h203
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c62_pos (not_le.mp h148).le h199 (not_le.mp h203).le h202
              · -- right
                by_cases h204 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c64_pos (not_le.mp h148).le h199 (not_le.mp h202).le h204
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c65_pos (not_le.mp h148).le h199 (not_le.mp h204).le h201
            · -- right
              by_cases h205 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h206 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c68_pos (not_le.mp h148).le h199 (not_le.mp h201).le h206
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c69_pos (not_le.mp h148).le h199 (not_le.mp h206).le h205
              · -- right
                by_cases h207 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c72_pos (not_le.mp h148).le h199 (not_le.mp h205).le h207
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c74_pos (not_le.mp h148).le h199 (not_le.mp h207).le h200
          · -- right
            by_cases h208 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h209 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h210 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c99_pos (not_le.mp h148).le h199 (not_le.mp h200).le h210
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c101_pos (not_le.mp h148).le h199 (not_le.mp h210).le h209
              · -- right
                by_cases h211 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c105_pos (not_le.mp h148).le h199 (not_le.mp h209).le h211
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c109_pos (not_le.mp h148).le h199 (not_le.mp h211).le h208
            · -- right
              by_cases h212 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h213 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h214 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c170_pos (not_le.mp h148).le h199 (not_le.mp h208).le h214
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c172_pos (not_le.mp h148).le h199 (not_le.mp h214).le h213
                · -- right
                  by_cases h215 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c178_pos (not_le.mp h148).le h199 (not_le.mp h213).le h215
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c180_pos (not_le.mp h148).le h199 (not_le.mp h215).le h212
              · -- right
                by_cases h216 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h217 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h218 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c273_pos (not_le.mp h148).le h199 (not_le.mp h212).le h218
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c274_pos (not_le.mp h148).le h199 (not_le.mp h218).le h217
                  · -- right
                    by_cases h219 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c281_pos (not_le.mp h148).le h199 (not_le.mp h217).le h219
                    · -- right
                      exact CKLaneC2R.Cells.S05.B014.c282_pos (not_le.mp h148).le h199 (not_le.mp h219).le h216
                · -- right
                  by_cases h220 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h221 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h222 : a ≤ ((30879/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c361_pos (not_le.mp h148).le h222 (not_le.mp h216).le h221
                      · -- right
                        exact CKLaneC2R.Cells.S05.B018.c362_pos (not_le.mp h222).le h199 (not_le.mp h216).le h221
                    · -- right
                      by_cases h223 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c365_pos (not_le.mp h148).le h199 (not_le.mp h221).le h223
                      · -- right
                        exact CKLaneC2R.Cells.S05.B018.c366_pos (not_le.mp h148).le h199 (not_le.mp h223).le h220
                  · -- right
                    by_cases h224 : a ≤ ((30879/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h225 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h226 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c423_pos (not_le.mp h148).le h224 (not_le.mp h220).le h226
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c425_pos (not_le.mp h148).le h224 (not_le.mp h226).le h225
                      · -- right
                        by_cases h227 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c436_pos (not_le.mp h148).le h224 (not_le.mp h225).le h227
                        · -- right
                          by_cases h228 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c495_pos (not_le.mp h148).le h224 (not_le.mp h227).le h228
                          · -- right
                            by_cases h229 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c528_pos (not_le.mp h148).le h224 (not_le.mp h228).le h229
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c529_pos (not_le.mp h148).le h224 (not_le.mp h229).le hz2
                    · -- right
                      by_cases h230 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h231 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c424_pos (not_le.mp h224).le h199 (not_le.mp h220).le h231
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c426_pos (not_le.mp h224).le h199 (not_le.mp h231).le h230
                      · -- right
                        by_cases h232 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c437_pos (not_le.mp h224).le h199 (not_le.mp h230).le h232
                        · -- right
                          by_cases h233 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c496_pos (not_le.mp h224).le h199 (not_le.mp h232).le h233
                          · -- right
                            by_cases h234 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c530_pos (not_le.mp h224).le h199 (not_le.mp h233).le h234
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c531_pos (not_le.mp h224).le h199 (not_le.mp h234).le hz2
        · -- right
          by_cases h235 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h236 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h237 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h238 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c61_pos (not_le.mp h199).le h147 hz1 h238
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c63_pos (not_le.mp h199).le h147 (not_le.mp h238).le h237
              · -- right
                by_cases h239 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c66_pos (not_le.mp h199).le h147 (not_le.mp h237).le h239
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c67_pos (not_le.mp h199).le h147 (not_le.mp h239).le h236
            · -- right
              by_cases h240 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h241 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c70_pos (not_le.mp h199).le h147 (not_le.mp h236).le h241
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c71_pos (not_le.mp h199).le h147 (not_le.mp h241).le h240
              · -- right
                by_cases h242 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c73_pos (not_le.mp h199).le h147 (not_le.mp h240).le h242
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c75_pos (not_le.mp h199).le h147 (not_le.mp h242).le h235
          · -- right
            by_cases h243 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h244 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h245 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c100_pos (not_le.mp h199).le h147 (not_le.mp h235).le h245
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c102_pos (not_le.mp h199).le h147 (not_le.mp h245).le h244
              · -- right
                by_cases h246 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c106_pos (not_le.mp h199).le h147 (not_le.mp h244).le h246
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c110_pos (not_le.mp h199).le h147 (not_le.mp h246).le h243
            · -- right
              by_cases h247 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h248 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h249 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c171_pos (not_le.mp h199).le h147 (not_le.mp h243).le h249
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c173_pos (not_le.mp h199).le h147 (not_le.mp h249).le h248
                · -- right
                  by_cases h250 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c179_pos (not_le.mp h199).le h147 (not_le.mp h248).le h250
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c181_pos (not_le.mp h199).le h147 (not_le.mp h250).le h247
              · -- right
                by_cases h251 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h252 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h253 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B013.c275_pos (not_le.mp h199).le h147 (not_le.mp h247).le h253
                    · -- right
                      exact CKLaneC2R.Cells.S05.B013.c276_pos (not_le.mp h199).le h147 (not_le.mp h253).le h252
                  · -- right
                    by_cases h254 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c283_pos (not_le.mp h199).le h147 (not_le.mp h252).le h254
                    · -- right
                      exact CKLaneC2R.Cells.S05.B014.c284_pos (not_le.mp h199).le h147 (not_le.mp h254).le h251
                · -- right
                  by_cases h255 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h256 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h257 : a ≤ ((31077/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c363_pos (not_le.mp h199).le h257 (not_le.mp h251).le h256
                      · -- right
                        exact CKLaneC2R.Cells.S05.B018.c364_pos (not_le.mp h257).le h147 (not_le.mp h251).le h256
                    · -- right
                      by_cases h258 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c367_pos (not_le.mp h199).le h147 (not_le.mp h256).le h258
                      · -- right
                        by_cases h259 : a ≤ ((31077/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c419_pos (not_le.mp h199).le h259 (not_le.mp h258).le h255
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c420_pos (not_le.mp h259).le h147 (not_le.mp h258).le h255
                  · -- right
                    by_cases h260 : a ≤ ((31077/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h261 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h262 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c427_pos (not_le.mp h199).le h260 (not_le.mp h255).le h262
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c429_pos (not_le.mp h199).le h260 (not_le.mp h262).le h261
                      · -- right
                        by_cases h263 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c438_pos (not_le.mp h199).le h260 (not_le.mp h261).le h263
                        · -- right
                          by_cases h264 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c497_pos (not_le.mp h199).le h260 (not_le.mp h263).le h264
                          · -- right
                            by_cases h265 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c532_pos (not_le.mp h199).le h260 (not_le.mp h264).le h265
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c533_pos (not_le.mp h199).le h260 (not_le.mp h265).le hz2
                    · -- right
                      by_cases h266 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h267 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c428_pos (not_le.mp h260).le h147 (not_le.mp h255).le h267
                        · -- right
                          exact CKLaneC2R.Cells.S05.B021.c430_pos (not_le.mp h260).le h147 (not_le.mp h267).le h266
                      · -- right
                        by_cases h268 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B021.c439_pos (not_le.mp h260).le h147 (not_le.mp h266).le h268
                        · -- right
                          by_cases h269 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c498_pos (not_le.mp h260).le h147 (not_le.mp h268).le h269
                          · -- right
                            by_cases h270 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c534_pos (not_le.mp h260).le h147 (not_le.mp h269).le h270
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c535_pos (not_le.mp h260).le h147 (not_le.mp h270).le hz2
    · -- right
      by_cases h271 : a ≤ ((7893/8000 : ℚ) : ℝ)
      · -- left
        by_cases h272 : a ≤ ((15687/16000 : ℚ) : ℝ)
        · -- left
          by_cases h273 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h274 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h275 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h276 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h277 : a ≤ ((1251/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B006.c130_pos (not_le.mp h147).le h277 hz1 h276
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c131_pos (not_le.mp h277).le h272 hz1 h276
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c76_pos (not_le.mp h147).le h272 (not_le.mp h276).le h275
              · -- right
                by_cases h278 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B003.c77_pos (not_le.mp h147).le h272 (not_le.mp h275).le h278
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c78_pos (not_le.mp h147).le h272 (not_le.mp h278).le h274
            · -- right
              by_cases h279 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h280 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c81_pos (not_le.mp h147).le h272 (not_le.mp h274).le h280
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c82_pos (not_le.mp h147).le h272 (not_le.mp h280).le h279
              · -- right
                by_cases h281 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c85_pos (not_le.mp h147).le h272 (not_le.mp h279).le h281
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c86_pos (not_le.mp h147).le h272 (not_le.mp h281).le h273
          · -- right
            by_cases h282 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h283 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h284 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c111_pos (not_le.mp h147).le h272 (not_le.mp h273).le h284
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c112_pos (not_le.mp h147).le h272 (not_le.mp h284).le h283
              · -- right
                by_cases h285 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B005.c113_pos (not_le.mp h147).le h272 (not_le.mp h283).le h285
                · -- right
                  exact CKLaneC2R.Cells.S05.B005.c114_pos (not_le.mp h147).le h272 (not_le.mp h285).le h282
            · -- right
              by_cases h286 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h287 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h288 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c182_pos (not_le.mp h147).le h272 (not_le.mp h282).le h288
                  · -- right
                    exact CKLaneC2R.Cells.S05.B009.c183_pos (not_le.mp h147).le h272 (not_le.mp h288).le h287
                · -- right
                  by_cases h289 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c186_pos (not_le.mp h147).le h272 (not_le.mp h287).le h289
                  · -- right
                    by_cases h290 : a ≤ ((1251/1280 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c235_pos (not_le.mp h147).le h290 (not_le.mp h289).le h286
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c236_pos (not_le.mp h290).le h272 (not_le.mp h289).le h286
              · -- right
                by_cases h291 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h292 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h293 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c285_pos (not_le.mp h147).le h272 (not_le.mp h286).le h293
                    · -- right
                      exact CKLaneC2R.Cells.S05.B014.c286_pos (not_le.mp h147).le h272 (not_le.mp h293).le h292
                  · -- right
                    by_cases h294 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c289_pos (not_le.mp h147).le h272 (not_le.mp h292).le h294
                    · -- right
                      by_cases h295 : a ≤ ((1251/1280 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c343_pos (not_le.mp h147).le h295 (not_le.mp h294).le h291
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c344_pos (not_le.mp h295).le h272 (not_le.mp h294).le h291
                · -- right
                  by_cases h296 : a ≤ ((1251/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h297 : z ≤ ((6211/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h298 : z ≤ ((61197/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c371_pos (not_le.mp h147).le h296 (not_le.mp h291).le h298
                      · -- right
                        by_cases h299 : z ≤ ((123307/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c440_pos (not_le.mp h147).le h296 (not_le.mp h298).le h299
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c441_pos (not_le.mp h147).le h296 (not_le.mp h299).le h297
                    · -- right
                      by_cases h300 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h301 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c455_pos (not_le.mp h147).le h296 (not_le.mp h297).le h301
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c457_pos (not_le.mp h147).le h296 (not_le.mp h301).le h300
                      · -- right
                        by_cases h302 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h303 : z ≤ ((50601/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c515_pos (not_le.mp h147).le h296 (not_le.mp h300).le h303
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c516_pos (not_le.mp h147).le h296 (not_le.mp h303).le h302
                        · -- right
                          by_cases h304 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c519_pos (not_le.mp h147).le h296 (not_le.mp h302).le h304
                          · -- right
                            by_cases h305 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c549_pos (not_le.mp h147).le h296 (not_le.mp h304).le h305
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c550_pos (not_le.mp h147).le h296 (not_le.mp h305).le hz2
                  · -- right
                    by_cases h306 : z ≤ ((6211/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h307 : z ≤ ((61197/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c372_pos (not_le.mp h296).le h272 (not_le.mp h291).le h307
                      · -- right
                        by_cases h308 : z ≤ ((123307/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c442_pos (not_le.mp h296).le h272 (not_le.mp h307).le h308
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c443_pos (not_le.mp h296).le h272 (not_le.mp h308).le h306
                    · -- right
                      by_cases h309 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h310 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c456_pos (not_le.mp h296).le h272 (not_le.mp h306).le h310
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c458_pos (not_le.mp h296).le h272 (not_le.mp h310).le h309
                      · -- right
                        by_cases h311 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h312 : z ≤ ((50601/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c517_pos (not_le.mp h296).le h272 (not_le.mp h309).le h312
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c518_pos (not_le.mp h296).le h272 (not_le.mp h312).le h311
                        · -- right
                          by_cases h313 : z ≤ ((254831/256000 : ℚ) : ℝ)
                          · -- left
                            by_cases h314 : a ≤ ((62649/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c547_pos (not_le.mp h296).le h314 (not_le.mp h311).le h313
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c548_pos (not_le.mp h314).le h272 (not_le.mp h311).le h313
                          · -- right
                            by_cases h315 : z ≤ ((20423/20480 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c551_pos (not_le.mp h296).le h272 (not_le.mp h313).le h315
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c552_pos (not_le.mp h296).le h272 (not_le.mp h315).le hz2
        · -- right
          by_cases h316 : a ≤ ((31473/32000 : ℚ) : ℝ)
          · -- left
            by_cases h317 : z ≤ ((217/400 : ℚ) : ℝ)
            · -- left
              by_cases h318 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h319 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h320 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B006.c132_pos (not_le.mp h272).le h316 hz1 h320
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c134_pos (not_le.mp h272).le h316 (not_le.mp h320).le h319
                · -- right
                  exact CKLaneC2R.Cells.S05.B003.c79_pos (not_le.mp h272).le h316 (not_le.mp h319).le h318
              · -- right
                by_cases h321 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c83_pos (not_le.mp h272).le h316 (not_le.mp h318).le h321
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c87_pos (not_le.mp h272).le h316 (not_le.mp h321).le h317
            · -- right
              by_cases h322 : z ≤ ((3083/4000 : ℚ) : ℝ)
              · -- left
                by_cases h323 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h324 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c149_pos (not_le.mp h272).le h316 (not_le.mp h317).le h324
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c151_pos (not_le.mp h272).le h316 (not_le.mp h324).le h323
                · -- right
                  by_cases h325 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c153_pos (not_le.mp h272).le h316 (not_le.mp h323).le h325
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c155_pos (not_le.mp h272).le h316 (not_le.mp h325).le h322
              · -- right
                by_cases h326 : z ≤ ((7079/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h327 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c184_pos (not_le.mp h272).le h316 (not_le.mp h322).le h327
                  · -- right
                    by_cases h328 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c233_pos (not_le.mp h272).le h316 (not_le.mp h327).le h328
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c237_pos (not_le.mp h272).le h316 (not_le.mp h328).le h326
                · -- right
                  by_cases h329 : z ≤ ((15071/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h330 : z ≤ ((29229/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c287_pos (not_le.mp h272).le h316 (not_le.mp h326).le h330
                    · -- right
                      by_cases h331 : z ≤ ((59371/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c345_pos (not_le.mp h272).le h316 (not_le.mp h330).le h331
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c347_pos (not_le.mp h272).le h316 (not_le.mp h331).le h329
                  · -- right
                    by_cases h332 : z ≤ ((6211/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h333 : z ≤ ((61197/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c373_pos (not_le.mp h272).le h316 (not_le.mp h329).le h333
                      · -- right
                        by_cases h334 : z ≤ ((123307/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c444_pos (not_le.mp h272).le h316 (not_le.mp h333).le h334
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c445_pos (not_le.mp h272).le h316 (not_le.mp h334).le h332
                    · -- right
                      by_cases h335 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h336 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c459_pos (not_le.mp h272).le h316 (not_le.mp h332).le h336
                        · -- right
                          by_cases h337 : z ≤ ((251179/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c511_pos (not_le.mp h272).le h316 (not_le.mp h336).le h337
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c512_pos (not_le.mp h272).le h316 (not_le.mp h337).le h335
                      · -- right
                        by_cases h338 : z ≤ ((126959/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h339 : z ≤ ((50601/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c520_pos (not_le.mp h272).le h316 (not_le.mp h335).le h339
                          · -- right
                            by_cases h340 : a ≤ ((62847/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c553_pos (not_le.mp h272).le h340 (not_le.mp h339).le h338
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c554_pos (not_le.mp h340).le h316 (not_le.mp h339).le h338
                        · -- right
                          by_cases h341 : a ≤ ((62847/64000 : ℚ) : ℝ)
                          · -- left
                            by_cases h342 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c559_pos (not_le.mp h272).le h341 (not_le.mp h338).le h342
                            · -- right
                              by_cases h343 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c585_pos (not_le.mp h272).le h341 (not_le.mp h342).le h343
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c587_pos (not_le.mp h272).le h341 (not_le.mp h343).le hz2
                          · -- right
                            by_cases h344 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c560_pos (not_le.mp h341).le h316 (not_le.mp h338).le h344
                            · -- right
                              by_cases h345 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c586_pos (not_le.mp h341).le h316 (not_le.mp h344).le h345
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c588_pos (not_le.mp h341).le h316 (not_le.mp h345).le hz2
          · -- right
            by_cases h346 : z ≤ ((217/400 : ℚ) : ℝ)
            · -- left
              by_cases h347 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h348 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h349 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B006.c133_pos (not_le.mp h316).le h271 hz1 h349
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c135_pos (not_le.mp h316).le h271 (not_le.mp h349).le h348
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c80_pos (not_le.mp h316).le h271 (not_le.mp h348).le h347
              · -- right
                by_cases h350 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c84_pos (not_le.mp h316).le h271 (not_le.mp h347).le h350
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c88_pos (not_le.mp h316).le h271 (not_le.mp h350).le h346
            · -- right
              by_cases h351 : z ≤ ((3083/4000 : ℚ) : ℝ)
              · -- left
                by_cases h352 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h353 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c150_pos (not_le.mp h316).le h271 (not_le.mp h346).le h353
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c152_pos (not_le.mp h316).le h271 (not_le.mp h353).le h352
                · -- right
                  by_cases h354 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c154_pos (not_le.mp h316).le h271 (not_le.mp h352).le h354
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c156_pos (not_le.mp h316).le h271 (not_le.mp h354).le h351
              · -- right
                by_cases h355 : z ≤ ((7079/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h356 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B009.c185_pos (not_le.mp h316).le h271 (not_le.mp h351).le h356
                  · -- right
                    by_cases h357 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c234_pos (not_le.mp h316).le h271 (not_le.mp h356).le h357
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c238_pos (not_le.mp h316).le h271 (not_le.mp h357).le h355
                · -- right
                  by_cases h358 : z ≤ ((15071/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h359 : z ≤ ((29229/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B014.c288_pos (not_le.mp h316).le h271 (not_le.mp h355).le h359
                    · -- right
                      by_cases h360 : z ≤ ((59371/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c346_pos (not_le.mp h316).le h271 (not_le.mp h359).le h360
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c348_pos (not_le.mp h316).le h271 (not_le.mp h360).le h358
                  · -- right
                    by_cases h361 : z ≤ ((6211/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h362 : z ≤ ((61197/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B018.c374_pos (not_le.mp h316).le h271 (not_le.mp h358).le h362
                      · -- right
                        by_cases h363 : z ≤ ((123307/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c446_pos (not_le.mp h316).le h271 (not_le.mp h362).le h363
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c447_pos (not_le.mp h316).le h271 (not_le.mp h363).le h361
                    · -- right
                      by_cases h364 : z ≤ ((63023/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h365 : z ≤ ((125133/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B023.c460_pos (not_le.mp h316).le h271 (not_le.mp h361).le h365
                        · -- right
                          by_cases h366 : z ≤ ((251179/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c513_pos (not_le.mp h316).le h271 (not_le.mp h365).le h366
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c514_pos (not_le.mp h316).le h271 (not_le.mp h366).le h364
                      · -- right
                        by_cases h367 : a ≤ ((12609/12800 : ℚ) : ℝ)
                        · -- left
                          by_cases h368 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h369 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c555_pos (not_le.mp h316).le h367 (not_le.mp h364).le h369
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c557_pos (not_le.mp h316).le h367 (not_le.mp h369).le h368
                          · -- right
                            by_cases h370 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c561_pos (not_le.mp h316).le h367 (not_le.mp h368).le h370
                            · -- right
                              by_cases h371 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c589_pos (not_le.mp h316).le h367 (not_le.mp h370).le h371
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c590_pos (not_le.mp h316).le h367 (not_le.mp h371).le hz2
                        · -- right
                          by_cases h372 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h373 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c556_pos (not_le.mp h367).le h271 (not_le.mp h364).le h373
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c558_pos (not_le.mp h367).le h271 (not_le.mp h373).le h372
                          · -- right
                            by_cases h374 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c562_pos (not_le.mp h367).le h271 (not_le.mp h372).le h374
                            · -- right
                              by_cases h375 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c591_pos (not_le.mp h367).le h271 (not_le.mp h374).le h375
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c592_pos (not_le.mp h367).le h271 (not_le.mp h375).le hz2
      · -- right
        by_cases h376 : a ≤ ((3177/3200 : ℚ) : ℝ)
        · -- left
          by_cases h377 : a ≤ ((31671/32000 : ℚ) : ℝ)
          · -- left
            by_cases h378 : z ≤ ((217/400 : ℚ) : ℝ)
            · -- left
              by_cases h379 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h380 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h381 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h382 : a ≤ ((63243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c203_pos (not_le.mp h271).le h382 hz1 h381
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c204_pos (not_le.mp h382).le h377 hz1 h381
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c136_pos (not_le.mp h271).le h377 (not_le.mp h381).le h380
                · -- right
                  by_cases h383 : a ≤ ((63243/64000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B006.c137_pos (not_le.mp h271).le h383 (not_le.mp h380).le h379
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c138_pos (not_le.mp h383).le h377 (not_le.mp h380).le h379
              · -- right
                by_cases h384 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S05.B004.c89_pos (not_le.mp h271).le h377 (not_le.mp h379).le h384
                · -- right
                  exact CKLaneC2R.Cells.S05.B004.c90_pos (not_le.mp h271).le h377 (not_le.mp h384).le h378
            · -- right
              by_cases h385 : z ≤ ((3083/4000 : ℚ) : ℝ)
              · -- left
                by_cases h386 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h387 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c157_pos (not_le.mp h271).le h377 (not_le.mp h378).le h387
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c158_pos (not_le.mp h271).le h377 (not_le.mp h387).le h386
                · -- right
                  by_cases h388 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c161_pos (not_le.mp h271).le h377 (not_le.mp h386).le h388
                  · -- right
                    exact CKLaneC2R.Cells.S05.B008.c162_pos (not_le.mp h271).le h377 (not_le.mp h388).le h385
              · -- right
                by_cases h389 : z ≤ ((7079/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h390 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h391 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c239_pos (not_le.mp h271).le h377 (not_le.mp h385).le h391
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c240_pos (not_le.mp h271).le h377 (not_le.mp h391).le h390
                  · -- right
                    by_cases h392 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c243_pos (not_le.mp h271).le h377 (not_le.mp h390).le h392
                    · -- right
                      exact CKLaneC2R.Cells.S05.B012.c244_pos (not_le.mp h271).le h377 (not_le.mp h392).le h389
                · -- right
                  by_cases h393 : z ≤ ((15071/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h394 : z ≤ ((29229/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h395 : z ≤ ((11509/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c349_pos (not_le.mp h271).le h377 (not_le.mp h389).le h395
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c350_pos (not_le.mp h271).le h377 (not_le.mp h395).le h394
                    · -- right
                      by_cases h396 : z ≤ ((59371/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c353_pos (not_le.mp h271).le h377 (not_le.mp h394).le h396
                      · -- right
                        exact CKLaneC2R.Cells.S05.B017.c354_pos (not_le.mp h271).le h377 (not_le.mp h396).le h393
                  · -- right
                    by_cases h397 : z ≤ ((6211/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h398 : z ≤ ((61197/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h399 : z ≤ ((121481/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c448_pos (not_le.mp h271).le h377 (not_le.mp h393).le h399
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c449_pos (not_le.mp h271).le h377 (not_le.mp h399).le h398
                      · -- right
                        by_cases h400 : z ≤ ((123307/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c452_pos (not_le.mp h271).le h377 (not_le.mp h398).le h400
                        · -- right
                          exact CKLaneC2R.Cells.S05.B022.c453_pos (not_le.mp h271).le h377 (not_le.mp h400).le h397
                    · -- right
                      by_cases h401 : a ≤ ((63243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h402 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h403 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c521_pos (not_le.mp h271).le h401 (not_le.mp h397).le h403
                          · -- right
                            exact CKLaneC2R.Cells.S05.B026.c525_pos (not_le.mp h271).le h401 (not_le.mp h403).le h402
                        · -- right
                          by_cases h404 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h405 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c574_pos (not_le.mp h271).le h401 (not_le.mp h402).le h405
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c576_pos (not_le.mp h271).le h401 (not_le.mp h405).le h404
                          · -- right
                            by_cases h406 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B029.c581_pos (not_le.mp h271).le h401 (not_le.mp h404).le h406
                            · -- right
                              by_cases h407 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c608_pos (not_le.mp h271).le h401 (not_le.mp h406).le h407
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c609_pos (not_le.mp h271).le h401 (not_le.mp h407).le hz2
                      · -- right
                        by_cases h408 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h409 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c522_pos (not_le.mp h401).le h377 (not_le.mp h397).le h409
                          · -- right
                            exact CKLaneC2R.Cells.S05.B026.c526_pos (not_le.mp h401).le h377 (not_le.mp h409).le h408
                        · -- right
                          by_cases h410 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h411 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c575_pos (not_le.mp h401).le h377 (not_le.mp h408).le h411
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c577_pos (not_le.mp h401).le h377 (not_le.mp h411).le h410
                          · -- right
                            by_cases h412 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              by_cases h413 : z ≤ ((508749/512000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c606_pos (not_le.mp h401).le h377 (not_le.mp h410).le h413
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c607_pos (not_le.mp h401).le h377 (not_le.mp h413).le h412
                            · -- right
                              by_cases h414 : z ≤ ((20423/20480 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c610_pos (not_le.mp h401).le h377 (not_le.mp h412).le h414
                              · -- right
                                by_cases h415 : a ≤ ((25317/25600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c628_pos (not_le.mp h401).le h415 (not_le.mp h414).le hz2
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c629_pos (not_le.mp h415).le h377 (not_le.mp h414).le hz2
          · -- right
            by_cases h416 : a ≤ ((63441/64000 : ℚ) : ℝ)
            · -- left
              by_cases h417 : z ≤ ((217/400 : ℚ) : ℝ)
              · -- left
                by_cases h418 : z ≤ ((1257/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h419 : z ≤ ((1601/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h420 : z ≤ ((2289/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c205_pos (not_le.mp h377).le h416 hz1 h420
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c207_pos (not_le.mp h377).le h416 (not_le.mp h420).le h419
                  · -- right
                    exact CKLaneC2R.Cells.S05.B006.c139_pos (not_le.mp h377).le h416 (not_le.mp h419).le h418
                · -- right
                  by_cases h421 : z ≤ ((3427/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c141_pos (not_le.mp h377).le h416 (not_le.mp h418).le h421
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c143_pos (not_le.mp h377).le h416 (not_le.mp h421).le h417
              · -- right
                by_cases h422 : z ≤ ((3083/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h423 : z ≤ ((5253/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c159_pos (not_le.mp h377).le h416 (not_le.mp h417).le h423
                  · -- right
                    by_cases h424 : z ≤ ((11419/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c221_pos (not_le.mp h377).le h416 (not_le.mp h423).le h424
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c223_pos (not_le.mp h377).le h416 (not_le.mp h424).le h422
                · -- right
                  by_cases h425 : z ≤ ((7079/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h426 : z ≤ ((2649/3200 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c241_pos (not_le.mp h377).le h416 (not_le.mp h422).le h426
                    · -- right
                      by_cases h427 : z ≤ ((27403/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c320_pos (not_le.mp h377).le h416 (not_le.mp h426).le h427
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c322_pos (not_le.mp h377).le h416 (not_le.mp h427).le h425
                  · -- right
                    by_cases h428 : z ≤ ((15071/16000 : ℚ) : ℝ)
                    · -- left
                      by_cases h429 : z ≤ ((29229/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c351_pos (not_le.mp h377).le h416 (not_le.mp h425).le h429
                      · -- right
                        by_cases h430 : z ≤ ((59371/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c409_pos (not_le.mp h377).le h416 (not_le.mp h429).le h430
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c411_pos (not_le.mp h377).le h416 (not_le.mp h430).le h428
                    · -- right
                      by_cases h431 : z ≤ ((6211/6400 : ℚ) : ℝ)
                      · -- left
                        by_cases h432 : z ≤ ((61197/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c450_pos (not_le.mp h377).le h416 (not_le.mp h428).le h432
                        · -- right
                          by_cases h433 : z ≤ ((123307/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c499_pos (not_le.mp h377).le h416 (not_le.mp h432).le h433
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c501_pos (not_le.mp h377).le h416 (not_le.mp h433).le h431
                      · -- right
                        by_cases h434 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h435 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c523_pos (not_le.mp h377).le h416 (not_le.mp h431).le h435
                          · -- right
                            by_cases h436 : z ≤ ((251179/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c563_pos (not_le.mp h377).le h416 (not_le.mp h435).le h436
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c564_pos (not_le.mp h377).le h416 (not_le.mp h436).le h434
                        · -- right
                          by_cases h437 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h438 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c578_pos (not_le.mp h377).le h416 (not_le.mp h434).le h438
                            · -- right
                              exact CKLaneC2R.Cells.S05.B029.c580_pos (not_le.mp h377).le h416 (not_le.mp h438).le h437
                          · -- right
                            by_cases h439 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              by_cases h440 : z ≤ ((508749/512000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c611_pos (not_le.mp h377).le h416 (not_le.mp h437).le h440
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c612_pos (not_le.mp h377).le h416 (not_le.mp h440).le h439
                            · -- right
                              by_cases h441 : a ≤ ((126783/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h442 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c632_pos (not_le.mp h377).le h441 (not_le.mp h439).le h442
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c634_pos (not_le.mp h377).le h441 (not_le.mp h442).le hz2
                              · -- right
                                by_cases h443 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c633_pos (not_le.mp h441).le h416 (not_le.mp h439).le h443
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c635_pos (not_le.mp h441).le h416 (not_le.mp h443).le hz2
            · -- right
              by_cases h444 : z ≤ ((217/400 : ℚ) : ℝ)
              · -- left
                by_cases h445 : z ≤ ((1257/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h446 : z ≤ ((1601/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h447 : z ≤ ((2289/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c206_pos (not_le.mp h416).le h376 hz1 h447
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c208_pos (not_le.mp h416).le h376 (not_le.mp h447).le h446
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c140_pos (not_le.mp h416).le h376 (not_le.mp h446).le h445
                · -- right
                  by_cases h448 : z ≤ ((3427/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c142_pos (not_le.mp h416).le h376 (not_le.mp h445).le h448
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c144_pos (not_le.mp h416).le h376 (not_le.mp h448).le h444
              · -- right
                by_cases h449 : z ≤ ((3083/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h450 : z ≤ ((5253/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c160_pos (not_le.mp h416).le h376 (not_le.mp h444).le h450
                  · -- right
                    by_cases h451 : z ≤ ((11419/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c222_pos (not_le.mp h416).le h376 (not_le.mp h450).le h451
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c224_pos (not_le.mp h416).le h376 (not_le.mp h451).le h449
                · -- right
                  by_cases h452 : z ≤ ((7079/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h453 : z ≤ ((2649/3200 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c242_pos (not_le.mp h416).le h376 (not_le.mp h449).le h453
                    · -- right
                      by_cases h454 : z ≤ ((27403/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c321_pos (not_le.mp h416).le h376 (not_le.mp h453).le h454
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c323_pos (not_le.mp h416).le h376 (not_le.mp h454).le h452
                  · -- right
                    by_cases h455 : z ≤ ((15071/16000 : ℚ) : ℝ)
                    · -- left
                      by_cases h456 : z ≤ ((29229/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c352_pos (not_le.mp h416).le h376 (not_le.mp h452).le h456
                      · -- right
                        by_cases h457 : z ≤ ((59371/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c410_pos (not_le.mp h416).le h376 (not_le.mp h456).le h457
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c412_pos (not_le.mp h416).le h376 (not_le.mp h457).le h455
                    · -- right
                      by_cases h458 : z ≤ ((6211/6400 : ℚ) : ℝ)
                      · -- left
                        by_cases h459 : z ≤ ((61197/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c451_pos (not_le.mp h416).le h376 (not_le.mp h455).le h459
                        · -- right
                          by_cases h460 : z ≤ ((123307/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c500_pos (not_le.mp h416).le h376 (not_le.mp h459).le h460
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c502_pos (not_le.mp h416).le h376 (not_le.mp h460).le h458
                      · -- right
                        by_cases h461 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h462 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c524_pos (not_le.mp h416).le h376 (not_le.mp h458).le h462
                          · -- right
                            by_cases h463 : z ≤ ((251179/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c565_pos (not_le.mp h416).le h376 (not_le.mp h462).le h463
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c566_pos (not_le.mp h416).le h376 (not_le.mp h463).le h461
                        · -- right
                          by_cases h464 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h465 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c579_pos (not_le.mp h416).le h376 (not_le.mp h461).le h465
                            · -- right
                              by_cases h466 : z ≤ ((506923/512000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c604_pos (not_le.mp h416).le h376 (not_le.mp h465).le h466
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c605_pos (not_le.mp h416).le h376 (not_le.mp h466).le h464
                          · -- right
                            by_cases h467 : z ≤ ((254831/256000 : ℚ) : ℝ)
                            · -- left
                              by_cases h468 : z ≤ ((508749/512000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c613_pos (not_le.mp h416).le h376 (not_le.mp h464).le h468
                              · -- right
                                by_cases h469 : a ≤ ((126981/128000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c630_pos (not_le.mp h416).le h469 (not_le.mp h468).le h467
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c631_pos (not_le.mp h469).le h376 (not_le.mp h468).le h467
                            · -- right
                              by_cases h470 : a ≤ ((126981/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h471 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c636_pos (not_le.mp h416).le h470 (not_le.mp h467).le h471
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c638_pos (not_le.mp h416).le h470 (not_le.mp h471).le hz2
                              · -- right
                                by_cases h472 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c637_pos (not_le.mp h470).le h376 (not_le.mp h467).le h472
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c639_pos (not_le.mp h470).le h376 (not_le.mp h472).le hz2
        · -- right
          by_cases h473 : a ≤ ((31869/32000 : ℚ) : ℝ)
          · -- left
            by_cases h474 : a ≤ ((63639/64000 : ℚ) : ℝ)
            · -- left
              by_cases h475 : z ≤ ((217/400 : ℚ) : ℝ)
              · -- left
                by_cases h476 : z ≤ ((1257/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h477 : z ≤ ((1601/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h478 : z ≤ ((2289/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c209_pos (not_le.mp h376).le h474 hz1 h478
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c210_pos (not_le.mp h376).le h474 (not_le.mp h478).le h477
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c145_pos (not_le.mp h376).le h474 (not_le.mp h477).le h476
                · -- right
                  by_cases h479 : z ≤ ((3427/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B007.c146_pos (not_le.mp h376).le h474 (not_le.mp h476).le h479
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c147_pos (not_le.mp h376).le h474 (not_le.mp h479).le h475
              · -- right
                by_cases h480 : z ≤ ((3083/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h481 : z ≤ ((5253/8000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S05.B008.c163_pos (not_le.mp h376).le h474 (not_le.mp h475).le h481
                  · -- right
                    by_cases h482 : z ≤ ((11419/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c227_pos (not_le.mp h376).le h474 (not_le.mp h481).le h482
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c228_pos (not_le.mp h376).le h474 (not_le.mp h482).le h480
                · -- right
                  by_cases h483 : z ≤ ((7079/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h484 : z ≤ ((2649/3200 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c245_pos (not_le.mp h376).le h474 (not_le.mp h480).le h484
                    · -- right
                      by_cases h485 : z ≤ ((27403/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c324_pos (not_le.mp h376).le h474 (not_le.mp h484).le h485
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c325_pos (not_le.mp h376).le h474 (not_le.mp h485).le h483
                  · -- right
                    by_cases h486 : z ≤ ((15071/16000 : ℚ) : ℝ)
                    · -- left
                      by_cases h487 : z ≤ ((29229/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c355_pos (not_le.mp h376).le h474 (not_le.mp h483).le h487
                      · -- right
                        by_cases h488 : z ≤ ((59371/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c413_pos (not_le.mp h376).le h474 (not_le.mp h487).le h488
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c414_pos (not_le.mp h376).le h474 (not_le.mp h488).le h486
                    · -- right
                      by_cases h489 : z ≤ ((6211/6400 : ℚ) : ℝ)
                      · -- left
                        by_cases h490 : z ≤ ((61197/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B022.c454_pos (not_le.mp h376).le h474 (not_le.mp h486).le h490
                        · -- right
                          by_cases h491 : z ≤ ((123307/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c505_pos (not_le.mp h376).le h474 (not_le.mp h490).le h491
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c506_pos (not_le.mp h376).le h474 (not_le.mp h491).le h489
                      · -- right
                        by_cases h492 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h493 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B026.c527_pos (not_le.mp h376).le h474 (not_le.mp h489).le h493
                          · -- right
                            by_cases h494 : z ≤ ((251179/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c569_pos (not_le.mp h376).le h474 (not_le.mp h493).le h494
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c570_pos (not_le.mp h376).le h474 (not_le.mp h494).le h492
                        · -- right
                          by_cases h495 : z ≤ ((126959/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h496 : z ≤ ((50601/51200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B029.c582_pos (not_le.mp h376).le h474 (not_le.mp h492).le h496
                            · -- right
                              by_cases h497 : a ≤ ((127179/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c616_pos (not_le.mp h376).le h497 (not_le.mp h496).le h495
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c617_pos (not_le.mp h497).le h474 (not_le.mp h496).le h495
                          · -- right
                            by_cases h498 : a ≤ ((127179/128000 : ℚ) : ℝ)
                            · -- left
                              by_cases h499 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h500 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c651_pos (not_le.mp h376).le h498 (not_le.mp h495).le h500
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c653_pos (not_le.mp h376).le h498 (not_le.mp h500).le h499
                              · -- right
                                by_cases h501 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c659_pos (not_le.mp h376).le h498 (not_le.mp h499).le h501
                                · -- right
                                  by_cases h502 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c667_pos (not_le.mp h376).le h498 (not_le.mp h501).le h502
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c668_pos (not_le.mp h376).le h498 (not_le.mp h502).le hz2
                            · -- right
                              by_cases h503 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h504 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c652_pos (not_le.mp h498).le h474 (not_le.mp h495).le h504
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c654_pos (not_le.mp h498).le h474 (not_le.mp h504).le h503
                              · -- right
                                by_cases h505 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B033.c660_pos (not_le.mp h498).le h474 (not_le.mp h503).le h505
                                · -- right
                                  by_cases h506 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c669_pos (not_le.mp h498).le h474 (not_le.mp h505).le h506
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c670_pos (not_le.mp h498).le h474 (not_le.mp h506).le hz2
            · -- right
              by_cases h507 : z ≤ ((217/400 : ℚ) : ℝ)
              · -- left
                by_cases h508 : z ≤ ((1257/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h509 : a ≤ ((127377/128000 : ℚ) : ℝ)
                  · -- left
                    by_cases h510 : z ≤ ((1601/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h511 : z ≤ ((2289/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B014.c292_pos (not_le.mp h474).le h509 hz1 h511
                      · -- right
                        exact CKLaneC2R.Cells.S05.B014.c294_pos (not_le.mp h474).le h509 (not_le.mp h511).le h510
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c211_pos (not_le.mp h474).le h509 (not_le.mp h510).le h508
                  · -- right
                    by_cases h512 : z ≤ ((1601/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h513 : z ≤ ((2289/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B014.c293_pos (not_le.mp h509).le h473 hz1 h513
                      · -- right
                        exact CKLaneC2R.Cells.S05.B014.c295_pos (not_le.mp h509).le h473 (not_le.mp h513).le h512
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c212_pos (not_le.mp h509).le h473 (not_le.mp h512).le h508
                · -- right
                  by_cases h514 : z ≤ ((3427/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h515 : a ≤ ((127377/128000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c215_pos (not_le.mp h474).le h515 (not_le.mp h508).le h514
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c216_pos (not_le.mp h515).le h473 (not_le.mp h508).le h514
                  · -- right
                    exact CKLaneC2R.Cells.S05.B007.c148_pos (not_le.mp h474).le h473 (not_le.mp h514).le h507
              · -- right
                by_cases h516 : z ≤ ((3083/4000 : ℚ) : ℝ)
                · -- left
                  by_cases h517 : z ≤ ((5253/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h518 : a ≤ ((127377/128000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c225_pos (not_le.mp h474).le h518 (not_le.mp h507).le h517
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c226_pos (not_le.mp h518).le h473 (not_le.mp h507).le h517
                  · -- right
                    by_cases h519 : z ≤ ((11419/16000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c229_pos (not_le.mp h474).le h473 (not_le.mp h517).le h519
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c230_pos (not_le.mp h474).le h473 (not_le.mp h519).le h516
                · -- right
                  by_cases h520 : z ≤ ((7079/8000 : ℚ) : ℝ)
                  · -- left
                    by_cases h521 : z ≤ ((2649/3200 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B012.c246_pos (not_le.mp h474).le h473 (not_le.mp h516).le h521
                    · -- right
                      by_cases h522 : z ≤ ((27403/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c326_pos (not_le.mp h474).le h473 (not_le.mp h521).le h522
                      · -- right
                        exact CKLaneC2R.Cells.S05.B016.c327_pos (not_le.mp h474).le h473 (not_le.mp h522).le h520
                  · -- right
                    by_cases h523 : z ≤ ((15071/16000 : ℚ) : ℝ)
                    · -- left
                      by_cases h524 : z ≤ ((29229/32000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B017.c356_pos (not_le.mp h474).le h473 (not_le.mp h520).le h524
                      · -- right
                        by_cases h525 : z ≤ ((59371/64000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c415_pos (not_le.mp h474).le h473 (not_le.mp h524).le h525
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c416_pos (not_le.mp h474).le h473 (not_le.mp h525).le h523
                    · -- right
                      by_cases h526 : z ≤ ((6211/6400 : ℚ) : ℝ)
                      · -- left
                        by_cases h527 : z ≤ ((61197/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h528 : a ≤ ((127377/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c503_pos (not_le.mp h474).le h528 (not_le.mp h523).le h527
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c504_pos (not_le.mp h528).le h473 (not_le.mp h523).le h527
                        · -- right
                          by_cases h529 : z ≤ ((123307/128000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c507_pos (not_le.mp h474).le h473 (not_le.mp h527).le h529
                          · -- right
                            exact CKLaneC2R.Cells.S05.B025.c508_pos (not_le.mp h474).le h473 (not_le.mp h529).le h526
                      · -- right
                        by_cases h530 : z ≤ ((63023/64000 : ℚ) : ℝ)
                        · -- left
                          by_cases h531 : z ≤ ((125133/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h532 : a ≤ ((127377/128000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c567_pos (not_le.mp h474).le h532 (not_le.mp h526).le h531
                            · -- right
                              exact CKLaneC2R.Cells.S05.B028.c568_pos (not_le.mp h532).le h473 (not_le.mp h526).le h531
                          · -- right
                            by_cases h533 : z ≤ ((251179/256000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c571_pos (not_le.mp h474).le h473 (not_le.mp h531).le h533
                            · -- right
                              by_cases h534 : a ≤ ((127377/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c593_pos (not_le.mp h474).le h534 (not_le.mp h533).le h530
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c594_pos (not_le.mp h534).le h473 (not_le.mp h533).le h530
                        · -- right
                          by_cases h535 : a ≤ ((127377/128000 : ℚ) : ℝ)
                          · -- left
                            by_cases h536 : z ≤ ((126959/128000 : ℚ) : ℝ)
                            · -- left
                              by_cases h537 : z ≤ ((50601/51200 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c614_pos (not_le.mp h474).le h535 (not_le.mp h530).le h537
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c618_pos (not_le.mp h474).le h535 (not_le.mp h537).le h536
                            · -- right
                              by_cases h538 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h539 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c655_pos (not_le.mp h474).le h535 (not_le.mp h536).le h539
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c657_pos (not_le.mp h474).le h535 (not_le.mp h539).le h538
                              · -- right
                                by_cases h540 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B033.c661_pos (not_le.mp h474).le h535 (not_le.mp h538).le h540
                                · -- right
                                  by_cases h541 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c673_pos (not_le.mp h474).le h535 (not_le.mp h540).le h541
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c674_pos (not_le.mp h474).le h535 (not_le.mp h541).le hz2
                          · -- right
                            by_cases h542 : z ≤ ((126959/128000 : ℚ) : ℝ)
                            · -- left
                              by_cases h543 : z ≤ ((50601/51200 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c615_pos (not_le.mp h535).le h473 (not_le.mp h530).le h543
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c619_pos (not_le.mp h535).le h473 (not_le.mp h543).le h542
                            · -- right
                              by_cases h544 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h545 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c656_pos (not_le.mp h535).le h473 (not_le.mp h542).le h545
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c658_pos (not_le.mp h535).le h473 (not_le.mp h545).le h544
                              · -- right
                                by_cases h546 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  by_cases h547 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c671_pos (not_le.mp h535).le h473 (not_le.mp h544).le h547
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c672_pos (not_le.mp h535).le h473 (not_le.mp h547).le h546
                                · -- right
                                  by_cases h548 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c675_pos (not_le.mp h535).le h473 (not_le.mp h546).le h548
                                  · -- right
                                    by_cases h549 : a ≤ ((254853/256000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c688_pos (not_le.mp h535).le h549 (not_le.mp h548).le hz2
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B034.c689_pos (not_le.mp h549).le h473 (not_le.mp h548).le hz2
          · -- right
            by_cases h550 : a ≤ ((63837/64000 : ℚ) : ℝ)
            · -- left
              by_cases h551 : a ≤ ((5103/5120 : ℚ) : ℝ)
              · -- left
                by_cases h552 : z ≤ ((217/400 : ℚ) : ℝ)
                · -- left
                  by_cases h553 : z ≤ ((1257/4000 : ℚ) : ℝ)
                  · -- left
                    by_cases h554 : z ≤ ((1601/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h555 : z ≤ ((2289/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B014.c296_pos (not_le.mp h473).le h551 hz1 h555
                      · -- right
                        exact CKLaneC2R.Cells.S05.B014.c297_pos (not_le.mp h473).le h551 (not_le.mp h555).le h554
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c213_pos (not_le.mp h473).le h551 (not_le.mp h554).le h553
                  · -- right
                    by_cases h556 : z ≤ ((3427/8000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c217_pos (not_le.mp h473).le h551 (not_le.mp h553).le h556
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c219_pos (not_le.mp h473).le h551 (not_le.mp h556).le h552
                · -- right
                  by_cases h557 : z ≤ ((3083/4000 : ℚ) : ℝ)
                  · -- left
                    by_cases h558 : z ≤ ((5253/8000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c231_pos (not_le.mp h473).le h551 (not_le.mp h552).le h558
                    · -- right
                      by_cases h559 : z ≤ ((11419/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c309_pos (not_le.mp h473).le h551 (not_le.mp h558).le h559
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c310_pos (not_le.mp h473).le h551 (not_le.mp h559).le h557
                  · -- right
                    by_cases h560 : z ≤ ((7079/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h561 : z ≤ ((2649/3200 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c328_pos (not_le.mp h473).le h551 (not_le.mp h557).le h561
                      · -- right
                        by_cases h562 : z ≤ ((27403/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c389_pos (not_le.mp h473).le h551 (not_le.mp h561).le h562
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c390_pos (not_le.mp h473).le h551 (not_le.mp h562).le h560
                    · -- right
                      by_cases h563 : z ≤ ((15071/16000 : ℚ) : ℝ)
                      · -- left
                        by_cases h564 : z ≤ ((29229/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c417_pos (not_le.mp h473).le h551 (not_le.mp h560).le h564
                        · -- right
                          by_cases h565 : z ≤ ((59371/64000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c477_pos (not_le.mp h473).le h551 (not_le.mp h564).le h565
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c478_pos (not_le.mp h473).le h551 (not_le.mp h565).le h563
                      · -- right
                        by_cases h566 : z ≤ ((6211/6400 : ℚ) : ℝ)
                        · -- left
                          by_cases h567 : z ≤ ((61197/64000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c509_pos (not_le.mp h473).le h551 (not_le.mp h563).le h567
                          · -- right
                            by_cases h568 : z ≤ ((123307/128000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c536_pos (not_le.mp h473).le h551 (not_le.mp h567).le h568
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c537_pos (not_le.mp h473).le h551 (not_le.mp h568).le h566
                        · -- right
                          by_cases h569 : z ≤ ((63023/64000 : ℚ) : ℝ)
                          · -- left
                            by_cases h570 : z ≤ ((125133/128000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c572_pos (not_le.mp h473).le h551 (not_le.mp h566).le h570
                            · -- right
                              by_cases h571 : z ≤ ((251179/256000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c595_pos (not_le.mp h473).le h551 (not_le.mp h570).le h571
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c596_pos (not_le.mp h473).le h551 (not_le.mp h571).le h569
                          · -- right
                            by_cases h572 : z ≤ ((126959/128000 : ℚ) : ℝ)
                            · -- left
                              by_cases h573 : z ≤ ((50601/51200 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B031.c620_pos (not_le.mp h473).le h551 (not_le.mp h569).le h573
                              · -- right
                                by_cases h574 : z ≤ ((506923/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c640_pos (not_le.mp h473).le h551 (not_le.mp h573).le h574
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c641_pos (not_le.mp h473).le h551 (not_le.mp h574).le h572
                            · -- right
                              by_cases h575 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h576 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B033.c662_pos (not_le.mp h473).le h551 (not_le.mp h572).le h576
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B033.c664_pos (not_le.mp h473).le h551 (not_le.mp h576).le h575
                              · -- right
                                by_cases h577 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  by_cases h578 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B034.c685_pos (not_le.mp h473).le h551 (not_le.mp h575).le h578
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B034.c686_pos (not_le.mp h473).le h551 (not_le.mp h578).le h577
                                · -- right
                                  by_cases h579 : a ≤ ((255051/256000 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h580 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c694_pos (not_le.mp h473).le h579 (not_le.mp h577).le h580
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B034.c696_pos (not_le.mp h473).le h579 (not_le.mp h580).le hz2
                                  · -- right
                                    by_cases h581 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c695_pos (not_le.mp h579).le h551 (not_le.mp h577).le h581
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B034.c697_pos (not_le.mp h579).le h551 (not_le.mp h581).le hz2
              · -- right
                by_cases h582 : z ≤ ((217/400 : ℚ) : ℝ)
                · -- left
                  by_cases h583 : z ≤ ((1257/4000 : ℚ) : ℝ)
                  · -- left
                    by_cases h584 : z ≤ ((1601/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h585 : z ≤ ((2289/16000 : ℚ) : ℝ)
                      · -- left
                        by_cases h586 : a ≤ ((255249/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B018.c375_pos (not_le.mp h551).le h586 hz1 h585
                        · -- right
                          exact CKLaneC2R.Cells.S05.B018.c376_pos (not_le.mp h586).le h550 hz1 h585
                      · -- right
                        exact CKLaneC2R.Cells.S05.B014.c298_pos (not_le.mp h551).le h550 (not_le.mp h585).le h584
                    · -- right
                      exact CKLaneC2R.Cells.S05.B010.c214_pos (not_le.mp h551).le h550 (not_le.mp h584).le h583
                  · -- right
                    by_cases h587 : z ≤ ((3427/8000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B010.c218_pos (not_le.mp h551).le h550 (not_le.mp h583).le h587
                    · -- right
                      exact CKLaneC2R.Cells.S05.B011.c220_pos (not_le.mp h551).le h550 (not_le.mp h587).le h582
                · -- right
                  by_cases h588 : z ≤ ((3083/4000 : ℚ) : ℝ)
                  · -- left
                    by_cases h589 : z ≤ ((5253/8000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S05.B011.c232_pos (not_le.mp h551).le h550 (not_le.mp h582).le h589
                    · -- right
                      by_cases h590 : z ≤ ((11419/16000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c311_pos (not_le.mp h551).le h550 (not_le.mp h589).le h590
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c312_pos (not_le.mp h551).le h550 (not_le.mp h590).le h588
                  · -- right
                    by_cases h591 : z ≤ ((7079/8000 : ℚ) : ℝ)
                    · -- left
                      by_cases h592 : z ≤ ((2649/3200 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B016.c329_pos (not_le.mp h551).le h550 (not_le.mp h588).le h592
                      · -- right
                        by_cases h593 : z ≤ ((27403/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c391_pos (not_le.mp h551).le h550 (not_le.mp h592).le h593
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c392_pos (not_le.mp h551).le h550 (not_le.mp h593).le h591
                    · -- right
                      by_cases h594 : z ≤ ((15071/16000 : ℚ) : ℝ)
                      · -- left
                        by_cases h595 : z ≤ ((29229/32000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B020.c418_pos (not_le.mp h551).le h550 (not_le.mp h591).le h595
                        · -- right
                          by_cases h596 : z ≤ ((59371/64000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c479_pos (not_le.mp h551).le h550 (not_le.mp h595).le h596
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c480_pos (not_le.mp h551).le h550 (not_le.mp h596).le h594
                      · -- right
                        by_cases h597 : z ≤ ((6211/6400 : ℚ) : ℝ)
                        · -- left
                          by_cases h598 : z ≤ ((61197/64000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B025.c510_pos (not_le.mp h551).le h550 (not_le.mp h594).le h598
                          · -- right
                            by_cases h599 : z ≤ ((123307/128000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B026.c538_pos (not_le.mp h551).le h550 (not_le.mp h598).le h599
                            · -- right
                              exact CKLaneC2R.Cells.S05.B026.c539_pos (not_le.mp h551).le h550 (not_le.mp h599).le h597
                        · -- right
                          by_cases h600 : z ≤ ((63023/64000 : ℚ) : ℝ)
                          · -- left
                            by_cases h601 : z ≤ ((125133/128000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B028.c573_pos (not_le.mp h551).le h550 (not_le.mp h597).le h601
                            · -- right
                              by_cases h602 : z ≤ ((251179/256000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c597_pos (not_le.mp h551).le h550 (not_le.mp h601).le h602
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c598_pos (not_le.mp h551).le h550 (not_le.mp h602).le h600
                          · -- right
                            by_cases h603 : z ≤ ((126959/128000 : ℚ) : ℝ)
                            · -- left
                              by_cases h604 : z ≤ ((50601/51200 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B031.c621_pos (not_le.mp h551).le h550 (not_le.mp h600).le h604
                              · -- right
                                by_cases h605 : z ≤ ((506923/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c642_pos (not_le.mp h551).le h550 (not_le.mp h604).le h605
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c643_pos (not_le.mp h551).le h550 (not_le.mp h605).le h603
                            · -- right
                              by_cases h606 : z ≤ ((254831/256000 : ℚ) : ℝ)
                              · -- left
                                by_cases h607 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B033.c663_pos (not_le.mp h551).le h550 (not_le.mp h603).le h607
                                · -- right
                                  by_cases h608 : a ≤ ((255249/256000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c676_pos (not_le.mp h551).le h608 (not_le.mp h607).le h606
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c677_pos (not_le.mp h608).le h550 (not_le.mp h607).le h606
                              · -- right
                                by_cases h609 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                · -- left
                                  by_cases h610 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B034.c687_pos (not_le.mp h551).le h550 (not_le.mp h606).le h610
                                  · -- right
                                    by_cases h611 : a ≤ ((255249/256000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c692_pos (not_le.mp h551).le h611 (not_le.mp h610).le h609
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B034.c693_pos (not_le.mp h611).le h550 (not_le.mp h610).le h609
                                · -- right
                                  by_cases h612 : a ≤ ((255249/256000 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h613 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c698_pos (not_le.mp h551).le h612 (not_le.mp h609).le h613
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B035.c700_pos (not_le.mp h551).le h612 (not_le.mp h613).le hz2
                                  · -- right
                                    by_cases h614 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c699_pos (not_le.mp h612).le h550 (not_le.mp h609).le h614
                                    · -- right
                                      by_cases h615 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c708_pos (not_le.mp h612).le h550 (not_le.mp h614).le h615
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c709_pos (not_le.mp h612).le h550 (not_le.mp h615).le hz2
            · -- right
              by_cases h616 : a ≤ ((127773/128000 : ℚ) : ℝ)
              · -- left
                by_cases h617 : a ≤ ((255447/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h618 : z ≤ ((217/400 : ℚ) : ℝ)
                  · -- left
                    by_cases h619 : z ≤ ((1257/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h620 : z ≤ ((1601/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h621 : z ≤ ((2289/16000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B018.c377_pos (not_le.mp h550).le h617 hz1 h621
                        · -- right
                          exact CKLaneC2R.Cells.S05.B018.c379_pos (not_le.mp h550).le h617 (not_le.mp h621).le h620
                      · -- right
                        exact CKLaneC2R.Cells.S05.B014.c299_pos (not_le.mp h550).le h617 (not_le.mp h620).le h619
                    · -- right
                      by_cases h622 : z ≤ ((3427/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c302_pos (not_le.mp h550).le h617 (not_le.mp h619).le h622
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c304_pos (not_le.mp h550).le h617 (not_le.mp h622).le h618
                  · -- right
                    by_cases h623 : z ≤ ((3083/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h624 : z ≤ ((5253/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c313_pos (not_le.mp h550).le h617 (not_le.mp h618).le h624
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c317_pos (not_le.mp h550).le h617 (not_le.mp h624).le h623
                    · -- right
                      by_cases h625 : z ≤ ((7079/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h626 : z ≤ ((2649/3200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c393_pos (not_le.mp h550).le h617 (not_le.mp h623).le h626
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c397_pos (not_le.mp h550).le h617 (not_le.mp h626).le h625
                      · -- right
                        by_cases h627 : z ≤ ((15071/16000 : ℚ) : ℝ)
                        · -- left
                          by_cases h628 : z ≤ ((29229/32000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c481_pos (not_le.mp h550).le h617 (not_le.mp h625).le h628
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c485_pos (not_le.mp h550).le h617 (not_le.mp h628).le h627
                        · -- right
                          by_cases h629 : z ≤ ((6211/6400 : ℚ) : ℝ)
                          · -- left
                            by_cases h630 : z ≤ ((61197/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c540_pos (not_le.mp h550).le h617 (not_le.mp h627).le h630
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c544_pos (not_le.mp h550).le h617 (not_le.mp h630).le h629
                          · -- right
                            by_cases h631 : z ≤ ((63023/64000 : ℚ) : ℝ)
                            · -- left
                              by_cases h632 : z ≤ ((125133/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c599_pos (not_le.mp h550).le h617 (not_le.mp h629).le h632
                              · -- right
                                by_cases h633 : z ≤ ((251179/256000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c622_pos (not_le.mp h550).le h617 (not_le.mp h632).le h633
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c624_pos (not_le.mp h550).le h617 (not_le.mp h633).le h631
                            · -- right
                              by_cases h634 : z ≤ ((126959/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h635 : z ≤ ((50601/51200 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c644_pos (not_le.mp h550).le h617 (not_le.mp h631).le h635
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c648_pos (not_le.mp h550).le h617 (not_le.mp h635).le h634
                              · -- right
                                by_cases h636 : z ≤ ((254831/256000 : ℚ) : ℝ)
                                · -- left
                                  by_cases h637 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c678_pos (not_le.mp h550).le h617 (not_le.mp h634).le h637
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B034.c680_pos (not_le.mp h550).le h617 (not_le.mp h637).le h636
                                · -- right
                                  by_cases h638 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h639 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B035.c701_pos (not_le.mp h550).le h617 (not_le.mp h636).le h639
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B035.c703_pos (not_le.mp h550).le h617 (not_le.mp h639).le h638
                                  · -- right
                                    by_cases h640 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B035.c707_pos (not_le.mp h550).le h617 (not_le.mp h638).le h640
                                    · -- right
                                      by_cases h641 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c716_pos (not_le.mp h550).le h617 (not_le.mp h640).le h641
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c717_pos (not_le.mp h550).le h617 (not_le.mp h641).le hz2
                · -- right
                  by_cases h642 : z ≤ ((217/400 : ℚ) : ℝ)
                  · -- left
                    by_cases h643 : z ≤ ((1257/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h644 : z ≤ ((1601/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h645 : z ≤ ((2289/16000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B018.c378_pos (not_le.mp h617).le h616 hz1 h645
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c380_pos (not_le.mp h617).le h616 (not_le.mp h645).le h644
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c300_pos (not_le.mp h617).le h616 (not_le.mp h644).le h643
                    · -- right
                      by_cases h646 : z ≤ ((3427/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c303_pos (not_le.mp h617).le h616 (not_le.mp h643).le h646
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c305_pos (not_le.mp h617).le h616 (not_le.mp h646).le h642
                  · -- right
                    by_cases h647 : z ≤ ((3083/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h648 : z ≤ ((5253/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c314_pos (not_le.mp h617).le h616 (not_le.mp h642).le h648
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c318_pos (not_le.mp h617).le h616 (not_le.mp h648).le h647
                    · -- right
                      by_cases h649 : z ≤ ((7079/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h650 : z ≤ ((2649/3200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c394_pos (not_le.mp h617).le h616 (not_le.mp h647).le h650
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c398_pos (not_le.mp h617).le h616 (not_le.mp h650).le h649
                      · -- right
                        by_cases h651 : z ≤ ((15071/16000 : ℚ) : ℝ)
                        · -- left
                          by_cases h652 : z ≤ ((29229/32000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c482_pos (not_le.mp h617).le h616 (not_le.mp h649).le h652
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c486_pos (not_le.mp h617).le h616 (not_le.mp h652).le h651
                        · -- right
                          by_cases h653 : z ≤ ((6211/6400 : ℚ) : ℝ)
                          · -- left
                            by_cases h654 : z ≤ ((61197/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c541_pos (not_le.mp h617).le h616 (not_le.mp h651).le h654
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c545_pos (not_le.mp h617).le h616 (not_le.mp h654).le h653
                          · -- right
                            by_cases h655 : z ≤ ((63023/64000 : ℚ) : ℝ)
                            · -- left
                              by_cases h656 : z ≤ ((125133/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c600_pos (not_le.mp h617).le h616 (not_le.mp h653).le h656
                              · -- right
                                by_cases h657 : z ≤ ((251179/256000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c623_pos (not_le.mp h617).le h616 (not_le.mp h656).le h657
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c625_pos (not_le.mp h617).le h616 (not_le.mp h657).le h655
                            · -- right
                              by_cases h658 : z ≤ ((126959/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h659 : z ≤ ((50601/51200 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c645_pos (not_le.mp h617).le h616 (not_le.mp h655).le h659
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c649_pos (not_le.mp h617).le h616 (not_le.mp h659).le h658
                              · -- right
                                by_cases h660 : z ≤ ((254831/256000 : ℚ) : ℝ)
                                · -- left
                                  by_cases h661 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c679_pos (not_le.mp h617).le h616 (not_le.mp h658).le h661
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B034.c681_pos (not_le.mp h617).le h616 (not_le.mp h661).le h660
                                · -- right
                                  by_cases h662 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h663 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B035.c702_pos (not_le.mp h617).le h616 (not_le.mp h660).le h663
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B035.c704_pos (not_le.mp h617).le h616 (not_le.mp h663).le h662
                                  · -- right
                                    by_cases h664 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      by_cases h665 : z ≤ ((2043213/2048000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c714_pos (not_le.mp h617).le h616 (not_le.mp h662).le h665
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c715_pos (not_le.mp h617).le h616 (not_le.mp h665).le h664
                                    · -- right
                                      by_cases h666 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c718_pos (not_le.mp h617).le h616 (not_le.mp h664).le h666
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c719_pos (not_le.mp h617).le h616 (not_le.mp h666).le hz2
              · -- right
                by_cases h667 : a ≤ ((51129/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h668 : z ≤ ((217/400 : ℚ) : ℝ)
                  · -- left
                    by_cases h669 : z ≤ ((1257/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h670 : z ≤ ((1601/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h671 : z ≤ ((2289/16000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c381_pos (not_le.mp h616).le h667 hz1 h671
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c382_pos (not_le.mp h616).le h667 (not_le.mp h671).le h670
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c301_pos (not_le.mp h616).le h667 (not_le.mp h670).le h669
                    · -- right
                      by_cases h672 : z ≤ ((3427/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c306_pos (not_le.mp h616).le h667 (not_le.mp h669).le h672
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c307_pos (not_le.mp h616).le h667 (not_le.mp h672).le h668
                  · -- right
                    by_cases h673 : z ≤ ((3083/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h674 : z ≤ ((5253/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c315_pos (not_le.mp h616).le h667 (not_le.mp h668).le h674
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c319_pos (not_le.mp h616).le h667 (not_le.mp h674).le h673
                    · -- right
                      by_cases h675 : z ≤ ((7079/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h676 : z ≤ ((2649/3200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c395_pos (not_le.mp h616).le h667 (not_le.mp h673).le h676
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c399_pos (not_le.mp h616).le h667 (not_le.mp h676).le h675
                      · -- right
                        by_cases h677 : z ≤ ((15071/16000 : ℚ) : ℝ)
                        · -- left
                          by_cases h678 : z ≤ ((29229/32000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c483_pos (not_le.mp h616).le h667 (not_le.mp h675).le h678
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c487_pos (not_le.mp h616).le h667 (not_le.mp h678).le h677
                        · -- right
                          by_cases h679 : z ≤ ((6211/6400 : ℚ) : ℝ)
                          · -- left
                            by_cases h680 : z ≤ ((61197/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c542_pos (not_le.mp h616).le h667 (not_le.mp h677).le h680
                            · -- right
                              exact CKLaneC2R.Cells.S05.B027.c546_pos (not_le.mp h616).le h667 (not_le.mp h680).le h679
                          · -- right
                            by_cases h681 : z ≤ ((63023/64000 : ℚ) : ℝ)
                            · -- left
                              by_cases h682 : z ≤ ((125133/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c601_pos (not_le.mp h616).le h667 (not_le.mp h679).le h682
                              · -- right
                                exact CKLaneC2R.Cells.S05.B030.c603_pos (not_le.mp h616).le h667 (not_le.mp h682).le h681
                            · -- right
                              by_cases h683 : z ≤ ((126959/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h684 : z ≤ ((50601/51200 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c646_pos (not_le.mp h616).le h667 (not_le.mp h681).le h684
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B032.c650_pos (not_le.mp h616).le h667 (not_le.mp h684).le h683
                              · -- right
                                by_cases h685 : z ≤ ((254831/256000 : ℚ) : ℝ)
                                · -- left
                                  by_cases h686 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B034.c682_pos (not_le.mp h616).le h667 (not_le.mp h683).le h686
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B034.c684_pos (not_le.mp h616).le h667 (not_le.mp h686).le h685
                                · -- right
                                  by_cases h687 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h688 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B035.c705_pos (not_le.mp h616).le h667 (not_le.mp h685).le h688
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B035.c706_pos (not_le.mp h616).le h667 (not_le.mp h688).le h687
                                  · -- right
                                    by_cases h689 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                    · -- left
                                      by_cases h690 : z ≤ ((2043213/2048000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B036.c720_pos (not_le.mp h616).le h667 (not_le.mp h687).le h690
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B036.c721_pos (not_le.mp h616).le h667 (not_le.mp h690).le h689
                                    · -- right
                                      by_cases h691 : a ≤ ((511191/512000 : ℚ) : ℝ)
                                      · -- left
                                        by_cases h692 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                        · -- left
                                          exact CKLaneC2R.Cells.S05.B036.c724_pos (not_le.mp h616).le h691 (not_le.mp h689).le h692
                                        · -- right
                                          exact CKLaneC2R.Cells.S05.B036.c726_pos (not_le.mp h616).le h691 (not_le.mp h692).le hz2
                                      · -- right
                                        by_cases h693 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                        · -- left
                                          exact CKLaneC2R.Cells.S05.B036.c725_pos (not_le.mp h691).le h667 (not_le.mp h689).le h693
                                        · -- right
                                          exact CKLaneC2R.Cells.S05.B036.c727_pos (not_le.mp h691).le h667 (not_le.mp h693).le hz2
                · -- right
                  by_cases h694 : z ≤ ((217/400 : ℚ) : ℝ)
                  · -- left
                    by_cases h695 : z ≤ ((1257/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h696 : a ≤ ((511389/512000 : ℚ) : ℝ)
                      · -- left
                        by_cases h697 : z ≤ ((1601/8000 : ℚ) : ℝ)
                        · -- left
                          by_cases h698 : z ≤ ((2289/16000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c461_pos (not_le.mp h667).le h696 hz1 h698
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c463_pos (not_le.mp h667).le h696 (not_le.mp h698).le h697
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c383_pos (not_le.mp h667).le h696 (not_le.mp h697).le h695
                      · -- right
                        by_cases h699 : z ≤ ((1601/8000 : ℚ) : ℝ)
                        · -- left
                          by_cases h700 : z ≤ ((2289/16000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B023.c462_pos (not_le.mp h696).le ha2 hz1 h700
                          · -- right
                            exact CKLaneC2R.Cells.S05.B023.c464_pos (not_le.mp h696).le ha2 (not_le.mp h700).le h699
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c384_pos (not_le.mp h696).le ha2 (not_le.mp h699).le h695
                    · -- right
                      by_cases h701 : z ≤ ((3427/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h702 : a ≤ ((511389/512000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c385_pos (not_le.mp h667).le h702 (not_le.mp h695).le h701
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c386_pos (not_le.mp h702).le ha2 (not_le.mp h695).le h701
                      · -- right
                        exact CKLaneC2R.Cells.S05.B015.c308_pos (not_le.mp h667).le ha2 (not_le.mp h701).le h694
                  · -- right
                    by_cases h703 : z ≤ ((3083/4000 : ℚ) : ℝ)
                    · -- left
                      by_cases h704 : z ≤ ((5253/8000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S05.B015.c316_pos (not_le.mp h667).le ha2 (not_le.mp h694).le h704
                      · -- right
                        by_cases h705 : a ≤ ((511389/512000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c387_pos (not_le.mp h667).le h705 (not_le.mp h704).le h703
                        · -- right
                          exact CKLaneC2R.Cells.S05.B019.c388_pos (not_le.mp h705).le ha2 (not_le.mp h704).le h703
                    · -- right
                      by_cases h706 : z ≤ ((7079/8000 : ℚ) : ℝ)
                      · -- left
                        by_cases h707 : z ≤ ((2649/3200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S05.B019.c396_pos (not_le.mp h667).le ha2 (not_le.mp h703).le h707
                        · -- right
                          exact CKLaneC2R.Cells.S05.B020.c400_pos (not_le.mp h667).le ha2 (not_le.mp h707).le h706
                      · -- right
                        by_cases h708 : z ≤ ((15071/16000 : ℚ) : ℝ)
                        · -- left
                          by_cases h709 : z ≤ ((29229/32000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S05.B024.c484_pos (not_le.mp h667).le ha2 (not_le.mp h706).le h709
                          · -- right
                            exact CKLaneC2R.Cells.S05.B024.c488_pos (not_le.mp h667).le ha2 (not_le.mp h709).le h708
                        · -- right
                          by_cases h710 : z ≤ ((6211/6400 : ℚ) : ℝ)
                          · -- left
                            by_cases h711 : z ≤ ((61197/64000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S05.B027.c543_pos (not_le.mp h667).le ha2 (not_le.mp h708).le h711
                            · -- right
                              by_cases h712 : a ≤ ((511389/512000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B029.c583_pos (not_le.mp h667).le h712 (not_le.mp h711).le h710
                              · -- right
                                exact CKLaneC2R.Cells.S05.B029.c584_pos (not_le.mp h712).le ha2 (not_le.mp h711).le h710
                          · -- right
                            by_cases h713 : z ≤ ((63023/64000 : ℚ) : ℝ)
                            · -- left
                              by_cases h714 : z ≤ ((125133/128000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S05.B030.c602_pos (not_le.mp h667).le ha2 (not_le.mp h710).le h714
                              · -- right
                                by_cases h715 : a ≤ ((511389/512000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B031.c626_pos (not_le.mp h667).le h715 (not_le.mp h714).le h713
                                · -- right
                                  exact CKLaneC2R.Cells.S05.B031.c627_pos (not_le.mp h715).le ha2 (not_le.mp h714).le h713
                            · -- right
                              by_cases h716 : z ≤ ((126959/128000 : ℚ) : ℝ)
                              · -- left
                                by_cases h717 : z ≤ ((50601/51200 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.Cells.S05.B032.c647_pos (not_le.mp h667).le ha2 (not_le.mp h713).le h717
                                · -- right
                                  by_cases h718 : a ≤ ((511389/512000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B033.c665_pos (not_le.mp h667).le h718 (not_le.mp h717).le h716
                                  · -- right
                                    exact CKLaneC2R.Cells.S05.B033.c666_pos (not_le.mp h718).le ha2 (not_le.mp h717).le h716
                              · -- right
                                by_cases h719 : z ≤ ((254831/256000 : ℚ) : ℝ)
                                · -- left
                                  by_cases h720 : z ≤ ((508749/512000 : ℚ) : ℝ)
                                  · -- left
                                    exact CKLaneC2R.Cells.S05.B034.c683_pos (not_le.mp h667).le ha2 (not_le.mp h716).le h720
                                  · -- right
                                    by_cases h721 : a ≤ ((511389/512000 : ℚ) : ℝ)
                                    · -- left
                                      exact CKLaneC2R.Cells.S05.B034.c690_pos (not_le.mp h667).le h721 (not_le.mp h720).le h719
                                    · -- right
                                      exact CKLaneC2R.Cells.S05.B034.c691_pos (not_le.mp h721).le ha2 (not_le.mp h720).le h719
                                · -- right
                                  by_cases h722 : a ≤ ((511389/512000 : ℚ) : ℝ)
                                  · -- left
                                    by_cases h723 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                    · -- left
                                      by_cases h724 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c710_pos (not_le.mp h667).le h722 (not_le.mp h719).le h724
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c712_pos (not_le.mp h667).le h722 (not_le.mp h724).le h723
                                    · -- right
                                      by_cases h725 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B036.c722_pos (not_le.mp h667).le h722 (not_le.mp h723).le h725
                                      · -- right
                                        by_cases h726 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                        · -- left
                                          exact CKLaneC2R.Cells.S05.B036.c728_pos (not_le.mp h667).le h722 (not_le.mp h725).le h726
                                        · -- right
                                          exact CKLaneC2R.Cells.S05.B036.c730_pos (not_le.mp h667).le h722 (not_le.mp h726).le hz2
                                  · -- right
                                    by_cases h727 : z ≤ ((20423/20480 : ℚ) : ℝ)
                                    · -- left
                                      by_cases h728 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B035.c711_pos (not_le.mp h722).le ha2 (not_le.mp h719).le h728
                                      · -- right
                                        exact CKLaneC2R.Cells.S05.B035.c713_pos (not_le.mp h722).le ha2 (not_le.mp h728).le h727
                                    · -- right
                                      by_cases h729 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                                      · -- left
                                        exact CKLaneC2R.Cells.S05.B036.c723_pos (not_le.mp h722).le ha2 (not_le.mp h727).le h729
                                      · -- right
                                        by_cases h730 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                                        · -- left
                                          exact CKLaneC2R.Cells.S05.B036.c729_pos (not_le.mp h722).le ha2 (not_le.mp h729).le h730
                                        · -- right
                                          exact CKLaneC2R.Cells.S05.B036.c731_pos (not_le.mp h722).le ha2 (not_le.mp h730).le hz2

end CKLaneC2R.CompactCover

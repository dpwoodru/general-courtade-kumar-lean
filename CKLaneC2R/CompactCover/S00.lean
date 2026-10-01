import CKLaneC2R.Cells.S00.B000
import CKLaneC2R.Cells.S00.B001
import CKLaneC2R.Cells.S00.B002
import CKLaneC2R.Cells.S00.B003
import CKLaneC2R.Cells.S00.B004
import CKLaneC2R.Cells.S00.B005
import CKLaneC2R.Cells.S00.B006
import CKLaneC2R.Cells.S00.B007
import CKLaneC2R.Cells.S00.B008
import CKLaneC2R.Cells.S00.B009
import CKLaneC2R.Cells.S00.B010
import CKLaneC2R.Cells.S00.B011
import CKLaneC2R.Cells.S00.B012
import CKLaneC2R.Cells.S00.B013
import CKLaneC2R.Cells.S00.B014
import CKLaneC2R.Cells.S00.B015
import CKLaneC2R.Cells.S00.B016
import CKLaneC2R.Cells.S00.B017
import CKLaneC2R.Cells.S00.B018
import CKLaneC2R.Cells.S00.B019
import CKLaneC2R.Cells.S00.B020
import CKLaneC2R.Cells.S00.B021
import CKLaneC2R.Cells.S00.B022
import CKLaneC2R.Cells.S00.B023
import CKLaneC2R.Cells.S00.B024
import CKLaneC2R.Cells.S00.B025
import CKLaneC2R.Cells.S00.B026
import CKLaneC2R.Cells.S00.B027
import CKLaneC2R.Cells.S00.B028
import CKLaneC2R.Cells.S00.B029
import CKLaneC2R.Cells.S00.B030
import CKLaneC2R.Cells.S00.B031
import CKLaneC2R.Cells.S00.B032
import CKLaneC2R.Cells.S00.B033
import CKLaneC2R.Cells.S00.B034
import CKLaneC2R.Cells.S00.B035
import CKLaneC2R.Cells.S00.B036
import CKLaneC2R.Cells.S00.B037
import CKLaneC2R.Cells.S00.B038
import CKLaneC2R.Cells.S00.B039
import CKLaneC2R.Cells.S00.B040
import CKLaneC2R.Cells.S00.B041
import CKLaneC2R.Cells.S00.B042
import CKLaneC2R.Cells.S00.B043
import CKLaneC2R.Cells.S00.B044
import CKLaneC2R.Cells.S00.B045
import CKLaneC2R.Cells.S00.B046
import CKLaneC2R.Cells.S00.B047
import CKLaneC2R.Cells.S00.B048
import CKLaneC2R.Cells.S00.B049
import CKLaneC2R.Cells.S00.B050
import CKLaneC2R.Cells.S00.B051
import CKLaneC2R.Cells.S00.B052
import CKLaneC2R.Cells.S00.B053
import CKLaneC2R.Cells.S00.B054
import CKLaneC2R.Cells.S00.B055
import CKLaneC2R.Cells.S00.B056
import CKLaneC2R.Cells.S00.B057
import CKLaneC2R.Cells.S00.B058
import CKLaneC2R.Cells.S00.B059
import CKLaneC2R.Cells.S00.B060
import CKLaneC2R.Cells.S00.B061
import CKLaneC2R.Cells.S00.B062
import CKLaneC2R.Cells.S00.B063
import CKLaneC2R.Cells.S00.B064
import CKLaneC2R.Cells.S00.B065
import CKLaneC2R.Cells.S00.B066
import CKLaneC2R.Cells.S00.B067
import CKLaneC2R.Cells.S00.B068
import CKLaneC2R.Cells.S00.B069
import CKLaneC2R.Cells.S00.B070
import CKLaneC2R.Cells.S00.B071
import CKLaneC2R.Cells.S00.B072
import CKLaneC2R.Cells.S00.B073
import CKLaneC2R.Cells.S00.B074
import CKLaneC2R.Cells.S00.B075

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 0: a ∈ [3/20,1/5], z ∈ [43/500,999/1000] (1510 cells, BSP depth 15). -/
theorem strip0 {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/5 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((7/40 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((13/80 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((5/32 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((49/320 : ℚ) : ℝ)
        · -- left
          by_cases h4 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h5 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h6 : a ≤ ((97/640 : ℚ) : ℝ)
              · -- left
                by_cases h7 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h8 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h9 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h10 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h11 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h12 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B068.c1370_pos ha1 h6 hz1 h12
                          · -- right
                            exact CKLaneC2R.Cells.S00.B068.c1371_pos ha1 h6 (not_le.mp h12).le h11
                        · -- right
                          by_cases h13 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B068.c1374_pos ha1 h6 (not_le.mp h11).le h13
                          · -- right
                            exact CKLaneC2R.Cells.S00.B068.c1375_pos ha1 h6 (not_le.mp h13).le h10
                      · -- right
                        by_cases h14 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h15 : z ≤ ((26581/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1386_pos ha1 h6 (not_le.mp h10).le h15
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1387_pos ha1 h6 (not_le.mp h15).le h14
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1060_pos ha1 h6 (not_le.mp h14).le h9
                    · -- right
                      by_cases h16 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h17 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1076_pos ha1 h6 (not_le.mp h9).le h17
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1078_pos ha1 h6 (not_le.mp h17).le h16
                      · -- right
                        by_cases h18 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1084_pos ha1 h6 (not_le.mp h16).le h18
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1086_pos ha1 h6 (not_le.mp h18).le h8
                  · -- right
                    by_cases h19 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h20 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h21 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1108_pos ha1 h6 (not_le.mp h8).le h21
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1109_pos ha1 h6 (not_le.mp h21).le h20
                      · -- right
                        by_cases h22 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1112_pos ha1 h6 (not_le.mp h20).le h22
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1113_pos ha1 h6 (not_le.mp h22).le h19
                    · -- right
                      by_cases h23 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        by_cases h24 : z ≤ ((22877/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1124_pos ha1 h6 (not_le.mp h19).le h24
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1125_pos ha1 h6 (not_le.mp h24).le h23
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c672_pos ha1 h6 (not_le.mp h23).le h7
                · -- right
                  by_cases h25 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h26 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h27 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c709_pos ha1 h6 (not_le.mp h7).le h27
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c711_pos ha1 h6 (not_le.mp h27).le h26
                    · -- right
                      by_cases h28 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c717_pos ha1 h6 (not_le.mp h26).le h28
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c719_pos ha1 h6 (not_le.mp h28).le h25
                  · -- right
                    by_cases h29 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h30 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c741_pos ha1 h6 (not_le.mp h25).le h30
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c743_pos ha1 h6 (not_le.mp h30).le h29
                    · -- right
                      by_cases h31 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c749_pos ha1 h6 (not_le.mp h29).le h31
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c751_pos ha1 h6 (not_le.mp h31).le h5
              · -- right
                by_cases h32 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h33 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h34 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h35 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h36 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h37 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B068.c1372_pos (not_le.mp h6).le h3 hz1 h37
                          · -- right
                            exact CKLaneC2R.Cells.S00.B068.c1373_pos (not_le.mp h6).le h3 (not_le.mp h37).le h36
                        · -- right
                          by_cases h38 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B068.c1376_pos (not_le.mp h6).le h3 (not_le.mp h36).le h38
                          · -- right
                            exact CKLaneC2R.Cells.S00.B068.c1377_pos (not_le.mp h6).le h3 (not_le.mp h38).le h35
                      · -- right
                        by_cases h39 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h40 : z ≤ ((26581/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1388_pos (not_le.mp h6).le h3 (not_le.mp h35).le h40
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1389_pos (not_le.mp h6).le h3 (not_le.mp h40).le h39
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1061_pos (not_le.mp h6).le h3 (not_le.mp h39).le h34
                    · -- right
                      by_cases h41 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h42 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1077_pos (not_le.mp h6).le h3 (not_le.mp h34).le h42
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1079_pos (not_le.mp h6).le h3 (not_le.mp h42).le h41
                      · -- right
                        by_cases h43 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1085_pos (not_le.mp h6).le h3 (not_le.mp h41).le h43
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1087_pos (not_le.mp h6).le h3 (not_le.mp h43).le h33
                  · -- right
                    by_cases h44 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h45 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h46 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1110_pos (not_le.mp h6).le h3 (not_le.mp h33).le h46
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1111_pos (not_le.mp h6).le h3 (not_le.mp h46).le h45
                      · -- right
                        by_cases h47 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1114_pos (not_le.mp h6).le h3 (not_le.mp h45).le h47
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1115_pos (not_le.mp h6).le h3 (not_le.mp h47).le h44
                    · -- right
                      by_cases h48 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        by_cases h49 : z ≤ ((22877/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1126_pos (not_le.mp h6).le h3 (not_le.mp h44).le h49
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1127_pos (not_le.mp h6).le h3 (not_le.mp h49).le h48
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c673_pos (not_le.mp h6).le h3 (not_le.mp h48).le h32
                · -- right
                  by_cases h50 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h51 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h52 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c710_pos (not_le.mp h6).le h3 (not_le.mp h32).le h52
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c712_pos (not_le.mp h6).le h3 (not_le.mp h52).le h51
                    · -- right
                      by_cases h53 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c718_pos (not_le.mp h6).le h3 (not_le.mp h51).le h53
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c720_pos (not_le.mp h6).le h3 (not_le.mp h53).le h50
                  · -- right
                    by_cases h54 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h55 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c742_pos (not_le.mp h6).le h3 (not_le.mp h50).le h55
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c744_pos (not_le.mp h6).le h3 (not_le.mp h55).le h54
                    · -- right
                      by_cases h56 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c750_pos (not_le.mp h6).le h3 (not_le.mp h54).le h56
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c752_pos (not_le.mp h6).le h3 (not_le.mp h56).le h5
            · -- right
              by_cases h57 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h58 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h59 : a ≤ ((97/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h60 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h61 : z ≤ ((841/2560 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c809_pos ha1 h59 (not_le.mp h5).le h61
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c811_pos ha1 h59 (not_le.mp h61).le h60
                    · -- right
                      by_cases h62 : z ≤ ((22851/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c817_pos ha1 h59 (not_le.mp h60).le h62
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c819_pos ha1 h59 (not_le.mp h62).le h58
                  · -- right
                    by_cases h63 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h64 : z ≤ ((841/2560 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c810_pos (not_le.mp h59).le h3 (not_le.mp h5).le h64
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c812_pos (not_le.mp h59).le h3 (not_le.mp h64).le h63
                    · -- right
                      by_cases h65 : z ≤ ((22851/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c818_pos (not_le.mp h59).le h3 (not_le.mp h63).le h65
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c820_pos (not_le.mp h59).le h3 (not_le.mp h65).le h58
                · -- right
                  by_cases h66 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h67 : a ≤ ((97/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h68 : z ≤ ((24677/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c825_pos ha1 h67 (not_le.mp h58).le h68
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c827_pos ha1 h67 (not_le.mp h68).le h66
                    · -- right
                      by_cases h69 : z ≤ ((24677/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c826_pos (not_le.mp h67).le h3 (not_le.mp h58).le h69
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c828_pos (not_le.mp h67).le h3 (not_le.mp h69).le h66
                  · -- right
                    by_cases h70 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c91_pos ha1 h3 (not_le.mp h66).le h70
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c92_pos ha1 h3 (not_le.mp h70).le h57
              · -- right
                by_cases h71 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h72 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h73 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c103_pos ha1 h3 (not_le.mp h57).le h73
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c104_pos ha1 h3 (not_le.mp h73).le h72
                  · -- right
                    by_cases h74 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c107_pos ha1 h3 (not_le.mp h72).le h74
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c108_pos ha1 h3 (not_le.mp h74).le h71
                · -- right
                  by_cases h75 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h76 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c119_pos ha1 h3 (not_le.mp h71).le h76
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c120_pos ha1 h3 (not_le.mp h76).le h75
                  · -- right
                    by_cases h77 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c123_pos ha1 h3 (not_le.mp h75).le h77
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c124_pos ha1 h3 (not_le.mp h77).le h4
          · -- right
            by_cases h78 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h79 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h80 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h81 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h82 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c345_pos ha1 h3 (not_le.mp h4).le h82
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c346_pos ha1 h3 (not_le.mp h82).le h81
                  · -- right
                    by_cases h83 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c349_pos ha1 h3 (not_le.mp h81).le h83
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c350_pos ha1 h3 (not_le.mp h83).le h80
                · -- right
                  by_cases h84 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h85 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c361_pos ha1 h3 (not_le.mp h80).le h85
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c362_pos ha1 h3 (not_le.mp h85).le h84
                  · -- right
                    by_cases h86 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c365_pos ha1 h3 (not_le.mp h84).le h86
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c366_pos ha1 h3 (not_le.mp h86).le h79
              · -- right
                by_cases h87 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h88 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h89 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c409_pos ha1 h3 (not_le.mp h79).le h89
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c410_pos ha1 h3 (not_le.mp h89).le h88
                  · -- right
                    by_cases h90 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c413_pos ha1 h3 (not_le.mp h88).le h90
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c414_pos ha1 h3 (not_le.mp h90).le h87
                · -- right
                  by_cases h91 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h92 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c425_pos ha1 h3 (not_le.mp h87).le h92
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c426_pos ha1 h3 (not_le.mp h92).le h91
                  · -- right
                    by_cases h93 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c429_pos ha1 h3 (not_le.mp h91).le h93
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c430_pos ha1 h3 (not_le.mp h93).le h78
            · -- right
              by_cases h94 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h95 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h96 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h97 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c517_pos ha1 h3 (not_le.mp h78).le h97
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c518_pos ha1 h3 (not_le.mp h97).le h96
                  · -- right
                    by_cases h98 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c521_pos ha1 h3 (not_le.mp h96).le h98
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c522_pos ha1 h3 (not_le.mp h98).le h95
                · -- right
                  by_cases h99 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h100 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c549_pos ha1 h3 (not_le.mp h95).le h100
                    · -- right
                      by_cases h101 : a ≤ ((97/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c921_pos ha1 h101 (not_le.mp h100).le h99
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c922_pos (not_le.mp h101).le h3 (not_le.mp h100).le h99
                  · -- right
                    by_cases h102 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h103 : z ≤ ((4421/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c923_pos ha1 h3 (not_le.mp h99).le h103
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c924_pos ha1 h3 (not_le.mp h103).le h102
                    · -- right
                      by_cases h104 : z ≤ ((112351/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c925_pos ha1 h3 (not_le.mp h102).le h104
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c926_pos ha1 h3 (not_le.mp h104).le h94
              · -- right
                by_cases h105 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h106 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h107 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h108 : z ≤ ((114177/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c929_pos ha1 h3 (not_le.mp h94).le h108
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c930_pos ha1 h3 (not_le.mp h108).le h107
                    · -- right
                      by_cases h109 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c933_pos ha1 h3 (not_le.mp h107).le h109
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c934_pos ha1 h3 (not_le.mp h109).le h106
                  · -- right
                    by_cases h110 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h111 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c945_pos ha1 h3 (not_le.mp h106).le h111
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c946_pos ha1 h3 (not_le.mp h111).le h110
                    · -- right
                      by_cases h112 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c949_pos ha1 h3 (not_le.mp h110).le h112
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c950_pos ha1 h3 (not_le.mp h112).le h105
                · -- right
                  by_cases h113 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h114 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h115 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c995_pos ha1 h3 (not_le.mp h105).le h115
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c997_pos ha1 h3 (not_le.mp h115).le h114
                    · -- right
                      by_cases h116 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h117 : z ≤ ((245701/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1289_pos ha1 h3 (not_le.mp h114).le h117
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1290_pos ha1 h3 (not_le.mp h117).le h116
                      · -- right
                        by_cases h118 : z ≤ ((247527/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1291_pos ha1 h3 (not_le.mp h116).le h118
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1292_pos ha1 h3 (not_le.mp h118).le h113
                  · -- right
                    by_cases h119 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h120 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h121 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1299_pos ha1 h3 (not_le.mp h113).le h121
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1300_pos ha1 h3 (not_le.mp h121).le h120
                      · -- right
                        by_cases h122 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1307_pos ha1 h3 (not_le.mp h120).le h122
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1309_pos ha1 h3 (not_le.mp h122).le h119
                    · -- right
                      by_cases h123 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h124 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          by_cases h125 : z ≤ ((505097/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1404_pos ha1 h3 (not_le.mp h119).le h125
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1405_pos ha1 h3 (not_le.mp h125).le h124
                        · -- right
                          by_cases h126 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1406_pos ha1 h3 (not_le.mp h124).le h126
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1407_pos ha1 h3 (not_le.mp h126).le h123
                      · -- right
                        by_cases h127 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h128 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1420_pos ha1 h3 (not_le.mp h123).le h128
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1422_pos ha1 h3 (not_le.mp h128).le h127
                        · -- right
                          by_cases h129 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h130 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B072.c1456_pos ha1 h3 (not_le.mp h127).le h130
                            · -- right
                              exact CKLaneC2R.Cells.S00.B072.c1457_pos ha1 h3 (not_le.mp h130).le h129
                          · -- right
                            by_cases h131 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1472_pos ha1 h3 (not_le.mp h129).le h131
                            · -- right
                              by_cases h132 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B074.c1490_pos ha1 h3 (not_le.mp h131).le h132
                              · -- right
                                exact CKLaneC2R.Cells.S00.B074.c1491_pos ha1 h3 (not_le.mp h132).le hz2
        · -- right
          by_cases h133 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h134 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h135 : a ≤ ((99/640 : ℚ) : ℝ)
              · -- left
                by_cases h136 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h137 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h138 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h139 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h140 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h141 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B068.c1378_pos (not_le.mp h3).le h135 hz1 h141
                          · -- right
                            exact CKLaneC2R.Cells.S00.B068.c1379_pos (not_le.mp h3).le h135 (not_le.mp h141).le h140
                        · -- right
                          by_cases h142 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1382_pos (not_le.mp h3).le h135 (not_le.mp h140).le h142
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1383_pos (not_le.mp h3).le h135 (not_le.mp h142).le h139
                      · -- right
                        by_cases h143 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1062_pos (not_le.mp h3).le h135 (not_le.mp h139).le h143
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1064_pos (not_le.mp h3).le h135 (not_le.mp h143).le h138
                    · -- right
                      by_cases h144 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h145 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1080_pos (not_le.mp h3).le h135 (not_le.mp h138).le h145
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1082_pos (not_le.mp h3).le h135 (not_le.mp h145).le h144
                      · -- right
                        by_cases h146 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1088_pos (not_le.mp h3).le h135 (not_le.mp h144).le h146
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1090_pos (not_le.mp h3).le h135 (not_le.mp h146).le h137
                  · -- right
                    by_cases h147 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h148 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h149 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1116_pos (not_le.mp h3).le h135 (not_le.mp h137).le h149
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1118_pos (not_le.mp h3).le h135 (not_le.mp h149).le h148
                      · -- right
                        by_cases h150 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1120_pos (not_le.mp h3).le h135 (not_le.mp h148).le h150
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1121_pos (not_le.mp h3).le h135 (not_le.mp h150).le h147
                    · -- right
                      by_cases h151 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        by_cases h152 : z ≤ ((22877/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1128_pos (not_le.mp h3).le h135 (not_le.mp h147).le h152
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1129_pos (not_le.mp h3).le h135 (not_le.mp h152).le h151
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c674_pos (not_le.mp h3).le h135 (not_le.mp h151).le h136
                · -- right
                  by_cases h153 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h154 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h155 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c713_pos (not_le.mp h3).le h135 (not_le.mp h136).le h155
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c715_pos (not_le.mp h3).le h135 (not_le.mp h155).le h154
                    · -- right
                      by_cases h156 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c721_pos (not_le.mp h3).le h135 (not_le.mp h154).le h156
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c723_pos (not_le.mp h3).le h135 (not_le.mp h156).le h153
                  · -- right
                    by_cases h157 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h158 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c745_pos (not_le.mp h3).le h135 (not_le.mp h153).le h158
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c747_pos (not_le.mp h3).le h135 (not_le.mp h158).le h157
                    · -- right
                      by_cases h159 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c753_pos (not_le.mp h3).le h135 (not_le.mp h157).le h159
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c755_pos (not_le.mp h3).le h135 (not_le.mp h159).le h134
              · -- right
                by_cases h160 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h161 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h162 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h163 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h164 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h165 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1380_pos (not_le.mp h135).le h2 hz1 h165
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1381_pos (not_le.mp h135).le h2 (not_le.mp h165).le h164
                        · -- right
                          by_cases h166 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1384_pos (not_le.mp h135).le h2 (not_le.mp h164).le h166
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1385_pos (not_le.mp h135).le h2 (not_le.mp h166).le h163
                      · -- right
                        by_cases h167 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1063_pos (not_le.mp h135).le h2 (not_le.mp h163).le h167
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1065_pos (not_le.mp h135).le h2 (not_le.mp h167).le h162
                    · -- right
                      by_cases h168 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h169 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1081_pos (not_le.mp h135).le h2 (not_le.mp h162).le h169
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1083_pos (not_le.mp h135).le h2 (not_le.mp h169).le h168
                      · -- right
                        by_cases h170 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1089_pos (not_le.mp h135).le h2 (not_le.mp h168).le h170
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1091_pos (not_le.mp h135).le h2 (not_le.mp h170).le h161
                  · -- right
                    by_cases h171 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h172 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h173 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1117_pos (not_le.mp h135).le h2 (not_le.mp h161).le h173
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1119_pos (not_le.mp h135).le h2 (not_le.mp h173).le h172
                      · -- right
                        by_cases h174 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1122_pos (not_le.mp h135).le h2 (not_le.mp h172).le h174
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1123_pos (not_le.mp h135).le h2 (not_le.mp h174).le h171
                    · -- right
                      by_cases h175 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        by_cases h176 : z ≤ ((22877/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1130_pos (not_le.mp h135).le h2 (not_le.mp h171).le h176
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1131_pos (not_le.mp h135).le h2 (not_le.mp h176).le h175
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c675_pos (not_le.mp h135).le h2 (not_le.mp h175).le h160
                · -- right
                  by_cases h177 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h178 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h179 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c714_pos (not_le.mp h135).le h2 (not_le.mp h160).le h179
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c716_pos (not_le.mp h135).le h2 (not_le.mp h179).le h178
                    · -- right
                      by_cases h180 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c722_pos (not_le.mp h135).le h2 (not_le.mp h178).le h180
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c724_pos (not_le.mp h135).le h2 (not_le.mp h180).le h177
                  · -- right
                    by_cases h181 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h182 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c746_pos (not_le.mp h135).le h2 (not_le.mp h177).le h182
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c748_pos (not_le.mp h135).le h2 (not_le.mp h182).le h181
                    · -- right
                      by_cases h183 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c754_pos (not_le.mp h135).le h2 (not_le.mp h181).le h183
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c756_pos (not_le.mp h135).le h2 (not_le.mp h183).le h134
            · -- right
              by_cases h184 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h185 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h186 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h187 : a ≤ ((99/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h188 : z ≤ ((841/2560 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c813_pos (not_le.mp h3).le h187 (not_le.mp h134).le h188
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c815_pos (not_le.mp h3).le h187 (not_le.mp h188).le h186
                    · -- right
                      by_cases h189 : z ≤ ((841/2560 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c814_pos (not_le.mp h187).le h2 (not_le.mp h134).le h189
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c816_pos (not_le.mp h187).le h2 (not_le.mp h189).le h186
                  · -- right
                    by_cases h190 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h191 : a ≤ ((99/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c821_pos (not_le.mp h3).le h191 (not_le.mp h186).le h190
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c822_pos (not_le.mp h191).le h2 (not_le.mp h186).le h190
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c81_pos (not_le.mp h3).le h2 (not_le.mp h190).le h185
                · -- right
                  by_cases h192 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h193 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c89_pos (not_le.mp h3).le h2 (not_le.mp h185).le h193
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c90_pos (not_le.mp h3).le h2 (not_le.mp h193).le h192
                  · -- right
                    by_cases h194 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c93_pos (not_le.mp h3).le h2 (not_le.mp h192).le h194
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c94_pos (not_le.mp h3).le h2 (not_le.mp h194).le h184
              · -- right
                by_cases h195 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h196 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h197 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c105_pos (not_le.mp h3).le h2 (not_le.mp h184).le h197
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c106_pos (not_le.mp h3).le h2 (not_le.mp h197).le h196
                  · -- right
                    by_cases h198 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c109_pos (not_le.mp h3).le h2 (not_le.mp h196).le h198
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c110_pos (not_le.mp h3).le h2 (not_le.mp h198).le h195
                · -- right
                  by_cases h199 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h200 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c121_pos (not_le.mp h3).le h2 (not_le.mp h195).le h200
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c122_pos (not_le.mp h3).le h2 (not_le.mp h200).le h199
                  · -- right
                    by_cases h201 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c125_pos (not_le.mp h3).le h2 (not_le.mp h199).le h201
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c126_pos (not_le.mp h3).le h2 (not_le.mp h201).le h133
          · -- right
            by_cases h202 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h203 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h204 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h205 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h206 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c347_pos (not_le.mp h3).le h2 (not_le.mp h133).le h206
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c348_pos (not_le.mp h3).le h2 (not_le.mp h206).le h205
                  · -- right
                    by_cases h207 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c351_pos (not_le.mp h3).le h2 (not_le.mp h205).le h207
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c352_pos (not_le.mp h3).le h2 (not_le.mp h207).le h204
                · -- right
                  by_cases h208 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h209 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c363_pos (not_le.mp h3).le h2 (not_le.mp h204).le h209
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c364_pos (not_le.mp h3).le h2 (not_le.mp h209).le h208
                  · -- right
                    by_cases h210 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c367_pos (not_le.mp h3).le h2 (not_le.mp h208).le h210
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c368_pos (not_le.mp h3).le h2 (not_le.mp h210).le h203
              · -- right
                by_cases h211 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h212 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h213 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c411_pos (not_le.mp h3).le h2 (not_le.mp h203).le h213
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c412_pos (not_le.mp h3).le h2 (not_le.mp h213).le h212
                  · -- right
                    by_cases h214 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c415_pos (not_le.mp h3).le h2 (not_le.mp h212).le h214
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c416_pos (not_le.mp h3).le h2 (not_le.mp h214).le h211
                · -- right
                  by_cases h215 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h216 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c427_pos (not_le.mp h3).le h2 (not_le.mp h211).le h216
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c428_pos (not_le.mp h3).le h2 (not_le.mp h216).le h215
                  · -- right
                    by_cases h217 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c431_pos (not_le.mp h3).le h2 (not_le.mp h215).le h217
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c432_pos (not_le.mp h3).le h2 (not_le.mp h217).le h202
            · -- right
              by_cases h218 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h219 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h220 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h221 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c519_pos (not_le.mp h3).le h2 (not_le.mp h202).le h221
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c520_pos (not_le.mp h3).le h2 (not_le.mp h221).le h220
                  · -- right
                    by_cases h222 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c523_pos (not_le.mp h3).le h2 (not_le.mp h220).le h222
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c524_pos (not_le.mp h3).le h2 (not_le.mp h222).le h219
                · -- right
                  by_cases h223 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h224 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c550_pos (not_le.mp h3).le h2 (not_le.mp h219).le h224
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c551_pos (not_le.mp h3).le h2 (not_le.mp h224).le h223
                  · -- right
                    by_cases h225 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c556_pos (not_le.mp h3).le h2 (not_le.mp h223).le h225
                    · -- right
                      by_cases h226 : z ≤ ((112351/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c927_pos (not_le.mp h3).le h2 (not_le.mp h225).le h226
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c928_pos (not_le.mp h3).le h2 (not_le.mp h226).le h218
              · -- right
                by_cases h227 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h228 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h229 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h230 : z ≤ ((114177/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c931_pos (not_le.mp h3).le h2 (not_le.mp h218).le h230
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c932_pos (not_le.mp h3).le h2 (not_le.mp h230).le h229
                    · -- right
                      by_cases h231 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c935_pos (not_le.mp h3).le h2 (not_le.mp h229).le h231
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c936_pos (not_le.mp h3).le h2 (not_le.mp h231).le h228
                  · -- right
                    by_cases h232 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h233 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c947_pos (not_le.mp h3).le h2 (not_le.mp h228).le h233
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c948_pos (not_le.mp h3).le h2 (not_le.mp h233).le h232
                    · -- right
                      by_cases h234 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c951_pos (not_le.mp h3).le h2 (not_le.mp h232).le h234
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c952_pos (not_le.mp h3).le h2 (not_le.mp h234).le h227
                · -- right
                  by_cases h235 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h236 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h237 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c996_pos (not_le.mp h3).le h2 (not_le.mp h227).le h237
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c998_pos (not_le.mp h3).le h2 (not_le.mp h237).le h236
                    · -- right
                      by_cases h238 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1003_pos (not_le.mp h3).le h2 (not_le.mp h236).le h238
                      · -- right
                        by_cases h239 : z ≤ ((247527/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1293_pos (not_le.mp h3).le h2 (not_le.mp h238).le h239
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1294_pos (not_le.mp h3).le h2 (not_le.mp h239).le h235
                  · -- right
                    by_cases h240 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h241 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h242 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1301_pos (not_le.mp h3).le h2 (not_le.mp h235).le h242
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1302_pos (not_le.mp h3).le h2 (not_le.mp h242).le h241
                      · -- right
                        by_cases h243 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1308_pos (not_le.mp h3).le h2 (not_le.mp h241).le h243
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1310_pos (not_le.mp h3).le h2 (not_le.mp h243).le h240
                    · -- right
                      by_cases h244 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h245 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1343_pos (not_le.mp h3).le h2 (not_le.mp h240).le h245
                        · -- right
                          by_cases h246 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1408_pos (not_le.mp h3).le h2 (not_le.mp h245).le h246
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1409_pos (not_le.mp h3).le h2 (not_le.mp h246).le h244
                      · -- right
                        by_cases h247 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h248 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1421_pos (not_le.mp h3).le h2 (not_le.mp h244).le h248
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1423_pos (not_le.mp h3).le h2 (not_le.mp h248).le h247
                        · -- right
                          by_cases h249 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h250 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B072.c1458_pos (not_le.mp h3).le h2 (not_le.mp h247).le h250
                            · -- right
                              exact CKLaneC2R.Cells.S00.B072.c1459_pos (not_le.mp h3).le h2 (not_le.mp h250).le h249
                          · -- right
                            by_cases h251 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1473_pos (not_le.mp h3).le h2 (not_le.mp h249).le h251
                            · -- right
                              by_cases h252 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B074.c1492_pos (not_le.mp h3).le h2 (not_le.mp h251).le h252
                              · -- right
                                exact CKLaneC2R.Cells.S00.B074.c1493_pos (not_le.mp h3).le h2 (not_le.mp h252).le hz2
      · -- right
        by_cases h253 : a ≤ ((51/320 : ℚ) : ℝ)
        · -- left
          by_cases h254 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h255 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h256 : a ≤ ((101/640 : ℚ) : ℝ)
              · -- left
                by_cases h257 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h258 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h259 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h260 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h261 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h262 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1390_pos (not_le.mp h2).le h256 hz1 h262
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1391_pos (not_le.mp h2).le h256 (not_le.mp h262).le h261
                        · -- right
                          by_cases h263 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1394_pos (not_le.mp h2).le h256 (not_le.mp h261).le h263
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1395_pos (not_le.mp h2).le h256 (not_le.mp h263).le h260
                      · -- right
                        by_cases h264 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1068_pos (not_le.mp h2).le h256 (not_le.mp h260).le h264
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1070_pos (not_le.mp h2).le h256 (not_le.mp h264).le h259
                    · -- right
                      by_cases h265 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h266 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1092_pos (not_le.mp h2).le h256 (not_le.mp h259).le h266
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1094_pos (not_le.mp h2).le h256 (not_le.mp h266).le h265
                      · -- right
                        by_cases h267 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1100_pos (not_le.mp h2).le h256 (not_le.mp h265).le h267
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1102_pos (not_le.mp h2).le h256 (not_le.mp h267).le h258
                  · -- right
                    by_cases h268 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h269 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h270 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1132_pos (not_le.mp h2).le h256 (not_le.mp h258).le h270
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1134_pos (not_le.mp h2).le h256 (not_le.mp h270).le h269
                      · -- right
                        by_cases h271 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1136_pos (not_le.mp h2).le h256 (not_le.mp h269).le h271
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1137_pos (not_le.mp h2).le h256 (not_le.mp h271).le h268
                    · -- right
                      by_cases h272 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B033.c676_pos (not_le.mp h2).le h256 (not_le.mp h268).le h272
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c678_pos (not_le.mp h2).le h256 (not_le.mp h272).le h257
                · -- right
                  by_cases h273 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h274 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h275 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c725_pos (not_le.mp h2).le h256 (not_le.mp h257).le h275
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c727_pos (not_le.mp h2).le h256 (not_le.mp h275).le h274
                    · -- right
                      by_cases h276 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c733_pos (not_le.mp h2).le h256 (not_le.mp h274).le h276
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c735_pos (not_le.mp h2).le h256 (not_le.mp h276).le h273
                  · -- right
                    by_cases h277 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h278 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c757_pos (not_le.mp h2).le h256 (not_le.mp h273).le h278
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c759_pos (not_le.mp h2).le h256 (not_le.mp h278).le h277
                    · -- right
                      by_cases h279 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c765_pos (not_le.mp h2).le h256 (not_le.mp h277).le h279
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c767_pos (not_le.mp h2).le h256 (not_le.mp h279).le h255
              · -- right
                by_cases h280 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h281 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h282 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h283 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h284 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h285 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1392_pos (not_le.mp h256).le h253 hz1 h285
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1393_pos (not_le.mp h256).le h253 (not_le.mp h285).le h284
                        · -- right
                          by_cases h286 : z ≤ ((4951/51200 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1396_pos (not_le.mp h256).le h253 (not_le.mp h284).le h286
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1397_pos (not_le.mp h256).le h253 (not_le.mp h286).le h283
                      · -- right
                        by_cases h287 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1069_pos (not_le.mp h256).le h253 (not_le.mp h283).le h287
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1071_pos (not_le.mp h256).le h253 (not_le.mp h287).le h282
                    · -- right
                      by_cases h288 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h289 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1093_pos (not_le.mp h256).le h253 (not_le.mp h282).le h289
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1095_pos (not_le.mp h256).le h253 (not_le.mp h289).le h288
                      · -- right
                        by_cases h290 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1101_pos (not_le.mp h256).le h253 (not_le.mp h288).le h290
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1103_pos (not_le.mp h256).le h253 (not_le.mp h290).le h281
                  · -- right
                    by_cases h291 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h292 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h293 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1133_pos (not_le.mp h256).le h253 (not_le.mp h281).le h293
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1135_pos (not_le.mp h256).le h253 (not_le.mp h293).le h292
                      · -- right
                        by_cases h294 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B056.c1138_pos (not_le.mp h256).le h253 (not_le.mp h292).le h294
                        · -- right
                          exact CKLaneC2R.Cells.S00.B056.c1139_pos (not_le.mp h256).le h253 (not_le.mp h294).le h291
                    · -- right
                      by_cases h295 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B033.c677_pos (not_le.mp h256).le h253 (not_le.mp h291).le h295
                      · -- right
                        exact CKLaneC2R.Cells.S00.B033.c679_pos (not_le.mp h256).le h253 (not_le.mp h295).le h280
                · -- right
                  by_cases h296 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h297 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h298 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c726_pos (not_le.mp h256).le h253 (not_le.mp h280).le h298
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c728_pos (not_le.mp h256).le h253 (not_le.mp h298).le h297
                    · -- right
                      by_cases h299 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c734_pos (not_le.mp h256).le h253 (not_le.mp h297).le h299
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c736_pos (not_le.mp h256).le h253 (not_le.mp h299).le h296
                  · -- right
                    by_cases h300 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h301 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B037.c758_pos (not_le.mp h256).le h253 (not_le.mp h296).le h301
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c760_pos (not_le.mp h256).le h253 (not_le.mp h301).le h300
                    · -- right
                      by_cases h302 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c766_pos (not_le.mp h256).le h253 (not_le.mp h300).le h302
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c768_pos (not_le.mp h256).le h253 (not_le.mp h302).le h255
            · -- right
              by_cases h303 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h304 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h305 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h306 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      by_cases h307 : a ≤ ((101/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c823_pos (not_le.mp h2).le h307 (not_le.mp h255).le h306
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c824_pos (not_le.mp h307).le h253 (not_le.mp h255).le h306
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c82_pos (not_le.mp h2).le h253 (not_le.mp h306).le h305
                  · -- right
                    by_cases h308 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c85_pos (not_le.mp h2).le h253 (not_le.mp h305).le h308
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c86_pos (not_le.mp h2).le h253 (not_le.mp h308).le h304
                · -- right
                  by_cases h309 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h310 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c95_pos (not_le.mp h2).le h253 (not_le.mp h304).le h310
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c96_pos (not_le.mp h2).le h253 (not_le.mp h310).le h309
                  · -- right
                    by_cases h311 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c99_pos (not_le.mp h2).le h253 (not_le.mp h309).le h311
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c100_pos (not_le.mp h2).le h253 (not_le.mp h311).le h303
              · -- right
                by_cases h312 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h313 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h314 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c111_pos (not_le.mp h2).le h253 (not_le.mp h303).le h314
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c112_pos (not_le.mp h2).le h253 (not_le.mp h314).le h313
                  · -- right
                    by_cases h315 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c115_pos (not_le.mp h2).le h253 (not_le.mp h313).le h315
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c116_pos (not_le.mp h2).le h253 (not_le.mp h315).le h312
                · -- right
                  by_cases h316 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h317 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c127_pos (not_le.mp h2).le h253 (not_le.mp h312).le h317
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c128_pos (not_le.mp h2).le h253 (not_le.mp h317).le h316
                  · -- right
                    by_cases h318 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c131_pos (not_le.mp h2).le h253 (not_le.mp h316).le h318
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c132_pos (not_le.mp h2).le h253 (not_le.mp h318).le h254
          · -- right
            by_cases h319 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h320 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h321 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h322 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h323 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c353_pos (not_le.mp h2).le h253 (not_le.mp h254).le h323
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c354_pos (not_le.mp h2).le h253 (not_le.mp h323).le h322
                  · -- right
                    by_cases h324 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c357_pos (not_le.mp h2).le h253 (not_le.mp h322).le h324
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c358_pos (not_le.mp h2).le h253 (not_le.mp h324).le h321
                · -- right
                  by_cases h325 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h326 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c369_pos (not_le.mp h2).le h253 (not_le.mp h321).le h326
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c370_pos (not_le.mp h2).le h253 (not_le.mp h326).le h325
                  · -- right
                    by_cases h327 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c373_pos (not_le.mp h2).le h253 (not_le.mp h325).le h327
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c374_pos (not_le.mp h2).le h253 (not_le.mp h327).le h320
              · -- right
                by_cases h328 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h329 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h330 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c417_pos (not_le.mp h2).le h253 (not_le.mp h320).le h330
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c418_pos (not_le.mp h2).le h253 (not_le.mp h330).le h329
                  · -- right
                    by_cases h331 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c421_pos (not_le.mp h2).le h253 (not_le.mp h329).le h331
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c422_pos (not_le.mp h2).le h253 (not_le.mp h331).le h328
                · -- right
                  by_cases h332 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h333 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c433_pos (not_le.mp h2).le h253 (not_le.mp h328).le h333
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c434_pos (not_le.mp h2).le h253 (not_le.mp h333).le h332
                  · -- right
                    by_cases h334 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c437_pos (not_le.mp h2).le h253 (not_le.mp h332).le h334
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c438_pos (not_le.mp h2).le h253 (not_le.mp h334).le h319
            · -- right
              by_cases h335 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h336 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h337 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h338 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c525_pos (not_le.mp h2).le h253 (not_le.mp h319).le h338
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c526_pos (not_le.mp h2).le h253 (not_le.mp h338).le h337
                  · -- right
                    by_cases h339 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c529_pos (not_le.mp h2).le h253 (not_le.mp h337).le h339
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c530_pos (not_le.mp h2).le h253 (not_le.mp h339).le h336
                · -- right
                  by_cases h340 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h341 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c552_pos (not_le.mp h2).le h253 (not_le.mp h336).le h341
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c553_pos (not_le.mp h2).le h253 (not_le.mp h341).le h340
                  · -- right
                    by_cases h342 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c557_pos (not_le.mp h2).le h253 (not_le.mp h340).le h342
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c559_pos (not_le.mp h2).le h253 (not_le.mp h342).le h335
              · -- right
                by_cases h343 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h344 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h345 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h346 : z ≤ ((114177/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c937_pos (not_le.mp h2).le h253 (not_le.mp h335).le h346
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c938_pos (not_le.mp h2).le h253 (not_le.mp h346).le h345
                    · -- right
                      by_cases h347 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c941_pos (not_le.mp h2).le h253 (not_le.mp h345).le h347
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c942_pos (not_le.mp h2).le h253 (not_le.mp h347).le h344
                  · -- right
                    by_cases h348 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h349 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c953_pos (not_le.mp h2).le h253 (not_le.mp h344).le h349
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c954_pos (not_le.mp h2).le h253 (not_le.mp h349).le h348
                    · -- right
                      by_cases h350 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c957_pos (not_le.mp h2).le h253 (not_le.mp h348).le h350
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c958_pos (not_le.mp h2).le h253 (not_le.mp h350).le h343
                · -- right
                  by_cases h351 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h352 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h353 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c999_pos (not_le.mp h2).le h253 (not_le.mp h343).le h353
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1001_pos (not_le.mp h2).le h253 (not_le.mp h353).le h352
                    · -- right
                      by_cases h354 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1004_pos (not_le.mp h2).le h253 (not_le.mp h352).le h354
                      · -- right
                        by_cases h355 : z ≤ ((247527/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1295_pos (not_le.mp h2).le h253 (not_le.mp h354).le h355
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1296_pos (not_le.mp h2).le h253 (not_le.mp h355).le h351
                  · -- right
                    by_cases h356 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h357 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h358 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1303_pos (not_le.mp h2).le h253 (not_le.mp h351).le h358
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1304_pos (not_le.mp h2).le h253 (not_le.mp h358).le h357
                      · -- right
                        by_cases h359 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1311_pos (not_le.mp h2).le h253 (not_le.mp h357).le h359
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1313_pos (not_le.mp h2).le h253 (not_le.mp h359).le h356
                    · -- right
                      by_cases h360 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h361 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1344_pos (not_le.mp h2).le h253 (not_le.mp h356).le h361
                        · -- right
                          by_cases h362 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1410_pos (not_le.mp h2).le h253 (not_le.mp h361).le h362
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1411_pos (not_le.mp h2).le h253 (not_le.mp h362).le h360
                      · -- right
                        by_cases h363 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h364 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1424_pos (not_le.mp h2).le h253 (not_le.mp h360).le h364
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1426_pos (not_le.mp h2).le h253 (not_le.mp h364).le h363
                        · -- right
                          by_cases h365 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h366 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1460_pos (not_le.mp h2).le h253 (not_le.mp h363).le h366
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1461_pos (not_le.mp h2).le h253 (not_le.mp h366).le h365
                          · -- right
                            by_cases h367 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1474_pos (not_le.mp h2).le h253 (not_le.mp h365).le h367
                            · -- right
                              by_cases h368 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B074.c1494_pos (not_le.mp h2).le h253 (not_le.mp h367).le h368
                              · -- right
                                exact CKLaneC2R.Cells.S00.B074.c1495_pos (not_le.mp h2).le h253 (not_le.mp h368).le hz2
        · -- right
          by_cases h369 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h370 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h371 : a ≤ ((103/640 : ℚ) : ℝ)
              · -- left
                by_cases h372 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h373 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h374 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h375 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h376 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h377 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B069.c1398_pos (not_le.mp h253).le h371 hz1 h377
                          · -- right
                            exact CKLaneC2R.Cells.S00.B069.c1399_pos (not_le.mp h253).le h371 (not_le.mp h377).le h376
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1066_pos (not_le.mp h253).le h371 (not_le.mp h376).le h375
                      · -- right
                        by_cases h378 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1072_pos (not_le.mp h253).le h371 (not_le.mp h375).le h378
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1074_pos (not_le.mp h253).le h371 (not_le.mp h378).le h374
                    · -- right
                      by_cases h379 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h380 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1096_pos (not_le.mp h253).le h371 (not_le.mp h374).le h380
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1098_pos (not_le.mp h253).le h371 (not_le.mp h380).le h379
                      · -- right
                        by_cases h381 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1104_pos (not_le.mp h253).le h371 (not_le.mp h379).le h381
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1106_pos (not_le.mp h253).le h371 (not_le.mp h381).le h373
                  · -- right
                    by_cases h382 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h383 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h384 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1140_pos (not_le.mp h253).le h371 (not_le.mp h373).le h384
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1142_pos (not_le.mp h253).le h371 (not_le.mp h384).le h383
                      · -- right
                        by_cases h385 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1144_pos (not_le.mp h253).le h371 (not_le.mp h383).le h385
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1145_pos (not_le.mp h253).le h371 (not_le.mp h385).le h382
                    · -- right
                      by_cases h386 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c680_pos (not_le.mp h253).le h371 (not_le.mp h382).le h386
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c682_pos (not_le.mp h253).le h371 (not_le.mp h386).le h372
                · -- right
                  by_cases h387 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h388 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h389 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c729_pos (not_le.mp h253).le h371 (not_le.mp h372).le h389
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c731_pos (not_le.mp h253).le h371 (not_le.mp h389).le h388
                    · -- right
                      by_cases h390 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c737_pos (not_le.mp h253).le h371 (not_le.mp h388).le h390
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c739_pos (not_le.mp h253).le h371 (not_le.mp h390).le h387
                  · -- right
                    by_cases h391 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h392 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c761_pos (not_le.mp h253).le h371 (not_le.mp h387).le h392
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c763_pos (not_le.mp h253).le h371 (not_le.mp h392).le h391
                    · -- right
                      by_cases h393 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c769_pos (not_le.mp h253).le h371 (not_le.mp h391).le h393
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c771_pos (not_le.mp h253).le h371 (not_le.mp h393).le h370
              · -- right
                by_cases h394 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h395 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h396 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h397 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h398 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h399 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1400_pos (not_le.mp h371).le h1 hz1 h399
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1401_pos (not_le.mp h371).le h1 (not_le.mp h399).le h398
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1067_pos (not_le.mp h371).le h1 (not_le.mp h398).le h397
                      · -- right
                        by_cases h400 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B053.c1073_pos (not_le.mp h371).le h1 (not_le.mp h397).le h400
                        · -- right
                          exact CKLaneC2R.Cells.S00.B053.c1075_pos (not_le.mp h371).le h1 (not_le.mp h400).le h396
                    · -- right
                      by_cases h401 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h402 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B054.c1097_pos (not_le.mp h371).le h1 (not_le.mp h396).le h402
                        · -- right
                          exact CKLaneC2R.Cells.S00.B054.c1099_pos (not_le.mp h371).le h1 (not_le.mp h402).le h401
                      · -- right
                        by_cases h403 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B055.c1105_pos (not_le.mp h371).le h1 (not_le.mp h401).le h403
                        · -- right
                          exact CKLaneC2R.Cells.S00.B055.c1107_pos (not_le.mp h371).le h1 (not_le.mp h403).le h395
                  · -- right
                    by_cases h404 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h405 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h406 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1141_pos (not_le.mp h371).le h1 (not_le.mp h395).le h406
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1143_pos (not_le.mp h371).le h1 (not_le.mp h406).le h405
                      · -- right
                        by_cases h407 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1146_pos (not_le.mp h371).le h1 (not_le.mp h405).le h407
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1147_pos (not_le.mp h371).le h1 (not_le.mp h407).le h404
                    · -- right
                      by_cases h408 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c681_pos (not_le.mp h371).le h1 (not_le.mp h404).le h408
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c683_pos (not_le.mp h371).le h1 (not_le.mp h408).le h394
                · -- right
                  by_cases h409 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h410 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h411 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c730_pos (not_le.mp h371).le h1 (not_le.mp h394).le h411
                      · -- right
                        exact CKLaneC2R.Cells.S00.B036.c732_pos (not_le.mp h371).le h1 (not_le.mp h411).le h410
                    · -- right
                      by_cases h412 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B036.c738_pos (not_le.mp h371).le h1 (not_le.mp h410).le h412
                      · -- right
                        exact CKLaneC2R.Cells.S00.B037.c740_pos (not_le.mp h371).le h1 (not_le.mp h412).le h409
                  · -- right
                    by_cases h413 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h414 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c762_pos (not_le.mp h371).le h1 (not_le.mp h409).le h414
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c764_pos (not_le.mp h371).le h1 (not_le.mp h414).le h413
                    · -- right
                      by_cases h415 : z ≤ ((19199/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c770_pos (not_le.mp h371).le h1 (not_le.mp h413).le h415
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c772_pos (not_le.mp h371).le h1 (not_le.mp h415).le h370
            · -- right
              by_cases h416 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h417 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h418 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h419 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c83_pos (not_le.mp h253).le h1 (not_le.mp h370).le h419
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c84_pos (not_le.mp h253).le h1 (not_le.mp h419).le h418
                  · -- right
                    by_cases h420 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c87_pos (not_le.mp h253).le h1 (not_le.mp h418).le h420
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c88_pos (not_le.mp h253).le h1 (not_le.mp h420).le h417
                · -- right
                  by_cases h421 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h422 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B004.c97_pos (not_le.mp h253).le h1 (not_le.mp h417).le h422
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c98_pos (not_le.mp h253).le h1 (not_le.mp h422).le h421
                  · -- right
                    by_cases h423 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c101_pos (not_le.mp h253).le h1 (not_le.mp h421).le h423
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c102_pos (not_le.mp h253).le h1 (not_le.mp h423).le h416
              · -- right
                by_cases h424 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h425 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h426 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c113_pos (not_le.mp h253).le h1 (not_le.mp h416).le h426
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c114_pos (not_le.mp h253).le h1 (not_le.mp h426).le h425
                  · -- right
                    by_cases h427 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B005.c117_pos (not_le.mp h253).le h1 (not_le.mp h425).le h427
                    · -- right
                      exact CKLaneC2R.Cells.S00.B005.c118_pos (not_le.mp h253).le h1 (not_le.mp h427).le h424
                · -- right
                  by_cases h428 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h429 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c129_pos (not_le.mp h253).le h1 (not_le.mp h424).le h429
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c130_pos (not_le.mp h253).le h1 (not_le.mp h429).le h428
                  · -- right
                    by_cases h430 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c133_pos (not_le.mp h253).le h1 (not_le.mp h428).le h430
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c134_pos (not_le.mp h253).le h1 (not_le.mp h430).le h369
          · -- right
            by_cases h431 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h432 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h433 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h434 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h435 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c355_pos (not_le.mp h253).le h1 (not_le.mp h369).le h435
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c356_pos (not_le.mp h253).le h1 (not_le.mp h435).le h434
                  · -- right
                    by_cases h436 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c359_pos (not_le.mp h253).le h1 (not_le.mp h434).le h436
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c360_pos (not_le.mp h253).le h1 (not_le.mp h436).le h433
                · -- right
                  by_cases h437 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h438 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c371_pos (not_le.mp h253).le h1 (not_le.mp h433).le h438
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c372_pos (not_le.mp h253).le h1 (not_le.mp h438).le h437
                  · -- right
                    by_cases h439 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c375_pos (not_le.mp h253).le h1 (not_le.mp h437).le h439
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c376_pos (not_le.mp h253).le h1 (not_le.mp h439).le h432
              · -- right
                by_cases h440 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h441 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h442 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c419_pos (not_le.mp h253).le h1 (not_le.mp h432).le h442
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c420_pos (not_le.mp h253).le h1 (not_le.mp h442).le h441
                  · -- right
                    by_cases h443 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c423_pos (not_le.mp h253).le h1 (not_le.mp h441).le h443
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c424_pos (not_le.mp h253).le h1 (not_le.mp h443).le h440
                · -- right
                  by_cases h444 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h445 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c435_pos (not_le.mp h253).le h1 (not_le.mp h440).le h445
                    · -- right
                      exact CKLaneC2R.Cells.S00.B021.c436_pos (not_le.mp h253).le h1 (not_le.mp h445).le h444
                  · -- right
                    by_cases h446 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B021.c439_pos (not_le.mp h253).le h1 (not_le.mp h444).le h446
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c440_pos (not_le.mp h253).le h1 (not_le.mp h446).le h431
            · -- right
              by_cases h447 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h448 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h449 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h450 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c527_pos (not_le.mp h253).le h1 (not_le.mp h431).le h450
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c528_pos (not_le.mp h253).le h1 (not_le.mp h450).le h449
                  · -- right
                    by_cases h451 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c531_pos (not_le.mp h253).le h1 (not_le.mp h449).le h451
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c532_pos (not_le.mp h253).le h1 (not_le.mp h451).le h448
                · -- right
                  by_cases h452 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h453 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c554_pos (not_le.mp h253).le h1 (not_le.mp h448).le h453
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c555_pos (not_le.mp h253).le h1 (not_le.mp h453).le h452
                  · -- right
                    by_cases h454 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c558_pos (not_le.mp h253).le h1 (not_le.mp h452).le h454
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c560_pos (not_le.mp h253).le h1 (not_le.mp h454).le h447
              · -- right
                by_cases h455 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h456 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h457 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h458 : z ≤ ((114177/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B046.c939_pos (not_le.mp h253).le h1 (not_le.mp h447).le h458
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c940_pos (not_le.mp h253).le h1 (not_le.mp h458).le h457
                    · -- right
                      by_cases h459 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c943_pos (not_le.mp h253).le h1 (not_le.mp h457).le h459
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c944_pos (not_le.mp h253).le h1 (not_le.mp h459).le h456
                  · -- right
                    by_cases h460 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h461 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c955_pos (not_le.mp h253).le h1 (not_le.mp h456).le h461
                      · -- right
                        exact CKLaneC2R.Cells.S00.B047.c956_pos (not_le.mp h253).le h1 (not_le.mp h461).le h460
                    · -- right
                      by_cases h462 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B047.c959_pos (not_le.mp h253).le h1 (not_le.mp h460).le h462
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c960_pos (not_le.mp h253).le h1 (not_le.mp h462).le h455
                · -- right
                  by_cases h463 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h464 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h465 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1000_pos (not_le.mp h253).le h1 (not_le.mp h455).le h465
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1002_pos (not_le.mp h253).le h1 (not_le.mp h465).le h464
                    · -- right
                      by_cases h466 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1005_pos (not_le.mp h253).le h1 (not_le.mp h464).le h466
                      · -- right
                        by_cases h467 : z ≤ ((247527/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1297_pos (not_le.mp h253).le h1 (not_le.mp h466).le h467
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1298_pos (not_le.mp h253).le h1 (not_le.mp h467).le h463
                  · -- right
                    by_cases h468 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h469 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h470 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1305_pos (not_le.mp h253).le h1 (not_le.mp h463).le h470
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1306_pos (not_le.mp h253).le h1 (not_le.mp h470).le h469
                      · -- right
                        by_cases h471 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1312_pos (not_le.mp h253).le h1 (not_le.mp h469).le h471
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1314_pos (not_le.mp h253).le h1 (not_le.mp h471).le h468
                    · -- right
                      by_cases h472 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h473 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1345_pos (not_le.mp h253).le h1 (not_le.mp h468).le h473
                        · -- right
                          by_cases h474 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1412_pos (not_le.mp h253).le h1 (not_le.mp h473).le h474
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1413_pos (not_le.mp h253).le h1 (not_le.mp h474).le h472
                      · -- right
                        by_cases h475 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h476 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1425_pos (not_le.mp h253).le h1 (not_le.mp h472).le h476
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1427_pos (not_le.mp h253).le h1 (not_le.mp h476).le h475
                        · -- right
                          by_cases h477 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h478 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1462_pos (not_le.mp h253).le h1 (not_le.mp h475).le h478
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1463_pos (not_le.mp h253).le h1 (not_le.mp h478).le h477
                          · -- right
                            by_cases h479 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1475_pos (not_le.mp h253).le h1 (not_le.mp h477).le h479
                            · -- right
                              by_cases h480 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B074.c1496_pos (not_le.mp h253).le h1 (not_le.mp h479).le h480
                              · -- right
                                exact CKLaneC2R.Cells.S00.B074.c1497_pos (not_le.mp h253).le h1 (not_le.mp h480).le hz2
    · -- right
      by_cases h481 : a ≤ ((27/160 : ℚ) : ℝ)
      · -- left
        by_cases h482 : a ≤ ((53/320 : ℚ) : ℝ)
        · -- left
          by_cases h483 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h484 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h485 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h486 : a ≤ ((21/128 : ℚ) : ℝ)
                · -- left
                  by_cases h487 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h488 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h489 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h490 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          by_cases h491 : z ≤ ((22929/256000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1402_pos (not_le.mp h1).le h486 hz1 h491
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1403_pos (not_le.mp h1).le h486 (not_le.mp h491).le h490
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1149_pos (not_le.mp h1).le h486 (not_le.mp h490).le h489
                      · -- right
                        by_cases h492 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1155_pos (not_le.mp h1).le h486 (not_le.mp h489).le h492
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1157_pos (not_le.mp h1).le h486 (not_le.mp h492).le h488
                    · -- right
                      by_cases h493 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h494 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1179_pos (not_le.mp h1).le h486 (not_le.mp h488).le h494
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1181_pos (not_le.mp h1).le h486 (not_le.mp h494).le h493
                      · -- right
                        by_cases h495 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1187_pos (not_le.mp h1).le h486 (not_le.mp h493).le h495
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1189_pos (not_le.mp h1).le h486 (not_le.mp h495).le h487
                  · -- right
                    by_cases h496 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h497 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h498 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1211_pos (not_le.mp h1).le h486 (not_le.mp h487).le h498
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1213_pos (not_le.mp h1).le h486 (not_le.mp h498).le h497
                      · -- right
                        by_cases h499 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1219_pos (not_le.mp h1).le h486 (not_le.mp h497).le h499
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1221_pos (not_le.mp h1).le h486 (not_le.mp h499).le h496
                    · -- right
                      by_cases h500 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c686_pos (not_le.mp h1).le h486 (not_le.mp h496).le h500
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c688_pos (not_le.mp h1).le h486 (not_le.mp h500).le h485
                · -- right
                  by_cases h501 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h502 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h503 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h504 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1148_pos (not_le.mp h486).le h482 hz1 h504
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1150_pos (not_le.mp h486).le h482 (not_le.mp h504).le h503
                      · -- right
                        by_cases h505 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1156_pos (not_le.mp h486).le h482 (not_le.mp h503).le h505
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1158_pos (not_le.mp h486).le h482 (not_le.mp h505).le h502
                    · -- right
                      by_cases h506 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h507 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1180_pos (not_le.mp h486).le h482 (not_le.mp h502).le h507
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1182_pos (not_le.mp h486).le h482 (not_le.mp h507).le h506
                      · -- right
                        by_cases h508 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1188_pos (not_le.mp h486).le h482 (not_le.mp h506).le h508
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1190_pos (not_le.mp h486).le h482 (not_le.mp h508).le h501
                  · -- right
                    by_cases h509 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h510 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h511 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1212_pos (not_le.mp h486).le h482 (not_le.mp h501).le h511
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1214_pos (not_le.mp h486).le h482 (not_le.mp h511).le h510
                      · -- right
                        by_cases h512 : z ≤ ((21051/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1220_pos (not_le.mp h486).le h482 (not_le.mp h510).le h512
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1222_pos (not_le.mp h486).le h482 (not_le.mp h512).le h509
                    · -- right
                      by_cases h513 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c687_pos (not_le.mp h486).le h482 (not_le.mp h509).le h513
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c689_pos (not_le.mp h486).le h482 (not_le.mp h513).le h485
              · -- right
                by_cases h514 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h515 : a ≤ ((21/128 : ℚ) : ℝ)
                  · -- left
                    by_cases h516 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h517 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c773_pos (not_le.mp h1).le h515 (not_le.mp h485).le h517
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c775_pos (not_le.mp h1).le h515 (not_le.mp h517).le h516
                    · -- right
                      by_cases h518 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c781_pos (not_le.mp h1).le h515 (not_le.mp h516).le h518
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c783_pos (not_le.mp h1).le h515 (not_le.mp h518).le h514
                  · -- right
                    by_cases h519 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h520 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c774_pos (not_le.mp h515).le h482 (not_le.mp h485).le h520
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c776_pos (not_le.mp h515).le h482 (not_le.mp h520).le h519
                    · -- right
                      by_cases h521 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c782_pos (not_le.mp h515).le h482 (not_le.mp h519).le h521
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c784_pos (not_le.mp h515).le h482 (not_le.mp h521).le h514
                · -- right
                  by_cases h522 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h523 : a ≤ ((21/128 : ℚ) : ℝ)
                    · -- left
                      by_cases h524 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c803_pos (not_le.mp h1).le h523 (not_le.mp h514).le h524
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c805_pos (not_le.mp h1).le h523 (not_le.mp h524).le h522
                    · -- right
                      by_cases h525 : z ≤ ((17373/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c804_pos (not_le.mp h523).le h482 (not_le.mp h514).le h525
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c806_pos (not_le.mp h523).le h482 (not_le.mp h525).le h522
                  · -- right
                    by_cases h526 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c69_pos (not_le.mp h1).le h482 (not_le.mp h522).le h526
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c70_pos (not_le.mp h1).le h482 (not_le.mp h526).le h484
            · -- right
              by_cases h527 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h528 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h529 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h530 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c135_pos (not_le.mp h1).le h482 (not_le.mp h484).le h530
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c136_pos (not_le.mp h1).le h482 (not_le.mp h530).le h529
                  · -- right
                    by_cases h531 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c139_pos (not_le.mp h1).le h482 (not_le.mp h529).le h531
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c140_pos (not_le.mp h1).le h482 (not_le.mp h531).le h528
                · -- right
                  by_cases h532 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h533 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c151_pos (not_le.mp h1).le h482 (not_le.mp h528).le h533
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c152_pos (not_le.mp h1).le h482 (not_le.mp h533).le h532
                  · -- right
                    by_cases h534 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c155_pos (not_le.mp h1).le h482 (not_le.mp h532).le h534
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c156_pos (not_le.mp h1).le h482 (not_le.mp h534).le h527
              · -- right
                by_cases h535 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h536 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h537 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c167_pos (not_le.mp h1).le h482 (not_le.mp h527).le h537
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c168_pos (not_le.mp h1).le h482 (not_le.mp h537).le h536
                  · -- right
                    by_cases h538 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c171_pos (not_le.mp h1).le h482 (not_le.mp h536).le h538
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c172_pos (not_le.mp h1).le h482 (not_le.mp h538).le h535
                · -- right
                  by_cases h539 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h540 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c183_pos (not_le.mp h1).le h482 (not_le.mp h535).le h540
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c184_pos (not_le.mp h1).le h482 (not_le.mp h540).le h539
                  · -- right
                    by_cases h541 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c187_pos (not_le.mp h1).le h482 (not_le.mp h539).le h541
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c188_pos (not_le.mp h1).le h482 (not_le.mp h541).le h483
          · -- right
            by_cases h542 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h543 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h544 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h545 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h546 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c377_pos (not_le.mp h1).le h482 (not_le.mp h483).le h546
                    · -- right
                      exact CKLaneC2R.Cells.S00.B018.c378_pos (not_le.mp h1).le h482 (not_le.mp h546).le h545
                  · -- right
                    by_cases h547 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c381_pos (not_le.mp h1).le h482 (not_le.mp h545).le h547
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c382_pos (not_le.mp h1).le h482 (not_le.mp h547).le h544
                · -- right
                  by_cases h548 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h549 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c393_pos (not_le.mp h1).le h482 (not_le.mp h544).le h549
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c394_pos (not_le.mp h1).le h482 (not_le.mp h549).le h548
                  · -- right
                    by_cases h550 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c397_pos (not_le.mp h1).le h482 (not_le.mp h548).le h550
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c398_pos (not_le.mp h1).le h482 (not_le.mp h550).le h543
              · -- right
                by_cases h551 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h552 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h553 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c441_pos (not_le.mp h1).le h482 (not_le.mp h543).le h553
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c442_pos (not_le.mp h1).le h482 (not_le.mp h553).le h552
                  · -- right
                    by_cases h554 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c445_pos (not_le.mp h1).le h482 (not_le.mp h552).le h554
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c446_pos (not_le.mp h1).le h482 (not_le.mp h554).le h551
                · -- right
                  by_cases h555 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h556 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c457_pos (not_le.mp h1).le h482 (not_le.mp h551).le h556
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c458_pos (not_le.mp h1).le h482 (not_le.mp h556).le h555
                  · -- right
                    by_cases h557 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c461_pos (not_le.mp h1).le h482 (not_le.mp h555).le h557
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c462_pos (not_le.mp h1).le h482 (not_le.mp h557).le h542
            · -- right
              by_cases h558 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h559 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h560 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h561 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c533_pos (not_le.mp h1).le h482 (not_le.mp h542).le h561
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c534_pos (not_le.mp h1).le h482 (not_le.mp h561).le h560
                  · -- right
                    by_cases h562 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c537_pos (not_le.mp h1).le h482 (not_le.mp h560).le h562
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c538_pos (not_le.mp h1).le h482 (not_le.mp h562).le h559
                · -- right
                  by_cases h563 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h564 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c561_pos (not_le.mp h1).le h482 (not_le.mp h559).le h564
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c562_pos (not_le.mp h1).le h482 (not_le.mp h564).le h563
                  · -- right
                    by_cases h565 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c569_pos (not_le.mp h1).le h482 (not_le.mp h563).le h565
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c571_pos (not_le.mp h1).le h482 (not_le.mp h565).le h558
              · -- right
                by_cases h566 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h567 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h568 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c639_pos (not_le.mp h1).le h482 (not_le.mp h558).le h568
                    · -- right
                      by_cases h569 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c961_pos (not_le.mp h1).le h482 (not_le.mp h568).le h569
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c962_pos (not_le.mp h1).le h482 (not_le.mp h569).le h567
                  · -- right
                    by_cases h570 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h571 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c965_pos (not_le.mp h1).le h482 (not_le.mp h567).le h571
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c966_pos (not_le.mp h1).le h482 (not_le.mp h571).le h570
                    · -- right
                      by_cases h572 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c969_pos (not_le.mp h1).le h482 (not_le.mp h570).le h572
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c970_pos (not_le.mp h1).le h482 (not_le.mp h572).le h566
                · -- right
                  by_cases h573 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h574 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h575 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1006_pos (not_le.mp h1).le h482 (not_le.mp h566).le h575
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1008_pos (not_le.mp h1).le h482 (not_le.mp h575).le h574
                    · -- right
                      by_cases h576 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1014_pos (not_le.mp h1).le h482 (not_le.mp h574).le h576
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1016_pos (not_le.mp h1).le h482 (not_le.mp h576).le h573
                  · -- right
                    by_cases h577 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h578 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h579 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1315_pos (not_le.mp h1).le h482 (not_le.mp h573).le h579
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1316_pos (not_le.mp h1).le h482 (not_le.mp h579).le h578
                      · -- right
                        by_cases h580 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1323_pos (not_le.mp h1).le h482 (not_le.mp h578).le h580
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1325_pos (not_le.mp h1).le h482 (not_le.mp h580).le h577
                    · -- right
                      by_cases h581 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h582 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1346_pos (not_le.mp h1).le h482 (not_le.mp h577).le h582
                        · -- right
                          by_cases h583 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1414_pos (not_le.mp h1).le h482 (not_le.mp h582).le h583
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1415_pos (not_le.mp h1).le h482 (not_le.mp h583).le h581
                      · -- right
                        by_cases h584 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h585 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1428_pos (not_le.mp h1).le h482 (not_le.mp h581).le h585
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1430_pos (not_le.mp h1).le h482 (not_le.mp h585).le h584
                        · -- right
                          by_cases h586 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h587 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1464_pos (not_le.mp h1).le h482 (not_le.mp h584).le h587
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1465_pos (not_le.mp h1).le h482 (not_le.mp h587).le h586
                          · -- right
                            by_cases h588 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1476_pos (not_le.mp h1).le h482 (not_le.mp h586).le h588
                            · -- right
                              by_cases h589 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B074.c1498_pos (not_le.mp h1).le h482 (not_le.mp h588).le h589
                              · -- right
                                exact CKLaneC2R.Cells.S00.B074.c1499_pos (not_le.mp h1).le h482 (not_le.mp h589).le hz2
        · -- right
          by_cases h590 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h591 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h592 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h593 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h594 : a ≤ ((107/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h595 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h596 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h597 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1151_pos (not_le.mp h482).le h594 hz1 h597
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1153_pos (not_le.mp h482).le h594 (not_le.mp h597).le h596
                      · -- right
                        by_cases h598 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1159_pos (not_le.mp h482).le h594 (not_le.mp h596).le h598
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1161_pos (not_le.mp h482).le h594 (not_le.mp h598).le h595
                    · -- right
                      by_cases h599 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h600 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1183_pos (not_le.mp h482).le h594 (not_le.mp h595).le h600
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1185_pos (not_le.mp h482).le h594 (not_le.mp h600).le h599
                      · -- right
                        by_cases h601 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1191_pos (not_le.mp h482).le h594 (not_le.mp h599).le h601
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1193_pos (not_le.mp h482).le h594 (not_le.mp h601).le h593
                  · -- right
                    by_cases h602 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h603 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h604 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B057.c1152_pos (not_le.mp h594).le h481 hz1 h604
                        · -- right
                          exact CKLaneC2R.Cells.S00.B057.c1154_pos (not_le.mp h594).le h481 (not_le.mp h604).le h603
                      · -- right
                        by_cases h605 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1160_pos (not_le.mp h594).le h481 (not_le.mp h603).le h605
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1162_pos (not_le.mp h594).le h481 (not_le.mp h605).le h602
                    · -- right
                      by_cases h606 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h607 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1184_pos (not_le.mp h594).le h481 (not_le.mp h602).le h607
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1186_pos (not_le.mp h594).le h481 (not_le.mp h607).le h606
                      · -- right
                        by_cases h608 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1192_pos (not_le.mp h594).le h481 (not_le.mp h606).le h608
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1194_pos (not_le.mp h594).le h481 (not_le.mp h608).le h593
                · -- right
                  by_cases h609 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h610 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h611 : a ≤ ((107/640 : ℚ) : ℝ)
                      · -- left
                        by_cases h612 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1215_pos (not_le.mp h482).le h611 (not_le.mp h593).le h612
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1217_pos (not_le.mp h482).le h611 (not_le.mp h612).le h610
                      · -- right
                        by_cases h613 : z ≤ ((769/5120 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1216_pos (not_le.mp h611).le h481 (not_le.mp h593).le h613
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1218_pos (not_le.mp h611).le h481 (not_le.mp h613).le h610
                    · -- right
                      by_cases h614 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c684_pos (not_le.mp h482).le h481 (not_le.mp h610).le h614
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c685_pos (not_le.mp h482).le h481 (not_le.mp h614).le h609
                  · -- right
                    by_cases h615 : a ≤ ((107/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h616 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c690_pos (not_le.mp h482).le h615 (not_le.mp h609).le h616
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c692_pos (not_le.mp h482).le h615 (not_le.mp h616).le h592
                    · -- right
                      by_cases h617 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c691_pos (not_le.mp h615).le h481 (not_le.mp h609).le h617
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c693_pos (not_le.mp h615).le h481 (not_le.mp h617).le h592
              · -- right
                by_cases h618 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h619 : a ≤ ((107/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h620 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h621 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c777_pos (not_le.mp h482).le h619 (not_le.mp h592).le h621
                      · -- right
                        exact CKLaneC2R.Cells.S00.B038.c779_pos (not_le.mp h482).le h619 (not_le.mp h621).le h620
                    · -- right
                      by_cases h622 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c785_pos (not_le.mp h482).le h619 (not_le.mp h620).le h622
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c787_pos (not_le.mp h482).le h619 (not_le.mp h622).le h618
                  · -- right
                    by_cases h623 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h624 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B038.c778_pos (not_le.mp h619).le h481 (not_le.mp h592).le h624
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c780_pos (not_le.mp h619).le h481 (not_le.mp h624).le h623
                    · -- right
                      by_cases h625 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c786_pos (not_le.mp h619).le h481 (not_le.mp h623).le h625
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c788_pos (not_le.mp h619).le h481 (not_le.mp h625).le h618
                · -- right
                  by_cases h626 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h627 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h628 : a ≤ ((107/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c807_pos (not_le.mp h482).le h628 (not_le.mp h618).le h627
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c808_pos (not_le.mp h628).le h481 (not_le.mp h618).le h627
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c68_pos (not_le.mp h482).le h481 (not_le.mp h627).le h626
                  · -- right
                    by_cases h629 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c71_pos (not_le.mp h482).le h481 (not_le.mp h626).le h629
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c72_pos (not_le.mp h482).le h481 (not_le.mp h629).le h591
            · -- right
              by_cases h630 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h631 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h632 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h633 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B006.c137_pos (not_le.mp h482).le h481 (not_le.mp h591).le h633
                    · -- right
                      exact CKLaneC2R.Cells.S00.B006.c138_pos (not_le.mp h482).le h481 (not_le.mp h633).le h632
                  · -- right
                    by_cases h634 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c141_pos (not_le.mp h482).le h481 (not_le.mp h632).le h634
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c142_pos (not_le.mp h482).le h481 (not_le.mp h634).le h631
                · -- right
                  by_cases h635 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h636 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c153_pos (not_le.mp h482).le h481 (not_le.mp h631).le h636
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c154_pos (not_le.mp h482).le h481 (not_le.mp h636).le h635
                  · -- right
                    by_cases h637 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c157_pos (not_le.mp h482).le h481 (not_le.mp h635).le h637
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c158_pos (not_le.mp h482).le h481 (not_le.mp h637).le h630
              · -- right
                by_cases h638 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h639 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h640 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c169_pos (not_le.mp h482).le h481 (not_le.mp h630).le h640
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c170_pos (not_le.mp h482).le h481 (not_le.mp h640).le h639
                  · -- right
                    by_cases h641 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c173_pos (not_le.mp h482).le h481 (not_le.mp h639).le h641
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c174_pos (not_le.mp h482).le h481 (not_le.mp h641).le h638
                · -- right
                  by_cases h642 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h643 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c185_pos (not_le.mp h482).le h481 (not_le.mp h638).le h643
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c186_pos (not_le.mp h482).le h481 (not_le.mp h643).le h642
                  · -- right
                    by_cases h644 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c189_pos (not_le.mp h482).le h481 (not_le.mp h642).le h644
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c190_pos (not_le.mp h482).le h481 (not_le.mp h644).le h590
          · -- right
            by_cases h645 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h646 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h647 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h648 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h649 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B018.c379_pos (not_le.mp h482).le h481 (not_le.mp h590).le h649
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c380_pos (not_le.mp h482).le h481 (not_le.mp h649).le h648
                  · -- right
                    by_cases h650 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c383_pos (not_le.mp h482).le h481 (not_le.mp h648).le h650
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c384_pos (not_le.mp h482).le h481 (not_le.mp h650).le h647
                · -- right
                  by_cases h651 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h652 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c395_pos (not_le.mp h482).le h481 (not_le.mp h647).le h652
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c396_pos (not_le.mp h482).le h481 (not_le.mp h652).le h651
                  · -- right
                    by_cases h653 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c399_pos (not_le.mp h482).le h481 (not_le.mp h651).le h653
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c400_pos (not_le.mp h482).le h481 (not_le.mp h653).le h646
              · -- right
                by_cases h654 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h655 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h656 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c443_pos (not_le.mp h482).le h481 (not_le.mp h646).le h656
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c444_pos (not_le.mp h482).le h481 (not_le.mp h656).le h655
                  · -- right
                    by_cases h657 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c447_pos (not_le.mp h482).le h481 (not_le.mp h655).le h657
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c448_pos (not_le.mp h482).le h481 (not_le.mp h657).le h654
                · -- right
                  by_cases h658 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h659 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c459_pos (not_le.mp h482).le h481 (not_le.mp h654).le h659
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c460_pos (not_le.mp h482).le h481 (not_le.mp h659).le h658
                  · -- right
                    by_cases h660 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c463_pos (not_le.mp h482).le h481 (not_le.mp h658).le h660
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c464_pos (not_le.mp h482).le h481 (not_le.mp h660).le h645
            · -- right
              by_cases h661 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h662 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h663 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h664 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c535_pos (not_le.mp h482).le h481 (not_le.mp h645).le h664
                    · -- right
                      exact CKLaneC2R.Cells.S00.B026.c536_pos (not_le.mp h482).le h481 (not_le.mp h664).le h663
                  · -- right
                    by_cases h665 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B026.c539_pos (not_le.mp h482).le h481 (not_le.mp h663).le h665
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c540_pos (not_le.mp h482).le h481 (not_le.mp h665).le h662
                · -- right
                  by_cases h666 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h667 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c563_pos (not_le.mp h482).le h481 (not_le.mp h662).le h667
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c564_pos (not_le.mp h482).le h481 (not_le.mp h667).le h666
                  · -- right
                    by_cases h668 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c570_pos (not_le.mp h482).le h481 (not_le.mp h666).le h668
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c572_pos (not_le.mp h482).le h481 (not_le.mp h668).le h661
              · -- right
                by_cases h669 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h670 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h671 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c640_pos (not_le.mp h482).le h481 (not_le.mp h661).le h671
                    · -- right
                      by_cases h672 : z ≤ ((116003/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c963_pos (not_le.mp h482).le h481 (not_le.mp h671).le h672
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c964_pos (not_le.mp h482).le h481 (not_le.mp h672).le h670
                  · -- right
                    by_cases h673 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h674 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c967_pos (not_le.mp h482).le h481 (not_le.mp h670).le h674
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c968_pos (not_le.mp h482).le h481 (not_le.mp h674).le h673
                    · -- right
                      by_cases h675 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c971_pos (not_le.mp h482).le h481 (not_le.mp h673).le h675
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c972_pos (not_le.mp h482).le h481 (not_le.mp h675).le h669
                · -- right
                  by_cases h676 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h677 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h678 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1007_pos (not_le.mp h482).le h481 (not_le.mp h669).le h678
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1009_pos (not_le.mp h482).le h481 (not_le.mp h678).le h677
                    · -- right
                      by_cases h679 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1015_pos (not_le.mp h482).le h481 (not_le.mp h677).le h679
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1017_pos (not_le.mp h482).le h481 (not_le.mp h679).le h676
                  · -- right
                    by_cases h680 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h681 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h682 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1317_pos (not_le.mp h482).le h481 (not_le.mp h676).le h682
                        · -- right
                          exact CKLaneC2R.Cells.S00.B065.c1318_pos (not_le.mp h482).le h481 (not_le.mp h682).le h681
                      · -- right
                        by_cases h683 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1324_pos (not_le.mp h482).le h481 (not_le.mp h681).le h683
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1326_pos (not_le.mp h482).le h481 (not_le.mp h683).le h680
                    · -- right
                      by_cases h684 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h685 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1347_pos (not_le.mp h482).le h481 (not_le.mp h680).le h685
                        · -- right
                          by_cases h686 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1416_pos (not_le.mp h482).le h481 (not_le.mp h685).le h686
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1417_pos (not_le.mp h482).le h481 (not_le.mp h686).le h684
                      · -- right
                        by_cases h687 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h688 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1429_pos (not_le.mp h482).le h481 (not_le.mp h684).le h688
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1431_pos (not_le.mp h482).le h481 (not_le.mp h688).le h687
                        · -- right
                          by_cases h689 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h690 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1466_pos (not_le.mp h482).le h481 (not_le.mp h687).le h690
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1467_pos (not_le.mp h482).le h481 (not_le.mp h690).le h689
                          · -- right
                            by_cases h691 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1477_pos (not_le.mp h482).le h481 (not_le.mp h689).le h691
                            · -- right
                              by_cases h692 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B075.c1500_pos (not_le.mp h482).le h481 (not_le.mp h691).le h692
                              · -- right
                                exact CKLaneC2R.Cells.S00.B075.c1501_pos (not_le.mp h482).le h481 (not_le.mp h692).le hz2
      · -- right
        by_cases h693 : a ≤ ((11/64 : ℚ) : ℝ)
        · -- left
          by_cases h694 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h695 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h696 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h697 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h698 : a ≤ ((109/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h699 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h700 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h701 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1163_pos (not_le.mp h481).le h698 hz1 h701
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1165_pos (not_le.mp h481).le h698 (not_le.mp h701).le h700
                      · -- right
                        by_cases h702 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1171_pos (not_le.mp h481).le h698 (not_le.mp h700).le h702
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1173_pos (not_le.mp h481).le h698 (not_le.mp h702).le h699
                    · -- right
                      by_cases h703 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h704 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1195_pos (not_le.mp h481).le h698 (not_le.mp h699).le h704
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1197_pos (not_le.mp h481).le h698 (not_le.mp h704).le h703
                      · -- right
                        by_cases h705 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1203_pos (not_le.mp h481).le h698 (not_le.mp h703).le h705
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1205_pos (not_le.mp h481).le h698 (not_le.mp h705).le h697
                  · -- right
                    by_cases h706 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h707 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h708 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1164_pos (not_le.mp h698).le h693 hz1 h708
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1166_pos (not_le.mp h698).le h693 (not_le.mp h708).le h707
                      · -- right
                        by_cases h709 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1172_pos (not_le.mp h698).le h693 (not_le.mp h707).le h709
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1174_pos (not_le.mp h698).le h693 (not_le.mp h709).le h706
                    · -- right
                      by_cases h710 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h711 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1196_pos (not_le.mp h698).le h693 (not_le.mp h706).le h711
                        · -- right
                          exact CKLaneC2R.Cells.S00.B059.c1198_pos (not_le.mp h698).le h693 (not_le.mp h711).le h710
                      · -- right
                        by_cases h712 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1204_pos (not_le.mp h698).le h693 (not_le.mp h710).le h712
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1206_pos (not_le.mp h698).le h693 (not_le.mp h712).le h697
                · -- right
                  by_cases h713 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h714 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h715 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        by_cases h716 : a ≤ ((109/640 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1223_pos (not_le.mp h481).le h716 (not_le.mp h697).le h715
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1224_pos (not_le.mp h716).le h693 (not_le.mp h697).le h715
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c694_pos (not_le.mp h481).le h693 (not_le.mp h715).le h714
                    · -- right
                      by_cases h717 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c697_pos (not_le.mp h481).le h693 (not_le.mp h714).le h717
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c698_pos (not_le.mp h481).le h693 (not_le.mp h717).le h713
                  · -- right
                    by_cases h718 : a ≤ ((109/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h719 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c701_pos (not_le.mp h481).le h718 (not_le.mp h713).le h719
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c703_pos (not_le.mp h481).le h718 (not_le.mp h719).le h696
                    · -- right
                      by_cases h720 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c702_pos (not_le.mp h718).le h693 (not_le.mp h713).le h720
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c704_pos (not_le.mp h718).le h693 (not_le.mp h720).le h696
              · -- right
                by_cases h721 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h722 : a ≤ ((109/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h723 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h724 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c789_pos (not_le.mp h481).le h722 (not_le.mp h696).le h724
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c791_pos (not_le.mp h481).le h722 (not_le.mp h724).le h723
                    · -- right
                      by_cases h725 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c797_pos (not_le.mp h481).le h722 (not_le.mp h723).le h725
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c799_pos (not_le.mp h481).le h722 (not_le.mp h725).le h721
                  · -- right
                    by_cases h726 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h727 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c790_pos (not_le.mp h722).le h693 (not_le.mp h696).le h727
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c792_pos (not_le.mp h722).le h693 (not_le.mp h727).le h726
                    · -- right
                      by_cases h728 : z ≤ ((15547/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c798_pos (not_le.mp h722).le h693 (not_le.mp h726).le h728
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c800_pos (not_le.mp h722).le h693 (not_le.mp h728).le h721
                · -- right
                  by_cases h729 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h730 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c73_pos (not_le.mp h481).le h693 (not_le.mp h721).le h730
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c74_pos (not_le.mp h481).le h693 (not_le.mp h730).le h729
                  · -- right
                    by_cases h731 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c77_pos (not_le.mp h481).le h693 (not_le.mp h729).le h731
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c78_pos (not_le.mp h481).le h693 (not_le.mp h731).le h695
            · -- right
              by_cases h732 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h733 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h734 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h735 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c143_pos (not_le.mp h481).le h693 (not_le.mp h695).le h735
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c144_pos (not_le.mp h481).le h693 (not_le.mp h735).le h734
                  · -- right
                    by_cases h736 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c147_pos (not_le.mp h481).le h693 (not_le.mp h734).le h736
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c148_pos (not_le.mp h481).le h693 (not_le.mp h736).le h733
                · -- right
                  by_cases h737 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h738 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c159_pos (not_le.mp h481).le h693 (not_le.mp h733).le h738
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c160_pos (not_le.mp h481).le h693 (not_le.mp h738).le h737
                  · -- right
                    by_cases h739 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c163_pos (not_le.mp h481).le h693 (not_le.mp h737).le h739
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c164_pos (not_le.mp h481).le h693 (not_le.mp h739).le h732
              · -- right
                by_cases h740 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h741 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h742 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c175_pos (not_le.mp h481).le h693 (not_le.mp h732).le h742
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c176_pos (not_le.mp h481).le h693 (not_le.mp h742).le h741
                  · -- right
                    by_cases h743 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c179_pos (not_le.mp h481).le h693 (not_le.mp h741).le h743
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c180_pos (not_le.mp h481).le h693 (not_le.mp h743).le h740
                · -- right
                  by_cases h744 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h745 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c191_pos (not_le.mp h481).le h693 (not_le.mp h740).le h745
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c192_pos (not_le.mp h481).le h693 (not_le.mp h745).le h744
                  · -- right
                    by_cases h746 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c195_pos (not_le.mp h481).le h693 (not_le.mp h744).le h746
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c196_pos (not_le.mp h481).le h693 (not_le.mp h746).le h694
          · -- right
            by_cases h747 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h748 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h749 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h750 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h751 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c385_pos (not_le.mp h481).le h693 (not_le.mp h694).le h751
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c386_pos (not_le.mp h481).le h693 (not_le.mp h751).le h750
                  · -- right
                    by_cases h752 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c389_pos (not_le.mp h481).le h693 (not_le.mp h750).le h752
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c390_pos (not_le.mp h481).le h693 (not_le.mp h752).le h749
                · -- right
                  by_cases h753 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h754 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c401_pos (not_le.mp h481).le h693 (not_le.mp h749).le h754
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c402_pos (not_le.mp h481).le h693 (not_le.mp h754).le h753
                  · -- right
                    by_cases h755 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c405_pos (not_le.mp h481).le h693 (not_le.mp h753).le h755
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c406_pos (not_le.mp h481).le h693 (not_le.mp h755).le h748
              · -- right
                by_cases h756 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h757 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h758 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c449_pos (not_le.mp h481).le h693 (not_le.mp h748).le h758
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c450_pos (not_le.mp h481).le h693 (not_le.mp h758).le h757
                  · -- right
                    by_cases h759 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c453_pos (not_le.mp h481).le h693 (not_le.mp h757).le h759
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c454_pos (not_le.mp h481).le h693 (not_le.mp h759).le h756
                · -- right
                  by_cases h760 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h761 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c465_pos (not_le.mp h481).le h693 (not_le.mp h756).le h761
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c466_pos (not_le.mp h481).le h693 (not_le.mp h761).le h760
                  · -- right
                    by_cases h762 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c469_pos (not_le.mp h481).le h693 (not_le.mp h760).le h762
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c470_pos (not_le.mp h481).le h693 (not_le.mp h762).le h747
            · -- right
              by_cases h763 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h764 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h765 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h766 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c541_pos (not_le.mp h481).le h693 (not_le.mp h747).le h766
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c542_pos (not_le.mp h481).le h693 (not_le.mp h766).le h765
                  · -- right
                    by_cases h767 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c545_pos (not_le.mp h481).le h693 (not_le.mp h765).le h767
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c546_pos (not_le.mp h481).le h693 (not_le.mp h767).le h764
                · -- right
                  by_cases h768 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h769 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c565_pos (not_le.mp h481).le h693 (not_le.mp h764).le h769
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c567_pos (not_le.mp h481).le h693 (not_le.mp h769).le h768
                  · -- right
                    by_cases h770 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c573_pos (not_le.mp h481).le h693 (not_le.mp h768).le h770
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c575_pos (not_le.mp h481).le h693 (not_le.mp h770).le h763
              · -- right
                by_cases h771 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h772 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h773 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c641_pos (not_le.mp h481).le h693 (not_le.mp h763).le h773
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c643_pos (not_le.mp h481).le h693 (not_le.mp h773).le h772
                  · -- right
                    by_cases h774 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h775 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c973_pos (not_le.mp h481).le h693 (not_le.mp h772).le h775
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c974_pos (not_le.mp h481).le h693 (not_le.mp h775).le h774
                    · -- right
                      by_cases h776 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c977_pos (not_le.mp h481).le h693 (not_le.mp h774).le h776
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c978_pos (not_le.mp h481).le h693 (not_le.mp h776).le h771
                · -- right
                  by_cases h777 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h778 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h779 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1010_pos (not_le.mp h481).le h693 (not_le.mp h771).le h779
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1012_pos (not_le.mp h481).le h693 (not_le.mp h779).le h778
                    · -- right
                      by_cases h780 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1018_pos (not_le.mp h481).le h693 (not_le.mp h778).le h780
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1020_pos (not_le.mp h481).le h693 (not_le.mp h780).le h777
                  · -- right
                    by_cases h781 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h782 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h783 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B065.c1319_pos (not_le.mp h481).le h693 (not_le.mp h777).le h783
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1320_pos (not_le.mp h481).le h693 (not_le.mp h783).le h782
                      · -- right
                        by_cases h784 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1327_pos (not_le.mp h481).le h693 (not_le.mp h782).le h784
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1329_pos (not_le.mp h481).le h693 (not_le.mp h784).le h781
                    · -- right
                      by_cases h785 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h786 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1348_pos (not_le.mp h481).le h693 (not_le.mp h781).le h786
                        · -- right
                          by_cases h787 : z ≤ ((506923/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B070.c1418_pos (not_le.mp h481).le h693 (not_le.mp h786).le h787
                          · -- right
                            exact CKLaneC2R.Cells.S00.B070.c1419_pos (not_le.mp h481).le h693 (not_le.mp h787).le h785
                      · -- right
                        by_cases h788 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h789 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1432_pos (not_le.mp h481).le h693 (not_le.mp h785).le h789
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1434_pos (not_le.mp h481).le h693 (not_le.mp h789).le h788
                        · -- right
                          by_cases h790 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h791 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1468_pos (not_le.mp h481).le h693 (not_le.mp h788).le h791
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1469_pos (not_le.mp h481).le h693 (not_le.mp h791).le h790
                          · -- right
                            by_cases h792 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1478_pos (not_le.mp h481).le h693 (not_le.mp h790).le h792
                            · -- right
                              by_cases h793 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B075.c1502_pos (not_le.mp h481).le h693 (not_le.mp h792).le h793
                              · -- right
                                exact CKLaneC2R.Cells.S00.B075.c1503_pos (not_le.mp h481).le h693 (not_le.mp h793).le hz2
        · -- right
          by_cases h794 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h795 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h796 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h797 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h798 : a ≤ ((111/640 : ℚ) : ℝ)
                  · -- left
                    by_cases h799 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h800 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h801 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1167_pos (not_le.mp h693).le h798 hz1 h801
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1169_pos (not_le.mp h693).le h798 (not_le.mp h801).le h800
                      · -- right
                        by_cases h802 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1175_pos (not_le.mp h693).le h798 (not_le.mp h800).le h802
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1177_pos (not_le.mp h693).le h798 (not_le.mp h802).le h799
                    · -- right
                      by_cases h803 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h804 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B059.c1199_pos (not_le.mp h693).le h798 (not_le.mp h799).le h804
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1201_pos (not_le.mp h693).le h798 (not_le.mp h804).le h803
                      · -- right
                        by_cases h805 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1207_pos (not_le.mp h693).le h798 (not_le.mp h803).le h805
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1209_pos (not_le.mp h693).le h798 (not_le.mp h805).le h797
                  · -- right
                    by_cases h806 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h807 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h808 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1168_pos (not_le.mp h798).le h0 hz1 h808
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1170_pos (not_le.mp h798).le h0 (not_le.mp h808).le h807
                      · -- right
                        by_cases h809 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B058.c1176_pos (not_le.mp h798).le h0 (not_le.mp h807).le h809
                        · -- right
                          exact CKLaneC2R.Cells.S00.B058.c1178_pos (not_le.mp h798).le h0 (not_le.mp h809).le h806
                    · -- right
                      by_cases h810 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h811 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1200_pos (not_le.mp h798).le h0 (not_le.mp h806).le h811
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1202_pos (not_le.mp h798).le h0 (not_le.mp h811).le h810
                      · -- right
                        by_cases h812 : z ≤ ((17399/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B060.c1208_pos (not_le.mp h798).le h0 (not_le.mp h810).le h812
                        · -- right
                          exact CKLaneC2R.Cells.S00.B060.c1210_pos (not_le.mp h798).le h0 (not_le.mp h812).le h797
                · -- right
                  by_cases h813 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h814 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h815 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c695_pos (not_le.mp h693).le h0 (not_le.mp h797).le h815
                      · -- right
                        exact CKLaneC2R.Cells.S00.B034.c696_pos (not_le.mp h693).le h0 (not_le.mp h815).le h814
                    · -- right
                      by_cases h816 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B034.c699_pos (not_le.mp h693).le h0 (not_le.mp h814).le h816
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c700_pos (not_le.mp h693).le h0 (not_le.mp h816).le h813
                  · -- right
                    by_cases h817 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h818 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c705_pos (not_le.mp h693).le h0 (not_le.mp h813).le h818
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c706_pos (not_le.mp h693).le h0 (not_le.mp h818).le h817
                    · -- right
                      by_cases h819 : a ≤ ((111/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B035.c707_pos (not_le.mp h693).le h819 (not_le.mp h817).le h796
                      · -- right
                        exact CKLaneC2R.Cells.S00.B035.c708_pos (not_le.mp h819).le h0 (not_le.mp h817).le h796
              · -- right
                by_cases h820 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h821 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h822 : a ≤ ((111/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h823 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c793_pos (not_le.mp h693).le h822 (not_le.mp h796).le h823
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c795_pos (not_le.mp h693).le h822 (not_le.mp h823).le h821
                    · -- right
                      by_cases h824 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B039.c794_pos (not_le.mp h822).le h0 (not_le.mp h796).le h824
                      · -- right
                        exact CKLaneC2R.Cells.S00.B039.c796_pos (not_le.mp h822).le h0 (not_le.mp h824).le h821
                  · -- right
                    by_cases h825 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h826 : a ≤ ((111/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B040.c801_pos (not_le.mp h693).le h826 (not_le.mp h821).le h825
                      · -- right
                        exact CKLaneC2R.Cells.S00.B040.c802_pos (not_le.mp h826).le h0 (not_le.mp h821).le h825
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c67_pos (not_le.mp h693).le h0 (not_le.mp h825).le h820
                · -- right
                  by_cases h827 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h828 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c75_pos (not_le.mp h693).le h0 (not_le.mp h820).le h828
                    · -- right
                      exact CKLaneC2R.Cells.S00.B003.c76_pos (not_le.mp h693).le h0 (not_le.mp h828).le h827
                  · -- right
                    by_cases h829 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B003.c79_pos (not_le.mp h693).le h0 (not_le.mp h827).le h829
                    · -- right
                      exact CKLaneC2R.Cells.S00.B004.c80_pos (not_le.mp h693).le h0 (not_le.mp h829).le h795
            · -- right
              by_cases h830 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h831 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h832 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h833 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c145_pos (not_le.mp h693).le h0 (not_le.mp h795).le h833
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c146_pos (not_le.mp h693).le h0 (not_le.mp h833).le h832
                  · -- right
                    by_cases h834 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B007.c149_pos (not_le.mp h693).le h0 (not_le.mp h832).le h834
                    · -- right
                      exact CKLaneC2R.Cells.S00.B007.c150_pos (not_le.mp h693).le h0 (not_le.mp h834).le h831
                · -- right
                  by_cases h835 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h836 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c161_pos (not_le.mp h693).le h0 (not_le.mp h831).le h836
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c162_pos (not_le.mp h693).le h0 (not_le.mp h836).le h835
                  · -- right
                    by_cases h837 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c165_pos (not_le.mp h693).le h0 (not_le.mp h835).le h837
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c166_pos (not_le.mp h693).le h0 (not_le.mp h837).le h830
              · -- right
                by_cases h838 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h839 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h840 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B008.c177_pos (not_le.mp h693).le h0 (not_le.mp h830).le h840
                    · -- right
                      exact CKLaneC2R.Cells.S00.B008.c178_pos (not_le.mp h693).le h0 (not_le.mp h840).le h839
                  · -- right
                    by_cases h841 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c181_pos (not_le.mp h693).le h0 (not_le.mp h839).le h841
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c182_pos (not_le.mp h693).le h0 (not_le.mp h841).le h838
                · -- right
                  by_cases h842 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h843 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c193_pos (not_le.mp h693).le h0 (not_le.mp h838).le h843
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c194_pos (not_le.mp h693).le h0 (not_le.mp h843).le h842
                  · -- right
                    by_cases h844 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B009.c197_pos (not_le.mp h693).le h0 (not_le.mp h842).le h844
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c198_pos (not_le.mp h693).le h0 (not_le.mp h844).le h794
          · -- right
            by_cases h845 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h846 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h847 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h848 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h849 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c387_pos (not_le.mp h693).le h0 (not_le.mp h794).le h849
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c388_pos (not_le.mp h693).le h0 (not_le.mp h849).le h848
                  · -- right
                    by_cases h850 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B019.c391_pos (not_le.mp h693).le h0 (not_le.mp h848).le h850
                    · -- right
                      exact CKLaneC2R.Cells.S00.B019.c392_pos (not_le.mp h693).le h0 (not_le.mp h850).le h847
                · -- right
                  by_cases h851 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h852 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c403_pos (not_le.mp h693).le h0 (not_le.mp h847).le h852
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c404_pos (not_le.mp h693).le h0 (not_le.mp h852).le h851
                  · -- right
                    by_cases h853 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B020.c407_pos (not_le.mp h693).le h0 (not_le.mp h851).le h853
                    · -- right
                      exact CKLaneC2R.Cells.S00.B020.c408_pos (not_le.mp h693).le h0 (not_le.mp h853).le h846
              · -- right
                by_cases h854 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h855 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h856 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c451_pos (not_le.mp h693).le h0 (not_le.mp h846).le h856
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c452_pos (not_le.mp h693).le h0 (not_le.mp h856).le h855
                  · -- right
                    by_cases h857 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B022.c455_pos (not_le.mp h693).le h0 (not_le.mp h855).le h857
                    · -- right
                      exact CKLaneC2R.Cells.S00.B022.c456_pos (not_le.mp h693).le h0 (not_le.mp h857).le h854
                · -- right
                  by_cases h858 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h859 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c467_pos (not_le.mp h693).le h0 (not_le.mp h854).le h859
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c468_pos (not_le.mp h693).le h0 (not_le.mp h859).le h858
                  · -- right
                    by_cases h860 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c471_pos (not_le.mp h693).le h0 (not_le.mp h858).le h860
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c472_pos (not_le.mp h693).le h0 (not_le.mp h860).le h845
            · -- right
              by_cases h861 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h862 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h863 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h864 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c543_pos (not_le.mp h693).le h0 (not_le.mp h845).le h864
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c544_pos (not_le.mp h693).le h0 (not_le.mp h864).le h863
                  · -- right
                    by_cases h865 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B027.c547_pos (not_le.mp h693).le h0 (not_le.mp h863).le h865
                    · -- right
                      exact CKLaneC2R.Cells.S00.B027.c548_pos (not_le.mp h693).le h0 (not_le.mp h865).le h862
                · -- right
                  by_cases h866 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h867 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c566_pos (not_le.mp h693).le h0 (not_le.mp h862).le h867
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c568_pos (not_le.mp h693).le h0 (not_le.mp h867).le h866
                  · -- right
                    by_cases h868 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c574_pos (not_le.mp h693).le h0 (not_le.mp h866).le h868
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c576_pos (not_le.mp h693).le h0 (not_le.mp h868).le h861
              · -- right
                by_cases h869 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h870 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h871 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c642_pos (not_le.mp h693).le h0 (not_le.mp h861).le h871
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c644_pos (not_le.mp h693).le h0 (not_le.mp h871).le h870
                  · -- right
                    by_cases h872 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h873 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c975_pos (not_le.mp h693).le h0 (not_le.mp h870).le h873
                      · -- right
                        exact CKLaneC2R.Cells.S00.B048.c976_pos (not_le.mp h693).le h0 (not_le.mp h873).le h872
                    · -- right
                      by_cases h874 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B048.c979_pos (not_le.mp h693).le h0 (not_le.mp h872).le h874
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c980_pos (not_le.mp h693).le h0 (not_le.mp h874).le h869
                · -- right
                  by_cases h875 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h876 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h877 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1011_pos (not_le.mp h693).le h0 (not_le.mp h869).le h877
                      · -- right
                        exact CKLaneC2R.Cells.S00.B050.c1013_pos (not_le.mp h693).le h0 (not_le.mp h877).le h876
                    · -- right
                      by_cases h878 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B050.c1019_pos (not_le.mp h693).le h0 (not_le.mp h876).le h878
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1021_pos (not_le.mp h693).le h0 (not_le.mp h878).le h875
                  · -- right
                    by_cases h879 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h880 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h881 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1321_pos (not_le.mp h693).le h0 (not_le.mp h875).le h881
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1322_pos (not_le.mp h693).le h0 (not_le.mp h881).le h880
                      · -- right
                        by_cases h882 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1328_pos (not_le.mp h693).le h0 (not_le.mp h880).le h882
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1330_pos (not_le.mp h693).le h0 (not_le.mp h882).le h879
                    · -- right
                      by_cases h883 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h884 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1349_pos (not_le.mp h693).le h0 (not_le.mp h879).le h884
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1350_pos (not_le.mp h693).le h0 (not_le.mp h884).le h883
                      · -- right
                        by_cases h885 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h886 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1433_pos (not_le.mp h693).le h0 (not_le.mp h883).le h886
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1435_pos (not_le.mp h693).le h0 (not_le.mp h886).le h885
                        · -- right
                          by_cases h887 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            by_cases h888 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1470_pos (not_le.mp h693).le h0 (not_le.mp h885).le h888
                            · -- right
                              exact CKLaneC2R.Cells.S00.B073.c1471_pos (not_le.mp h693).le h0 (not_le.mp h888).le h887
                          · -- right
                            by_cases h889 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B073.c1479_pos (not_le.mp h693).le h0 (not_le.mp h887).le h889
                            · -- right
                              by_cases h890 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B075.c1504_pos (not_le.mp h693).le h0 (not_le.mp h889).le h890
                              · -- right
                                exact CKLaneC2R.Cells.S00.B075.c1505_pos (not_le.mp h693).le h0 (not_le.mp h890).le hz2
  · -- right
    by_cases h891 : a ≤ ((3/16 : ℚ) : ℝ)
    · -- left
      by_cases h892 : a ≤ ((29/160 : ℚ) : ℝ)
      · -- left
        by_cases h893 : a ≤ ((57/320 : ℚ) : ℝ)
        · -- left
          by_cases h894 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h895 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h896 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h897 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h898 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h899 : a ≤ ((113/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h900 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h901 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1225_pos (not_le.mp h0).le h899 hz1 h901
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1227_pos (not_le.mp h0).le h899 (not_le.mp h901).le h900
                      · -- right
                        by_cases h902 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1233_pos (not_le.mp h0).le h899 (not_le.mp h900).le h902
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1235_pos (not_le.mp h0).le h899 (not_le.mp h902).le h898
                    · -- right
                      by_cases h903 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h904 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1226_pos (not_le.mp h899).le h893 hz1 h904
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1228_pos (not_le.mp h899).le h893 (not_le.mp h904).le h903
                      · -- right
                        by_cases h905 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1234_pos (not_le.mp h899).le h893 (not_le.mp h903).le h905
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1236_pos (not_le.mp h899).le h893 (not_le.mp h905).le h898
                  · -- right
                    by_cases h906 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h907 : a ≤ ((113/640 : ℚ) : ℝ)
                      · -- left
                        by_cases h908 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1257_pos (not_le.mp h0).le h907 (not_le.mp h898).le h908
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1259_pos (not_le.mp h0).le h907 (not_le.mp h908).le h906
                      · -- right
                        by_cases h909 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1258_pos (not_le.mp h907).le h893 (not_le.mp h898).le h909
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1260_pos (not_le.mp h907).le h893 (not_le.mp h909).le h906
                    · -- right
                      by_cases h910 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h911 : a ≤ ((113/640 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1265_pos (not_le.mp h0).le h911 (not_le.mp h906).le h910
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1266_pos (not_le.mp h911).le h893 (not_le.mp h906).le h910
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c829_pos (not_le.mp h0).le h893 (not_le.mp h910).le h897
                · -- right
                  by_cases h912 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h913 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h914 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c861_pos (not_le.mp h0).le h893 (not_le.mp h897).le h914
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c862_pos (not_le.mp h0).le h893 (not_le.mp h914).le h913
                    · -- right
                      by_cases h915 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c865_pos (not_le.mp h0).le h893 (not_le.mp h913).le h915
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c866_pos (not_le.mp h0).le h893 (not_le.mp h915).le h912
                  · -- right
                    by_cases h916 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h917 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c877_pos (not_le.mp h0).le h893 (not_le.mp h912).le h917
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c878_pos (not_le.mp h0).le h893 (not_le.mp h917).le h916
                    · -- right
                      by_cases h918 : a ≤ ((113/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c879_pos (not_le.mp h0).le h918 (not_le.mp h916).le h896
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c880_pos (not_le.mp h918).le h893 (not_le.mp h916).le h896
              · -- right
                by_cases h919 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h920 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h921 : a ≤ ((113/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h922 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c913_pos (not_le.mp h0).le h921 (not_le.mp h896).le h922
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c915_pos (not_le.mp h0).le h921 (not_le.mp h922).le h920
                    · -- right
                      by_cases h923 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c914_pos (not_le.mp h921).le h893 (not_le.mp h896).le h923
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c916_pos (not_le.mp h921).le h893 (not_le.mp h923).le h920
                  · -- right
                    by_cases h924 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c206_pos (not_le.mp h0).le h893 (not_le.mp h920).le h924
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c207_pos (not_le.mp h0).le h893 (not_le.mp h924).le h919
                · -- right
                  by_cases h925 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h926 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c217_pos (not_le.mp h0).le h893 (not_le.mp h919).le h926
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c218_pos (not_le.mp h0).le h893 (not_le.mp h926).le h925
                  · -- right
                    by_cases h927 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c221_pos (not_le.mp h0).le h893 (not_le.mp h925).le h927
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c222_pos (not_le.mp h0).le h893 (not_le.mp h927).le h895
            · -- right
              by_cases h928 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h929 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h930 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h931 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c265_pos (not_le.mp h0).le h893 (not_le.mp h895).le h931
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c266_pos (not_le.mp h0).le h893 (not_le.mp h931).le h930
                  · -- right
                    by_cases h932 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c269_pos (not_le.mp h0).le h893 (not_le.mp h930).le h932
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c270_pos (not_le.mp h0).le h893 (not_le.mp h932).le h929
                · -- right
                  by_cases h933 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h934 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c281_pos (not_le.mp h0).le h893 (not_le.mp h929).le h934
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c282_pos (not_le.mp h0).le h893 (not_le.mp h934).le h933
                  · -- right
                    by_cases h935 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c285_pos (not_le.mp h0).le h893 (not_le.mp h933).le h935
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c286_pos (not_le.mp h0).le h893 (not_le.mp h935).le h928
              · -- right
                by_cases h936 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h937 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h938 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c321_pos (not_le.mp h0).le h893 (not_le.mp h928).le h938
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c322_pos (not_le.mp h0).le h893 (not_le.mp h938).le h937
                  · -- right
                    by_cases h939 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c325_pos (not_le.mp h0).le h893 (not_le.mp h937).le h939
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c326_pos (not_le.mp h0).le h893 (not_le.mp h939).le h936
                · -- right
                  by_cases h940 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h941 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c335_pos (not_le.mp h0).le h893 (not_le.mp h936).le h941
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c336_pos (not_le.mp h0).le h893 (not_le.mp h941).le h940
                  · -- right
                    by_cases h942 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c339_pos (not_le.mp h0).le h893 (not_le.mp h940).le h942
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c340_pos (not_le.mp h0).le h893 (not_le.mp h942).le h894
          · -- right
            by_cases h943 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h944 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h945 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h946 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h947 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c473_pos (not_le.mp h0).le h893 (not_le.mp h894).le h947
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c474_pos (not_le.mp h0).le h893 (not_le.mp h947).le h946
                  · -- right
                    by_cases h948 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c477_pos (not_le.mp h0).le h893 (not_le.mp h946).le h948
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c478_pos (not_le.mp h0).le h893 (not_le.mp h948).le h945
                · -- right
                  by_cases h949 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h950 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c481_pos (not_le.mp h0).le h893 (not_le.mp h945).le h950
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c482_pos (not_le.mp h0).le h893 (not_le.mp h950).le h949
                  · -- right
                    by_cases h951 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c485_pos (not_le.mp h0).le h893 (not_le.mp h949).le h951
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c486_pos (not_le.mp h0).le h893 (not_le.mp h951).le h944
              · -- right
                by_cases h952 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h953 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h954 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c489_pos (not_le.mp h0).le h893 (not_le.mp h944).le h954
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c490_pos (not_le.mp h0).le h893 (not_le.mp h954).le h953
                  · -- right
                    by_cases h955 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c493_pos (not_le.mp h0).le h893 (not_le.mp h953).le h955
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c494_pos (not_le.mp h0).le h893 (not_le.mp h955).le h952
                · -- right
                  by_cases h956 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h957 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c499_pos (not_le.mp h0).le h893 (not_le.mp h952).le h957
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c500_pos (not_le.mp h0).le h893 (not_le.mp h957).le h956
                  · -- right
                    by_cases h958 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c503_pos (not_le.mp h0).le h893 (not_le.mp h956).le h958
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c504_pos (not_le.mp h0).le h893 (not_le.mp h958).le h943
            · -- right
              by_cases h959 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h960 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h961 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h962 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c577_pos (not_le.mp h0).le h893 (not_le.mp h943).le h962
                    · -- right
                      exact CKLaneC2R.Cells.S00.B028.c578_pos (not_le.mp h0).le h893 (not_le.mp h962).le h961
                  · -- right
                    by_cases h963 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c581_pos (not_le.mp h0).le h893 (not_le.mp h961).le h963
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c582_pos (not_le.mp h0).le h893 (not_le.mp h963).le h960
                · -- right
                  by_cases h964 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h965 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c607_pos (not_le.mp h0).le h893 (not_le.mp h960).le h965
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c609_pos (not_le.mp h0).le h893 (not_le.mp h965).le h964
                  · -- right
                    by_cases h966 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c615_pos (not_le.mp h0).le h893 (not_le.mp h964).le h966
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c617_pos (not_le.mp h0).le h893 (not_le.mp h966).le h959
              · -- right
                by_cases h967 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h968 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h969 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c645_pos (not_le.mp h0).le h893 (not_le.mp h959).le h969
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c647_pos (not_le.mp h0).le h893 (not_le.mp h969).le h968
                  · -- right
                    by_cases h970 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h971 : z ≤ ((117829/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c981_pos (not_le.mp h0).le h893 (not_le.mp h968).le h971
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c982_pos (not_le.mp h0).le h893 (not_le.mp h971).le h970
                    · -- right
                      by_cases h972 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c983_pos (not_le.mp h0).le h893 (not_le.mp h970).le h972
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c984_pos (not_le.mp h0).le h893 (not_le.mp h972).le h967
                · -- right
                  by_cases h973 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h974 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h975 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1022_pos (not_le.mp h0).le h893 (not_le.mp h967).le h975
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1024_pos (not_le.mp h0).le h893 (not_le.mp h975).le h974
                    · -- right
                      by_cases h976 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1030_pos (not_le.mp h0).le h893 (not_le.mp h974).le h976
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1032_pos (not_le.mp h0).le h893 (not_le.mp h976).le h973
                  · -- right
                    by_cases h977 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h978 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h979 : z ≤ ((249353/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1331_pos (not_le.mp h0).le h893 (not_le.mp h973).le h979
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1332_pos (not_le.mp h0).le h893 (not_le.mp h979).le h978
                      · -- right
                        by_cases h980 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1333_pos (not_le.mp h0).le h893 (not_le.mp h978).le h980
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1335_pos (not_le.mp h0).le h893 (not_le.mp h980).le h977
                    · -- right
                      by_cases h981 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h982 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1351_pos (not_le.mp h0).le h893 (not_le.mp h977).le h982
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1353_pos (not_le.mp h0).le h893 (not_le.mp h982).le h981
                      · -- right
                        by_cases h983 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h984 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1436_pos (not_le.mp h0).le h893 (not_le.mp h981).le h984
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1438_pos (not_le.mp h0).le h893 (not_le.mp h984).le h983
                        · -- right
                          by_cases h985 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1446_pos (not_le.mp h0).le h893 (not_le.mp h983).le h985
                          · -- right
                            by_cases h986 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1480_pos (not_le.mp h0).le h893 (not_le.mp h985).le h986
                            · -- right
                              by_cases h987 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B075.c1506_pos (not_le.mp h0).le h893 (not_le.mp h986).le h987
                              · -- right
                                exact CKLaneC2R.Cells.S00.B075.c1508_pos (not_le.mp h0).le h893 (not_le.mp h987).le hz2
        · -- right
          by_cases h988 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h989 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h990 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h991 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h992 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h993 : a ≤ ((23/128 : ℚ) : ℝ)
                    · -- left
                      by_cases h994 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h995 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1229_pos (not_le.mp h893).le h993 hz1 h995
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1231_pos (not_le.mp h893).le h993 (not_le.mp h995).le h994
                      · -- right
                        by_cases h996 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1237_pos (not_le.mp h893).le h993 (not_le.mp h994).le h996
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1239_pos (not_le.mp h893).le h993 (not_le.mp h996).le h992
                    · -- right
                      by_cases h997 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h998 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1230_pos (not_le.mp h993).le h892 hz1 h998
                        · -- right
                          exact CKLaneC2R.Cells.S00.B061.c1232_pos (not_le.mp h993).le h892 (not_le.mp h998).le h997
                      · -- right
                        by_cases h999 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B061.c1238_pos (not_le.mp h993).le h892 (not_le.mp h997).le h999
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1240_pos (not_le.mp h993).le h892 (not_le.mp h999).le h992
                  · -- right
                    by_cases h1000 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1001 : a ≤ ((23/128 : ℚ) : ℝ)
                      · -- left
                        by_cases h1002 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1261_pos (not_le.mp h893).le h1001 (not_le.mp h992).le h1002
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1263_pos (not_le.mp h893).le h1001 (not_le.mp h1002).le h1000
                      · -- right
                        by_cases h1003 : z ≤ ((15573/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1262_pos (not_le.mp h1001).le h892 (not_le.mp h992).le h1003
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1264_pos (not_le.mp h1001).le h892 (not_le.mp h1003).le h1000
                    · -- right
                      by_cases h1004 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c830_pos (not_le.mp h893).le h892 (not_le.mp h1000).le h1004
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c831_pos (not_le.mp h893).le h892 (not_le.mp h1004).le h991
                · -- right
                  by_cases h1005 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1006 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1007 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c863_pos (not_le.mp h893).le h892 (not_le.mp h991).le h1007
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c864_pos (not_le.mp h893).le h892 (not_le.mp h1007).le h1006
                    · -- right
                      by_cases h1008 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c867_pos (not_le.mp h893).le h892 (not_le.mp h1006).le h1008
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c868_pos (not_le.mp h893).le h892 (not_le.mp h1008).le h1005
                  · -- right
                    by_cases h1009 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1010 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c881_pos (not_le.mp h893).le h892 (not_le.mp h1005).le h1010
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c882_pos (not_le.mp h893).le h892 (not_le.mp h1010).le h1009
                    · -- right
                      by_cases h1011 : a ≤ ((23/128 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c883_pos (not_le.mp h893).le h1011 (not_le.mp h1009).le h990
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c884_pos (not_le.mp h1011).le h892 (not_le.mp h1009).le h990
              · -- right
                by_cases h1012 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1013 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1014 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1015 : a ≤ ((23/128 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c917_pos (not_le.mp h893).le h1015 (not_le.mp h990).le h1014
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c918_pos (not_le.mp h1015).le h892 (not_le.mp h990).le h1014
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c205_pos (not_le.mp h893).le h892 (not_le.mp h1014).le h1013
                  · -- right
                    by_cases h1016 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c208_pos (not_le.mp h893).le h892 (not_le.mp h1013).le h1016
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c209_pos (not_le.mp h893).le h892 (not_le.mp h1016).le h1012
                · -- right
                  by_cases h1017 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1018 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c219_pos (not_le.mp h893).le h892 (not_le.mp h1012).le h1018
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c220_pos (not_le.mp h893).le h892 (not_le.mp h1018).le h1017
                  · -- right
                    by_cases h1019 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c223_pos (not_le.mp h893).le h892 (not_le.mp h1017).le h1019
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c224_pos (not_le.mp h893).le h892 (not_le.mp h1019).le h989
            · -- right
              by_cases h1020 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1021 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1022 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1023 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c267_pos (not_le.mp h893).le h892 (not_le.mp h989).le h1023
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c268_pos (not_le.mp h893).le h892 (not_le.mp h1023).le h1022
                  · -- right
                    by_cases h1024 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c271_pos (not_le.mp h893).le h892 (not_le.mp h1022).le h1024
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c272_pos (not_le.mp h893).le h892 (not_le.mp h1024).le h1021
                · -- right
                  by_cases h1025 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1026 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c283_pos (not_le.mp h893).le h892 (not_le.mp h1021).le h1026
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c284_pos (not_le.mp h893).le h892 (not_le.mp h1026).le h1025
                  · -- right
                    by_cases h1027 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c287_pos (not_le.mp h893).le h892 (not_le.mp h1025).le h1027
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c288_pos (not_le.mp h893).le h892 (not_le.mp h1027).le h1020
              · -- right
                by_cases h1028 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1029 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1030 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c323_pos (not_le.mp h893).le h892 (not_le.mp h1020).le h1030
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c324_pos (not_le.mp h893).le h892 (not_le.mp h1030).le h1029
                  · -- right
                    by_cases h1031 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c327_pos (not_le.mp h893).le h892 (not_le.mp h1029).le h1031
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c328_pos (not_le.mp h893).le h892 (not_le.mp h1031).le h1028
                · -- right
                  by_cases h1032 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1033 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c337_pos (not_le.mp h893).le h892 (not_le.mp h1028).le h1033
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c338_pos (not_le.mp h893).le h892 (not_le.mp h1033).le h1032
                  · -- right
                    by_cases h1034 : z ≤ ((33807/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c341_pos (not_le.mp h893).le h892 (not_le.mp h1032).le h1034
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c342_pos (not_le.mp h893).le h892 (not_le.mp h1034).le h988
          · -- right
            by_cases h1035 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1036 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1037 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1038 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1039 : z ≤ ((35633/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c475_pos (not_le.mp h893).le h892 (not_le.mp h988).le h1039
                    · -- right
                      exact CKLaneC2R.Cells.S00.B023.c476_pos (not_le.mp h893).le h892 (not_le.mp h1039).le h1038
                  · -- right
                    by_cases h1040 : z ≤ ((37459/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B023.c479_pos (not_le.mp h893).le h892 (not_le.mp h1038).le h1040
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c480_pos (not_le.mp h893).le h892 (not_le.mp h1040).le h1037
                · -- right
                  by_cases h1041 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1042 : z ≤ ((7857/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c483_pos (not_le.mp h893).le h892 (not_le.mp h1037).le h1042
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c484_pos (not_le.mp h893).le h892 (not_le.mp h1042).le h1041
                  · -- right
                    by_cases h1043 : z ≤ ((41111/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c487_pos (not_le.mp h893).le h892 (not_le.mp h1041).le h1043
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c488_pos (not_le.mp h893).le h892 (not_le.mp h1043).le h1036
              · -- right
                by_cases h1044 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1045 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    by_cases h1046 : z ≤ ((42937/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c491_pos (not_le.mp h893).le h892 (not_le.mp h1036).le h1046
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c492_pos (not_le.mp h893).le h892 (not_le.mp h1046).le h1045
                  · -- right
                    by_cases h1047 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c495_pos (not_le.mp h893).le h892 (not_le.mp h1045).le h1047
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c496_pos (not_le.mp h893).le h892 (not_le.mp h1047).le h1044
                · -- right
                  by_cases h1048 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1049 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c501_pos (not_le.mp h893).le h892 (not_le.mp h1044).le h1049
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c502_pos (not_le.mp h893).le h892 (not_le.mp h1049).le h1048
                  · -- right
                    by_cases h1050 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c505_pos (not_le.mp h893).le h892 (not_le.mp h1048).le h1050
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c506_pos (not_le.mp h893).le h892 (not_le.mp h1050).le h1035
            · -- right
              by_cases h1051 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1052 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1053 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1054 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B028.c579_pos (not_le.mp h893).le h892 (not_le.mp h1035).le h1054
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c580_pos (not_le.mp h893).le h892 (not_le.mp h1054).le h1053
                  · -- right
                    by_cases h1055 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c583_pos (not_le.mp h893).le h892 (not_le.mp h1053).le h1055
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c584_pos (not_le.mp h893).le h892 (not_le.mp h1055).le h1052
                · -- right
                  by_cases h1056 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1057 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c608_pos (not_le.mp h893).le h892 (not_le.mp h1052).le h1057
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c610_pos (not_le.mp h893).le h892 (not_le.mp h1057).le h1056
                  · -- right
                    by_cases h1058 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c616_pos (not_le.mp h893).le h892 (not_le.mp h1056).le h1058
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c618_pos (not_le.mp h893).le h892 (not_le.mp h1058).le h1051
              · -- right
                by_cases h1059 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1060 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1061 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c646_pos (not_le.mp h893).le h892 (not_le.mp h1051).le h1061
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c648_pos (not_le.mp h893).le h892 (not_le.mp h1061).le h1060
                  · -- right
                    by_cases h1062 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c653_pos (not_le.mp h893).le h892 (not_le.mp h1060).le h1062
                    · -- right
                      by_cases h1063 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c985_pos (not_le.mp h893).le h892 (not_le.mp h1062).le h1063
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c986_pos (not_le.mp h893).le h892 (not_le.mp h1063).le h1059
                · -- right
                  by_cases h1064 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1065 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1066 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1023_pos (not_le.mp h893).le h892 (not_le.mp h1059).le h1066
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1025_pos (not_le.mp h893).le h892 (not_le.mp h1066).le h1065
                    · -- right
                      by_cases h1067 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1031_pos (not_le.mp h893).le h892 (not_le.mp h1065).le h1067
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1033_pos (not_le.mp h893).le h892 (not_le.mp h1067).le h1064
                  · -- right
                    by_cases h1068 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1069 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1050_pos (not_le.mp h893).le h892 (not_le.mp h1064).le h1069
                      · -- right
                        by_cases h1070 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1334_pos (not_le.mp h893).le h892 (not_le.mp h1069).le h1070
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1336_pos (not_le.mp h893).le h892 (not_le.mp h1070).le h1068
                    · -- right
                      by_cases h1071 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1072 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1352_pos (not_le.mp h893).le h892 (not_le.mp h1068).le h1072
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1354_pos (not_le.mp h893).le h892 (not_le.mp h1072).le h1071
                      · -- right
                        by_cases h1073 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1074 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B071.c1437_pos (not_le.mp h893).le h892 (not_le.mp h1071).le h1074
                          · -- right
                            exact CKLaneC2R.Cells.S00.B071.c1439_pos (not_le.mp h893).le h892 (not_le.mp h1074).le h1073
                        · -- right
                          by_cases h1075 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1447_pos (not_le.mp h893).le h892 (not_le.mp h1073).le h1075
                          · -- right
                            by_cases h1076 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1481_pos (not_le.mp h893).le h892 (not_le.mp h1075).le h1076
                            · -- right
                              by_cases h1077 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.Cells.S00.B075.c1507_pos (not_le.mp h893).le h892 (not_le.mp h1076).le h1077
                              · -- right
                                exact CKLaneC2R.Cells.S00.B075.c1509_pos (not_le.mp h893).le h892 (not_le.mp h1077).le hz2
      · -- right
        by_cases h1078 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h1079 : a ≤ ((59/320 : ℚ) : ℝ)
          · -- left
            by_cases h1080 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1081 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1082 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1083 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1084 : a ≤ ((117/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h1085 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1086 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1241_pos (not_le.mp h892).le h1084 hz1 h1086
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1243_pos (not_le.mp h892).le h1084 (not_le.mp h1086).le h1085
                      · -- right
                        by_cases h1087 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1249_pos (not_le.mp h892).le h1084 (not_le.mp h1085).le h1087
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1251_pos (not_le.mp h892).le h1084 (not_le.mp h1087).le h1083
                    · -- right
                      by_cases h1088 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1089 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1242_pos (not_le.mp h1084).le h1079 hz1 h1089
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1244_pos (not_le.mp h1084).le h1079 (not_le.mp h1089).le h1088
                      · -- right
                        by_cases h1090 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1250_pos (not_le.mp h1084).le h1079 (not_le.mp h1088).le h1090
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1252_pos (not_le.mp h1084).le h1079 (not_le.mp h1090).le h1083
                  · -- right
                    by_cases h1091 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1092 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1093 : a ≤ ((117/640 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1267_pos (not_le.mp h892).le h1093 (not_le.mp h1083).le h1092
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1268_pos (not_le.mp h1093).le h1079 (not_le.mp h1083).le h1092
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c832_pos (not_le.mp h892).le h1079 (not_le.mp h1092).le h1091
                    · -- right
                      by_cases h1094 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c835_pos (not_le.mp h892).le h1079 (not_le.mp h1091).le h1094
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c836_pos (not_le.mp h892).le h1079 (not_le.mp h1094).le h1082
                · -- right
                  by_cases h1095 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1096 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1097 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c869_pos (not_le.mp h892).le h1079 (not_le.mp h1082).le h1097
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c870_pos (not_le.mp h892).le h1079 (not_le.mp h1097).le h1096
                    · -- right
                      by_cases h1098 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c873_pos (not_le.mp h892).le h1079 (not_le.mp h1096).le h1098
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c874_pos (not_le.mp h892).le h1079 (not_le.mp h1098).le h1095
                  · -- right
                    by_cases h1099 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1100 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c885_pos (not_le.mp h892).le h1079 (not_le.mp h1095).le h1100
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c886_pos (not_le.mp h892).le h1079 (not_le.mp h1100).le h1099
                    · -- right
                      by_cases h1101 : z ≤ ((24703/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c889_pos (not_le.mp h892).le h1079 (not_le.mp h1099).le h1101
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c890_pos (not_le.mp h892).le h1079 (not_le.mp h1101).le h1081
              · -- right
                by_cases h1102 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1103 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1104 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1105 : a ≤ ((117/640 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c919_pos (not_le.mp h892).le h1105 (not_le.mp h1081).le h1104
                      · -- right
                        exact CKLaneC2R.Cells.S00.B046.c920_pos (not_le.mp h1105).le h1079 (not_le.mp h1081).le h1104
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c210_pos (not_le.mp h892).le h1079 (not_le.mp h1104).le h1103
                  · -- right
                    by_cases h1106 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c213_pos (not_le.mp h892).le h1079 (not_le.mp h1103).le h1106
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c214_pos (not_le.mp h892).le h1079 (not_le.mp h1106).le h1102
                · -- right
                  by_cases h1107 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1108 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c225_pos (not_le.mp h892).le h1079 (not_le.mp h1102).le h1108
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c226_pos (not_le.mp h892).le h1079 (not_le.mp h1108).le h1107
                  · -- right
                    by_cases h1109 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c229_pos (not_le.mp h892).le h1079 (not_le.mp h1107).le h1109
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c230_pos (not_le.mp h892).le h1079 (not_le.mp h1109).le h1080
            · -- right
              by_cases h1110 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1111 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1112 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1113 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c273_pos (not_le.mp h892).le h1079 (not_le.mp h1080).le h1113
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c274_pos (not_le.mp h892).le h1079 (not_le.mp h1113).le h1112
                  · -- right
                    by_cases h1114 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c277_pos (not_le.mp h892).le h1079 (not_le.mp h1112).le h1114
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c278_pos (not_le.mp h892).le h1079 (not_le.mp h1114).le h1111
                · -- right
                  by_cases h1115 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1116 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c289_pos (not_le.mp h892).le h1079 (not_le.mp h1111).le h1116
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c290_pos (not_le.mp h892).le h1079 (not_le.mp h1116).le h1115
                  · -- right
                    by_cases h1117 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c293_pos (not_le.mp h892).le h1079 (not_le.mp h1115).le h1117
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c294_pos (not_le.mp h892).le h1079 (not_le.mp h1117).le h1110
              · -- right
                by_cases h1118 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1119 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1120 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c329_pos (not_le.mp h892).le h1079 (not_le.mp h1110).le h1120
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c330_pos (not_le.mp h892).le h1079 (not_le.mp h1120).le h1119
                  · -- right
                    by_cases h1121 : z ≤ ((6031/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c333_pos (not_le.mp h892).le h1079 (not_le.mp h1119).le h1121
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c334_pos (not_le.mp h892).le h1079 (not_le.mp h1121).le h1118
                · -- right
                  by_cases h1122 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1123 : z ≤ ((31981/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B017.c343_pos (not_le.mp h892).le h1079 (not_le.mp h1118).le h1123
                    · -- right
                      exact CKLaneC2R.Cells.S00.B017.c344_pos (not_le.mp h892).le h1079 (not_le.mp h1123).le h1122
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c6_pos (not_le.mp h892).le h1079 (not_le.mp h1122).le h1078
          · -- right
            by_cases h1124 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1125 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1126 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1127 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1128 : a ≤ ((119/640 : ℚ) : ℝ)
                    · -- left
                      by_cases h1129 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1130 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1245_pos (not_le.mp h1079).le h1128 hz1 h1130
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1247_pos (not_le.mp h1079).le h1128 (not_le.mp h1130).le h1129
                      · -- right
                        by_cases h1131 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1253_pos (not_le.mp h1079).le h1128 (not_le.mp h1129).le h1131
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1255_pos (not_le.mp h1079).le h1128 (not_le.mp h1131).le h1127
                    · -- right
                      by_cases h1132 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1133 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1246_pos (not_le.mp h1128).le h891 hz1 h1133
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1248_pos (not_le.mp h1128).le h891 (not_le.mp h1133).le h1132
                      · -- right
                        by_cases h1134 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B062.c1254_pos (not_le.mp h1128).le h891 (not_le.mp h1132).le h1134
                        · -- right
                          exact CKLaneC2R.Cells.S00.B062.c1256_pos (not_le.mp h1128).le h891 (not_le.mp h1134).le h1127
                  · -- right
                    by_cases h1135 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1136 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c833_pos (not_le.mp h1079).le h891 (not_le.mp h1127).le h1136
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c834_pos (not_le.mp h1079).le h891 (not_le.mp h1136).le h1135
                    · -- right
                      by_cases h1137 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B041.c837_pos (not_le.mp h1079).le h891 (not_le.mp h1135).le h1137
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c838_pos (not_le.mp h1079).le h891 (not_le.mp h1137).le h1126
                · -- right
                  by_cases h1138 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1139 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1140 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c871_pos (not_le.mp h1079).le h891 (not_le.mp h1126).le h1140
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c872_pos (not_le.mp h1079).le h891 (not_le.mp h1140).le h1139
                    · -- right
                      by_cases h1141 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B043.c875_pos (not_le.mp h1079).le h891 (not_le.mp h1139).le h1141
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c876_pos (not_le.mp h1079).le h891 (not_le.mp h1141).le h1138
                  · -- right
                    by_cases h1142 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1143 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c887_pos (not_le.mp h1079).le h891 (not_le.mp h1138).le h1143
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c888_pos (not_le.mp h1079).le h891 (not_le.mp h1143).le h1142
                    · -- right
                      by_cases h1144 : z ≤ ((24703/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c891_pos (not_le.mp h1079).le h891 (not_le.mp h1142).le h1144
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c892_pos (not_le.mp h1079).le h891 (not_le.mp h1144).le h1125
              · -- right
                by_cases h1145 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1146 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1147 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c211_pos (not_le.mp h1079).le h891 (not_le.mp h1125).le h1147
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c212_pos (not_le.mp h1079).le h891 (not_le.mp h1147).le h1146
                  · -- right
                    by_cases h1148 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c215_pos (not_le.mp h1079).le h891 (not_le.mp h1146).le h1148
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c216_pos (not_le.mp h1079).le h891 (not_le.mp h1148).le h1145
                · -- right
                  by_cases h1149 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1150 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c227_pos (not_le.mp h1079).le h891 (not_le.mp h1145).le h1150
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c228_pos (not_le.mp h1079).le h891 (not_le.mp h1150).le h1149
                  · -- right
                    by_cases h1151 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c231_pos (not_le.mp h1079).le h891 (not_le.mp h1149).le h1151
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c232_pos (not_le.mp h1079).le h891 (not_le.mp h1151).le h1124
            · -- right
              by_cases h1152 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1153 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1154 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1155 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c275_pos (not_le.mp h1079).le h891 (not_le.mp h1124).le h1155
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c276_pos (not_le.mp h1079).le h891 (not_le.mp h1155).le h1154
                  · -- right
                    by_cases h1156 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c279_pos (not_le.mp h1079).le h891 (not_le.mp h1154).le h1156
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c280_pos (not_le.mp h1079).le h891 (not_le.mp h1156).le h1153
                · -- right
                  by_cases h1157 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1158 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c291_pos (not_le.mp h1079).le h891 (not_le.mp h1153).le h1158
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c292_pos (not_le.mp h1079).le h891 (not_le.mp h1158).le h1157
                  · -- right
                    by_cases h1159 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c295_pos (not_le.mp h1079).le h891 (not_le.mp h1157).le h1159
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c296_pos (not_le.mp h1079).le h891 (not_le.mp h1159).le h1152
              · -- right
                by_cases h1160 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1161 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1162 : z ≤ ((28329/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B016.c331_pos (not_le.mp h1079).le h891 (not_le.mp h1152).le h1162
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c332_pos (not_le.mp h1079).le h891 (not_le.mp h1162).le h1161
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c4_pos (not_le.mp h1079).le h891 (not_le.mp h1161).le h1160
                · -- right
                  by_cases h1163 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c5_pos (not_le.mp h1079).le h891 (not_le.mp h1160).le h1163
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c7_pos (not_le.mp h1079).le h891 (not_le.mp h1163).le h1078
        · -- right
          by_cases h1164 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h1165 : a ≤ ((59/320 : ℚ) : ℝ)
            · -- left
              by_cases h1166 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1167 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1168 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c24_pos (not_le.mp h892).le h1165 (not_le.mp h1078).le h1168
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c26_pos (not_le.mp h892).le h1165 (not_le.mp h1168).le h1167
                · -- right
                  by_cases h1169 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c28_pos (not_le.mp h892).le h1165 (not_le.mp h1167).le h1169
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c30_pos (not_le.mp h892).le h1165 (not_le.mp h1169).le h1166
              · -- right
                by_cases h1170 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1171 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c48_pos (not_le.mp h892).le h1165 (not_le.mp h1166).le h1171
                  · -- right
                    by_cases h1172 : z ≤ ((44763/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B024.c497_pos (not_le.mp h892).le h1165 (not_le.mp h1171).le h1172
                    · -- right
                      exact CKLaneC2R.Cells.S00.B024.c498_pos (not_le.mp h892).le h1165 (not_le.mp h1172).le h1170
                · -- right
                  by_cases h1173 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1174 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c507_pos (not_le.mp h892).le h1165 (not_le.mp h1170).le h1174
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c508_pos (not_le.mp h892).le h1165 (not_le.mp h1174).le h1173
                  · -- right
                    by_cases h1175 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c511_pos (not_le.mp h892).le h1165 (not_le.mp h1173).le h1175
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c512_pos (not_le.mp h892).le h1165 (not_le.mp h1175).le h1164
            · -- right
              by_cases h1176 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1177 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1178 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c25_pos (not_le.mp h1165).le h891 (not_le.mp h1078).le h1178
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c27_pos (not_le.mp h1165).le h891 (not_le.mp h1178).le h1177
                · -- right
                  by_cases h1179 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c29_pos (not_le.mp h1165).le h891 (not_le.mp h1177).le h1179
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c31_pos (not_le.mp h1165).le h891 (not_le.mp h1179).le h1176
              · -- right
                by_cases h1180 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1181 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c49_pos (not_le.mp h1165).le h891 (not_le.mp h1176).le h1181
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c50_pos (not_le.mp h1165).le h891 (not_le.mp h1181).le h1180
                · -- right
                  by_cases h1182 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1183 : z ≤ ((46589/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c509_pos (not_le.mp h1165).le h891 (not_le.mp h1180).le h1183
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c510_pos (not_le.mp h1165).le h891 (not_le.mp h1183).le h1182
                  · -- right
                    by_cases h1184 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c513_pos (not_le.mp h1165).le h891 (not_le.mp h1182).le h1184
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c514_pos (not_le.mp h1165).le h891 (not_le.mp h1184).le h1164
          · -- right
            by_cases h1185 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h1186 : a ≤ ((59/320 : ℚ) : ℝ)
              · -- left
                by_cases h1187 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1188 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1189 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c585_pos (not_le.mp h892).le h1186 (not_le.mp h1164).le h1189
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c586_pos (not_le.mp h892).le h1186 (not_le.mp h1189).le h1188
                  · -- right
                    by_cases h1190 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c589_pos (not_le.mp h892).le h1186 (not_le.mp h1188).le h1190
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c590_pos (not_le.mp h892).le h1186 (not_le.mp h1190).le h1187
                · -- right
                  by_cases h1191 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1192 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c611_pos (not_le.mp h892).le h1186 (not_le.mp h1187).le h1192
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c613_pos (not_le.mp h892).le h1186 (not_le.mp h1192).le h1191
                  · -- right
                    by_cases h1193 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c619_pos (not_le.mp h892).le h1186 (not_le.mp h1191).le h1193
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c621_pos (not_le.mp h892).le h1186 (not_le.mp h1193).le h1185
              · -- right
                by_cases h1194 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1195 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1196 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c587_pos (not_le.mp h1186).le h891 (not_le.mp h1164).le h1196
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c588_pos (not_le.mp h1186).le h891 (not_le.mp h1196).le h1195
                  · -- right
                    by_cases h1197 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c591_pos (not_le.mp h1186).le h891 (not_le.mp h1195).le h1197
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c592_pos (not_le.mp h1186).le h891 (not_le.mp h1197).le h1194
                · -- right
                  by_cases h1198 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1199 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c612_pos (not_le.mp h1186).le h891 (not_le.mp h1194).le h1199
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c614_pos (not_le.mp h1186).le h891 (not_le.mp h1199).le h1198
                  · -- right
                    by_cases h1200 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c620_pos (not_le.mp h1186).le h891 (not_le.mp h1198).le h1200
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c622_pos (not_le.mp h1186).le h891 (not_le.mp h1200).le h1185
            · -- right
              by_cases h1201 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h1202 : a ≤ ((59/320 : ℚ) : ℝ)
                · -- left
                  by_cases h1203 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1204 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c649_pos (not_le.mp h892).le h1202 (not_le.mp h1185).le h1204
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c651_pos (not_le.mp h892).le h1202 (not_le.mp h1204).le h1203
                  · -- right
                    by_cases h1205 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c654_pos (not_le.mp h892).le h1202 (not_le.mp h1203).le h1205
                    · -- right
                      by_cases h1206 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c987_pos (not_le.mp h892).le h1202 (not_le.mp h1205).le h1206
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c988_pos (not_le.mp h892).le h1202 (not_le.mp h1206).le h1201
                · -- right
                  by_cases h1207 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1208 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c650_pos (not_le.mp h1202).le h891 (not_le.mp h1185).le h1208
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c652_pos (not_le.mp h1202).le h891 (not_le.mp h1208).le h1207
                  · -- right
                    by_cases h1209 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c655_pos (not_le.mp h1202).le h891 (not_le.mp h1207).le h1209
                    · -- right
                      by_cases h1210 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c989_pos (not_le.mp h1202).le h891 (not_le.mp h1209).le h1210
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c990_pos (not_le.mp h1202).le h891 (not_le.mp h1210).le h1201
              · -- right
                by_cases h1211 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h1212 : a ≤ ((59/320 : ℚ) : ℝ)
                  · -- left
                    by_cases h1213 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1214 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1026_pos (not_le.mp h892).le h1212 (not_le.mp h1201).le h1214
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1028_pos (not_le.mp h892).le h1212 (not_le.mp h1214).le h1213
                    · -- right
                      by_cases h1215 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1034_pos (not_le.mp h892).le h1212 (not_le.mp h1213).le h1215
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1036_pos (not_le.mp h892).le h1212 (not_le.mp h1215).le h1211
                  · -- right
                    by_cases h1216 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1217 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1027_pos (not_le.mp h1212).le h891 (not_le.mp h1201).le h1217
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1029_pos (not_le.mp h1212).le h891 (not_le.mp h1217).le h1216
                    · -- right
                      by_cases h1218 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1035_pos (not_le.mp h1212).le h891 (not_le.mp h1216).le h1218
                      · -- right
                        exact CKLaneC2R.Cells.S00.B051.c1037_pos (not_le.mp h1212).le h891 (not_le.mp h1218).le h1211
                · -- right
                  by_cases h1219 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1220 : a ≤ ((59/320 : ℚ) : ℝ)
                    · -- left
                      by_cases h1221 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1051_pos (not_le.mp h892).le h1220 (not_le.mp h1211).le h1221
                      · -- right
                        by_cases h1222 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1337_pos (not_le.mp h892).le h1220 (not_le.mp h1221).le h1222
                        · -- right
                          exact CKLaneC2R.Cells.S00.B066.c1339_pos (not_le.mp h892).le h1220 (not_le.mp h1222).le h1219
                    · -- right
                      by_cases h1223 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1052_pos (not_le.mp h1220).le h891 (not_le.mp h1211).le h1223
                      · -- right
                        by_cases h1224 : z ≤ ((251179/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B066.c1338_pos (not_le.mp h1220).le h891 (not_le.mp h1223).le h1224
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1340_pos (not_le.mp h1220).le h891 (not_le.mp h1224).le h1219
                  · -- right
                    by_cases h1225 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1226 : a ≤ ((59/320 : ℚ) : ℝ)
                      · -- left
                        by_cases h1227 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1355_pos (not_le.mp h892).le h1226 (not_le.mp h1219).le h1227
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1357_pos (not_le.mp h892).le h1226 (not_le.mp h1227).le h1225
                      · -- right
                        by_cases h1228 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1356_pos (not_le.mp h1226).le h891 (not_le.mp h1219).le h1228
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1358_pos (not_le.mp h1226).le h891 (not_le.mp h1228).le h1225
                    · -- right
                      by_cases h1229 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1230 : a ≤ ((59/320 : ℚ) : ℝ)
                        · -- left
                          by_cases h1231 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1440_pos (not_le.mp h892).le h1230 (not_le.mp h1225).le h1231
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1442_pos (not_le.mp h892).le h1230 (not_le.mp h1231).le h1229
                        · -- right
                          by_cases h1232 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1441_pos (not_le.mp h1230).le h891 (not_le.mp h1225).le h1232
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1443_pos (not_le.mp h1230).le h891 (not_le.mp h1232).le h1229
                      · -- right
                        by_cases h1233 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          by_cases h1234 : a ≤ ((59/320 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1448_pos (not_le.mp h892).le h1234 (not_le.mp h1229).le h1233
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1449_pos (not_le.mp h1234).le h891 (not_le.mp h1229).le h1233
                        · -- right
                          by_cases h1235 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1236 : a ≤ ((59/320 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1482_pos (not_le.mp h892).le h1236 (not_le.mp h1233).le h1235
                            · -- right
                              exact CKLaneC2R.Cells.S00.B074.c1483_pos (not_le.mp h1236).le h891 (not_le.mp h1233).le h1235
                          · -- right
                            by_cases h1237 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1484_pos (not_le.mp h892).le h891 (not_le.mp h1235).le h1237
                            · -- right
                              exact CKLaneC2R.Cells.S00.B074.c1485_pos (not_le.mp h892).le h891 (not_le.mp h1237).le hz2
    · -- right
      by_cases h1238 : a ≤ ((31/160 : ℚ) : ℝ)
      · -- left
        by_cases h1239 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h1240 : a ≤ ((61/320 : ℚ) : ℝ)
          · -- left
            by_cases h1241 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1242 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1243 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1244 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1245 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1246 : a ≤ ((121/640 : ℚ) : ℝ)
                      · -- left
                        by_cases h1247 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1269_pos (not_le.mp h891).le h1246 hz1 h1247
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1271_pos (not_le.mp h891).le h1246 (not_le.mp h1247).le h1245
                      · -- right
                        by_cases h1248 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1270_pos (not_le.mp h1246).le h1240 hz1 h1248
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1272_pos (not_le.mp h1246).le h1240 (not_le.mp h1248).le h1245
                    · -- right
                      by_cases h1249 : z ≤ ((13747/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1250 : a ≤ ((121/640 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1277_pos (not_le.mp h891).le h1250 (not_le.mp h1245).le h1249
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1278_pos (not_le.mp h1250).le h1240 (not_le.mp h1245).le h1249
                      · -- right
                        exact CKLaneC2R.Cells.S00.B041.c839_pos (not_le.mp h891).le h1240 (not_le.mp h1249).le h1244
                  · -- right
                    by_cases h1251 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1252 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c845_pos (not_le.mp h891).le h1240 (not_le.mp h1244).le h1252
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c846_pos (not_le.mp h891).le h1240 (not_le.mp h1252).le h1251
                    · -- right
                      by_cases h1253 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c849_pos (not_le.mp h891).le h1240 (not_le.mp h1251).le h1253
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c850_pos (not_le.mp h891).le h1240 (not_le.mp h1253).le h1243
                · -- right
                  by_cases h1254 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1255 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1256 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c893_pos (not_le.mp h891).le h1240 (not_le.mp h1243).le h1256
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c894_pos (not_le.mp h891).le h1240 (not_le.mp h1256).le h1255
                    · -- right
                      by_cases h1257 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c897_pos (not_le.mp h891).le h1240 (not_le.mp h1255).le h1257
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c898_pos (not_le.mp h891).le h1240 (not_le.mp h1257).le h1254
                  · -- right
                    by_cases h1258 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1259 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c909_pos (not_le.mp h891).le h1240 (not_le.mp h1254).le h1259
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c910_pos (not_le.mp h891).le h1240 (not_le.mp h1259).le h1258
                    · -- right
                      exact CKLaneC2R.Cells.S00.B009.c199_pos (not_le.mp h891).le h1240 (not_le.mp h1258).le h1242
              · -- right
                by_cases h1260 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1261 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1262 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c233_pos (not_le.mp h891).le h1240 (not_le.mp h1242).le h1262
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c234_pos (not_le.mp h891).le h1240 (not_le.mp h1262).le h1261
                  · -- right
                    by_cases h1263 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c237_pos (not_le.mp h891).le h1240 (not_le.mp h1261).le h1263
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c238_pos (not_le.mp h891).le h1240 (not_le.mp h1263).le h1260
                · -- right
                  by_cases h1264 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1265 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c249_pos (not_le.mp h891).le h1240 (not_le.mp h1260).le h1265
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c250_pos (not_le.mp h891).le h1240 (not_le.mp h1265).le h1264
                  · -- right
                    by_cases h1266 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c253_pos (not_le.mp h891).le h1240 (not_le.mp h1264).le h1266
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c254_pos (not_le.mp h891).le h1240 (not_le.mp h1266).le h1241
            · -- right
              by_cases h1267 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1268 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1269 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1270 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c297_pos (not_le.mp h891).le h1240 (not_le.mp h1241).le h1270
                    · -- right
                      exact CKLaneC2R.Cells.S00.B014.c298_pos (not_le.mp h891).le h1240 (not_le.mp h1270).le h1269
                  · -- right
                    by_cases h1271 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c301_pos (not_le.mp h891).le h1240 (not_le.mp h1269).le h1271
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c302_pos (not_le.mp h891).le h1240 (not_le.mp h1271).le h1268
                · -- right
                  by_cases h1272 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1273 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c313_pos (not_le.mp h891).le h1240 (not_le.mp h1268).le h1273
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c314_pos (not_le.mp h891).le h1240 (not_le.mp h1273).le h1272
                  · -- right
                    by_cases h1274 : z ≤ ((26503/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c317_pos (not_le.mp h891).le h1240 (not_le.mp h1272).le h1274
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c318_pos (not_le.mp h891).le h1240 (not_le.mp h1274).le h1267
              · -- right
                by_cases h1275 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1276 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c8_pos (not_le.mp h891).le h1240 (not_le.mp h1267).le h1276
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c10_pos (not_le.mp h891).le h1240 (not_le.mp h1276).le h1275
                · -- right
                  by_cases h1277 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c16_pos (not_le.mp h891).le h1240 (not_le.mp h1275).le h1277
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c18_pos (not_le.mp h891).le h1240 (not_le.mp h1277).le h1239
          · -- right
            by_cases h1278 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1279 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1280 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1281 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1282 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1283 : a ≤ ((123/640 : ℚ) : ℝ)
                      · -- left
                        by_cases h1284 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1273_pos (not_le.mp h1240).le h1283 hz1 h1284
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1275_pos (not_le.mp h1240).le h1283 (not_le.mp h1284).le h1282
                      · -- right
                        by_cases h1285 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1274_pos (not_le.mp h1283).le h1238 hz1 h1285
                        · -- right
                          exact CKLaneC2R.Cells.S00.B063.c1276_pos (not_le.mp h1283).le h1238 (not_le.mp h1285).le h1282
                    · -- right
                      by_cases h1286 : z ≤ ((13747/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1287 : a ≤ ((123/640 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B063.c1279_pos (not_le.mp h1240).le h1287 (not_le.mp h1282).le h1286
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1280_pos (not_le.mp h1287).le h1238 (not_le.mp h1282).le h1286
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c840_pos (not_le.mp h1240).le h1238 (not_le.mp h1286).le h1281
                  · -- right
                    by_cases h1288 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1289 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c847_pos (not_le.mp h1240).le h1238 (not_le.mp h1281).le h1289
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c848_pos (not_le.mp h1240).le h1238 (not_le.mp h1289).le h1288
                    · -- right
                      by_cases h1290 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c851_pos (not_le.mp h1240).le h1238 (not_le.mp h1288).le h1290
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c852_pos (not_le.mp h1240).le h1238 (not_le.mp h1290).le h1280
                · -- right
                  by_cases h1291 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1292 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1293 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c895_pos (not_le.mp h1240).le h1238 (not_le.mp h1280).le h1293
                      · -- right
                        exact CKLaneC2R.Cells.S00.B044.c896_pos (not_le.mp h1240).le h1238 (not_le.mp h1293).le h1292
                    · -- right
                      by_cases h1294 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B044.c899_pos (not_le.mp h1240).le h1238 (not_le.mp h1292).le h1294
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c900_pos (not_le.mp h1240).le h1238 (not_le.mp h1294).le h1291
                  · -- right
                    by_cases h1295 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1296 : z ≤ ((22877/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c911_pos (not_le.mp h1240).le h1238 (not_le.mp h1291).le h1296
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c912_pos (not_le.mp h1240).le h1238 (not_le.mp h1296).le h1295
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c200_pos (not_le.mp h1240).le h1238 (not_le.mp h1295).le h1279
              · -- right
                by_cases h1297 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1298 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1299 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c235_pos (not_le.mp h1240).le h1238 (not_le.mp h1279).le h1299
                    · -- right
                      exact CKLaneC2R.Cells.S00.B011.c236_pos (not_le.mp h1240).le h1238 (not_le.mp h1299).le h1298
                  · -- right
                    by_cases h1300 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B011.c239_pos (not_le.mp h1240).le h1238 (not_le.mp h1298).le h1300
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c240_pos (not_le.mp h1240).le h1238 (not_le.mp h1300).le h1297
                · -- right
                  by_cases h1301 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1302 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c251_pos (not_le.mp h1240).le h1238 (not_le.mp h1297).le h1302
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c252_pos (not_le.mp h1240).le h1238 (not_le.mp h1302).le h1301
                  · -- right
                    by_cases h1303 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c255_pos (not_le.mp h1240).le h1238 (not_le.mp h1301).le h1303
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c256_pos (not_le.mp h1240).le h1238 (not_le.mp h1303).le h1278
            · -- right
              by_cases h1304 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1305 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1306 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1307 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B014.c299_pos (not_le.mp h1240).le h1238 (not_le.mp h1278).le h1307
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c300_pos (not_le.mp h1240).le h1238 (not_le.mp h1307).le h1306
                  · -- right
                    by_cases h1308 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c303_pos (not_le.mp h1240).le h1238 (not_le.mp h1306).le h1308
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c304_pos (not_le.mp h1240).le h1238 (not_le.mp h1308).le h1305
                · -- right
                  by_cases h1309 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1310 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c315_pos (not_le.mp h1240).le h1238 (not_le.mp h1305).le h1310
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c316_pos (not_le.mp h1240).le h1238 (not_le.mp h1310).le h1309
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c0_pos (not_le.mp h1240).le h1238 (not_le.mp h1309).le h1304
              · -- right
                by_cases h1311 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1312 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c9_pos (not_le.mp h1240).le h1238 (not_le.mp h1304).le h1312
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c11_pos (not_le.mp h1240).le h1238 (not_le.mp h1312).le h1311
                · -- right
                  by_cases h1313 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c17_pos (not_le.mp h1240).le h1238 (not_le.mp h1311).le h1313
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c19_pos (not_le.mp h1240).le h1238 (not_le.mp h1313).le h1239
        · -- right
          by_cases h1314 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h1315 : a ≤ ((61/320 : ℚ) : ℝ)
            · -- left
              by_cases h1316 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1317 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1318 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c32_pos (not_le.mp h891).le h1315 (not_le.mp h1239).le h1318
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c34_pos (not_le.mp h891).le h1315 (not_le.mp h1318).le h1317
                · -- right
                  by_cases h1319 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c40_pos (not_le.mp h891).le h1315 (not_le.mp h1317).le h1319
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c42_pos (not_le.mp h891).le h1315 (not_le.mp h1319).le h1316
              · -- right
                by_cases h1320 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1321 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c51_pos (not_le.mp h891).le h1315 (not_le.mp h1316).le h1321
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c53_pos (not_le.mp h891).le h1315 (not_le.mp h1321).le h1320
                · -- right
                  by_cases h1322 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c59_pos (not_le.mp h891).le h1315 (not_le.mp h1320).le h1322
                  · -- right
                    by_cases h1323 : z ≤ ((9683/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B025.c515_pos (not_le.mp h891).le h1315 (not_le.mp h1322).le h1323
                    · -- right
                      exact CKLaneC2R.Cells.S00.B025.c516_pos (not_le.mp h891).le h1315 (not_le.mp h1323).le h1314
            · -- right
              by_cases h1324 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1325 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1326 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c33_pos (not_le.mp h1315).le h1238 (not_le.mp h1239).le h1326
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c35_pos (not_le.mp h1315).le h1238 (not_le.mp h1326).le h1325
                · -- right
                  by_cases h1327 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c41_pos (not_le.mp h1315).le h1238 (not_le.mp h1325).le h1327
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c43_pos (not_le.mp h1315).le h1238 (not_le.mp h1327).le h1324
              · -- right
                by_cases h1328 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1329 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c52_pos (not_le.mp h1315).le h1238 (not_le.mp h1324).le h1329
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c54_pos (not_le.mp h1315).le h1238 (not_le.mp h1329).le h1328
                · -- right
                  by_cases h1330 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B003.c60_pos (not_le.mp h1315).le h1238 (not_le.mp h1328).le h1330
                  · -- right
                    exact CKLaneC2R.Cells.S00.B003.c61_pos (not_le.mp h1315).le h1238 (not_le.mp h1330).le h1314
          · -- right
            by_cases h1331 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h1332 : a ≤ ((61/320 : ℚ) : ℝ)
              · -- left
                by_cases h1333 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1334 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1335 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c593_pos (not_le.mp h891).le h1332 (not_le.mp h1314).le h1335
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c594_pos (not_le.mp h891).le h1332 (not_le.mp h1335).le h1334
                  · -- right
                    by_cases h1336 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c597_pos (not_le.mp h891).le h1332 (not_le.mp h1334).le h1336
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c599_pos (not_le.mp h891).le h1332 (not_le.mp h1336).le h1333
                · -- right
                  by_cases h1337 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1338 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c623_pos (not_le.mp h891).le h1332 (not_le.mp h1333).le h1338
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c625_pos (not_le.mp h891).le h1332 (not_le.mp h1338).le h1337
                  · -- right
                    by_cases h1339 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c631_pos (not_le.mp h891).le h1332 (not_le.mp h1337).le h1339
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c633_pos (not_le.mp h891).le h1332 (not_le.mp h1339).le h1331
              · -- right
                by_cases h1340 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1341 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1342 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c595_pos (not_le.mp h1332).le h1238 (not_le.mp h1314).le h1342
                    · -- right
                      exact CKLaneC2R.Cells.S00.B029.c596_pos (not_le.mp h1332).le h1238 (not_le.mp h1342).le h1341
                  · -- right
                    by_cases h1343 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B029.c598_pos (not_le.mp h1332).le h1238 (not_le.mp h1341).le h1343
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c600_pos (not_le.mp h1332).le h1238 (not_le.mp h1343).le h1340
                · -- right
                  by_cases h1344 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1345 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c624_pos (not_le.mp h1332).le h1238 (not_le.mp h1340).le h1345
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c626_pos (not_le.mp h1332).le h1238 (not_le.mp h1345).le h1344
                  · -- right
                    by_cases h1346 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c632_pos (not_le.mp h1332).le h1238 (not_le.mp h1344).le h1346
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c634_pos (not_le.mp h1332).le h1238 (not_le.mp h1346).le h1331
            · -- right
              by_cases h1347 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h1348 : a ≤ ((61/320 : ℚ) : ℝ)
                · -- left
                  by_cases h1349 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1350 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c656_pos (not_le.mp h891).le h1348 (not_le.mp h1331).le h1350
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c658_pos (not_le.mp h891).le h1348 (not_le.mp h1350).le h1349
                  · -- right
                    by_cases h1351 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c664_pos (not_le.mp h891).le h1348 (not_le.mp h1349).le h1351
                    · -- right
                      by_cases h1352 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c991_pos (not_le.mp h891).le h1348 (not_le.mp h1351).le h1352
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c992_pos (not_le.mp h891).le h1348 (not_le.mp h1352).le h1347
                · -- right
                  by_cases h1353 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1354 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B032.c657_pos (not_le.mp h1348).le h1238 (not_le.mp h1331).le h1354
                    · -- right
                      exact CKLaneC2R.Cells.S00.B032.c659_pos (not_le.mp h1348).le h1238 (not_le.mp h1354).le h1353
                  · -- right
                    by_cases h1355 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c665_pos (not_le.mp h1348).le h1238 (not_le.mp h1353).le h1355
                    · -- right
                      by_cases h1356 : z ≤ ((23931/25600 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B049.c993_pos (not_le.mp h1348).le h1238 (not_le.mp h1355).le h1356
                      · -- right
                        exact CKLaneC2R.Cells.S00.B049.c994_pos (not_le.mp h1348).le h1238 (not_le.mp h1356).le h1347
              · -- right
                by_cases h1357 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h1358 : a ≤ ((61/320 : ℚ) : ℝ)
                  · -- left
                    by_cases h1359 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1360 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1038_pos (not_le.mp h891).le h1358 (not_le.mp h1347).le h1360
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1040_pos (not_le.mp h891).le h1358 (not_le.mp h1360).le h1359
                    · -- right
                      by_cases h1361 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1042_pos (not_le.mp h891).le h1358 (not_le.mp h1359).le h1361
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1044_pos (not_le.mp h891).le h1358 (not_le.mp h1361).le h1357
                  · -- right
                    by_cases h1362 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1363 : z ≤ ((121481/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B051.c1039_pos (not_le.mp h1358).le h1238 (not_le.mp h1347).le h1363
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1041_pos (not_le.mp h1358).le h1238 (not_le.mp h1363).le h1362
                    · -- right
                      by_cases h1364 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1043_pos (not_le.mp h1358).le h1238 (not_le.mp h1362).le h1364
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1045_pos (not_le.mp h1358).le h1238 (not_le.mp h1364).le h1357
                · -- right
                  by_cases h1365 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1366 : z ≤ ((125133/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1367 : a ≤ ((61/320 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1053_pos (not_le.mp h891).le h1367 (not_le.mp h1357).le h1366
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1054_pos (not_le.mp h1367).le h1238 (not_le.mp h1357).le h1366
                    · -- right
                      by_cases h1368 : z ≤ ((251179/256000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1057_pos (not_le.mp h891).le h1238 (not_le.mp h1366).le h1368
                      · -- right
                        by_cases h1369 : a ≤ ((61/320 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1341_pos (not_le.mp h891).le h1369 (not_le.mp h1368).le h1365
                        · -- right
                          exact CKLaneC2R.Cells.S00.B067.c1342_pos (not_le.mp h1369).le h1238 (not_le.mp h1368).le h1365
                  · -- right
                    by_cases h1370 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1371 : a ≤ ((61/320 : ℚ) : ℝ)
                      · -- left
                        by_cases h1372 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B067.c1359_pos (not_le.mp h891).le h1371 (not_le.mp h1365).le h1372
                        · -- right
                          exact CKLaneC2R.Cells.S00.B068.c1361_pos (not_le.mp h891).le h1371 (not_le.mp h1372).le h1370
                      · -- right
                        by_cases h1373 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B068.c1360_pos (not_le.mp h1371).le h1238 (not_le.mp h1365).le h1373
                        · -- right
                          exact CKLaneC2R.Cells.S00.B068.c1362_pos (not_le.mp h1371).le h1238 (not_le.mp h1373).le h1370
                    · -- right
                      by_cases h1374 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1375 : z ≤ ((508749/512000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B068.c1367_pos (not_le.mp h891).le h1238 (not_le.mp h1370).le h1375
                        · -- right
                          by_cases h1376 : a ≤ ((61/320 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1444_pos (not_le.mp h891).le h1376 (not_le.mp h1375).le h1374
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1445_pos (not_le.mp h1376).le h1238 (not_le.mp h1375).le h1374
                      · -- right
                        by_cases h1377 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          by_cases h1378 : a ≤ ((61/320 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1450_pos (not_le.mp h891).le h1378 (not_le.mp h1374).le h1377
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1451_pos (not_le.mp h1378).le h1238 (not_le.mp h1374).le h1377
                        · -- right
                          by_cases h1379 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1454_pos (not_le.mp h891).le h1238 (not_le.mp h1377).le h1379
                          · -- right
                            by_cases h1380 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1486_pos (not_le.mp h891).le h1238 (not_le.mp h1379).le h1380
                            · -- right
                              exact CKLaneC2R.Cells.S00.B074.c1487_pos (not_le.mp h891).le h1238 (not_le.mp h1380).le hz2
      · -- right
        by_cases h1381 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h1382 : a ≤ ((63/320 : ℚ) : ℝ)
          · -- left
            by_cases h1383 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1384 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1385 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1386 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1387 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1388 : a ≤ ((25/128 : ℚ) : ℝ)
                      · -- left
                        by_cases h1389 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1281_pos (not_le.mp h1238).le h1388 hz1 h1389
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1283_pos (not_le.mp h1238).le h1388 (not_le.mp h1389).le h1387
                      · -- right
                        by_cases h1390 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1282_pos (not_le.mp h1388).le h1382 hz1 h1390
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1284_pos (not_le.mp h1388).le h1382 (not_le.mp h1390).le h1387
                    · -- right
                      by_cases h1391 : z ≤ ((13747/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c841_pos (not_le.mp h1238).le h1382 (not_le.mp h1387).le h1391
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c842_pos (not_le.mp h1238).le h1382 (not_le.mp h1391).le h1386
                  · -- right
                    by_cases h1392 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1393 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c853_pos (not_le.mp h1238).le h1382 (not_le.mp h1386).le h1393
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c854_pos (not_le.mp h1238).le h1382 (not_le.mp h1393).le h1392
                    · -- right
                      by_cases h1394 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c857_pos (not_le.mp h1238).le h1382 (not_le.mp h1392).le h1394
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c858_pos (not_le.mp h1238).le h1382 (not_le.mp h1394).le h1385
                · -- right
                  by_cases h1395 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1396 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1397 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c901_pos (not_le.mp h1238).le h1382 (not_le.mp h1385).le h1397
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c902_pos (not_le.mp h1238).le h1382 (not_le.mp h1397).le h1396
                    · -- right
                      by_cases h1398 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c905_pos (not_le.mp h1238).le h1382 (not_le.mp h1396).le h1398
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c906_pos (not_le.mp h1238).le h1382 (not_le.mp h1398).le h1395
                  · -- right
                    by_cases h1399 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c201_pos (not_le.mp h1238).le h1382 (not_le.mp h1395).le h1399
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c203_pos (not_le.mp h1238).le h1382 (not_le.mp h1399).le h1384
              · -- right
                by_cases h1400 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1401 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1402 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c241_pos (not_le.mp h1238).le h1382 (not_le.mp h1384).le h1402
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c242_pos (not_le.mp h1238).le h1382 (not_le.mp h1402).le h1401
                  · -- right
                    by_cases h1403 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c245_pos (not_le.mp h1238).le h1382 (not_le.mp h1401).le h1403
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c246_pos (not_le.mp h1238).le h1382 (not_le.mp h1403).le h1400
                · -- right
                  by_cases h1404 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1405 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c257_pos (not_le.mp h1238).le h1382 (not_le.mp h1400).le h1405
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c258_pos (not_le.mp h1238).le h1382 (not_le.mp h1405).le h1404
                  · -- right
                    by_cases h1406 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c261_pos (not_le.mp h1238).le h1382 (not_le.mp h1404).le h1406
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c262_pos (not_le.mp h1238).le h1382 (not_le.mp h1406).le h1383
            · -- right
              by_cases h1407 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1408 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1409 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1410 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c305_pos (not_le.mp h1238).le h1382 (not_le.mp h1383).le h1410
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c306_pos (not_le.mp h1238).le h1382 (not_le.mp h1410).le h1409
                  · -- right
                    by_cases h1411 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c309_pos (not_le.mp h1238).le h1382 (not_le.mp h1409).le h1411
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c310_pos (not_le.mp h1238).le h1382 (not_le.mp h1411).le h1408
                · -- right
                  by_cases h1412 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1413 : z ≤ ((24677/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c319_pos (not_le.mp h1238).le h1382 (not_le.mp h1408).le h1413
                    · -- right
                      exact CKLaneC2R.Cells.S00.B016.c320_pos (not_le.mp h1238).le h1382 (not_le.mp h1413).le h1412
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c2_pos (not_le.mp h1238).le h1382 (not_le.mp h1412).le h1407
              · -- right
                by_cases h1414 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1415 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c12_pos (not_le.mp h1238).le h1382 (not_le.mp h1407).le h1415
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c14_pos (not_le.mp h1238).le h1382 (not_le.mp h1415).le h1414
                · -- right
                  by_cases h1416 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c20_pos (not_le.mp h1238).le h1382 (not_le.mp h1414).le h1416
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c22_pos (not_le.mp h1238).le h1382 (not_le.mp h1416).le h1381
          · -- right
            by_cases h1417 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h1418 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1419 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1420 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1421 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1422 : a ≤ ((127/640 : ℚ) : ℝ)
                      · -- left
                        by_cases h1423 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1285_pos (not_le.mp h1382).le h1422 hz1 h1423
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1287_pos (not_le.mp h1382).le h1422 (not_le.mp h1423).le h1421
                      · -- right
                        by_cases h1424 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B064.c1286_pos (not_le.mp h1422).le ha2 hz1 h1424
                        · -- right
                          exact CKLaneC2R.Cells.S00.B064.c1288_pos (not_le.mp h1422).le ha2 (not_le.mp h1424).le h1421
                    · -- right
                      by_cases h1425 : z ≤ ((13747/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c843_pos (not_le.mp h1382).le ha2 (not_le.mp h1421).le h1425
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c844_pos (not_le.mp h1382).le ha2 (not_le.mp h1425).le h1420
                  · -- right
                    by_cases h1426 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1427 : z ≤ ((15573/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c855_pos (not_le.mp h1382).le ha2 (not_le.mp h1420).le h1427
                      · -- right
                        exact CKLaneC2R.Cells.S00.B042.c856_pos (not_le.mp h1382).le ha2 (not_le.mp h1427).le h1426
                    · -- right
                      by_cases h1428 : z ≤ ((17399/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B042.c859_pos (not_le.mp h1382).le ha2 (not_le.mp h1426).le h1428
                      · -- right
                        exact CKLaneC2R.Cells.S00.B043.c860_pos (not_le.mp h1382).le ha2 (not_le.mp h1428).le h1419
                · -- right
                  by_cases h1429 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1430 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1431 : z ≤ ((769/5120 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c903_pos (not_le.mp h1382).le ha2 (not_le.mp h1419).le h1431
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c904_pos (not_le.mp h1382).le ha2 (not_le.mp h1431).le h1430
                    · -- right
                      by_cases h1432 : z ≤ ((21051/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B045.c907_pos (not_le.mp h1382).le ha2 (not_le.mp h1430).le h1432
                      · -- right
                        exact CKLaneC2R.Cells.S00.B045.c908_pos (not_le.mp h1382).le ha2 (not_le.mp h1432).le h1429
                  · -- right
                    by_cases h1433 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B010.c202_pos (not_le.mp h1382).le ha2 (not_le.mp h1429).le h1433
                    · -- right
                      exact CKLaneC2R.Cells.S00.B010.c204_pos (not_le.mp h1382).le ha2 (not_le.mp h1433).le h1418
              · -- right
                by_cases h1434 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1435 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1436 : z ≤ ((13721/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c243_pos (not_le.mp h1382).le ha2 (not_le.mp h1418).le h1436
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c244_pos (not_le.mp h1382).le ha2 (not_le.mp h1436).le h1435
                  · -- right
                    by_cases h1437 : z ≤ ((15547/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c247_pos (not_le.mp h1382).le ha2 (not_le.mp h1435).le h1437
                    · -- right
                      exact CKLaneC2R.Cells.S00.B012.c248_pos (not_le.mp h1382).le ha2 (not_le.mp h1437).le h1434
                · -- right
                  by_cases h1438 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1439 : z ≤ ((17373/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B012.c259_pos (not_le.mp h1382).le ha2 (not_le.mp h1434).le h1439
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c260_pos (not_le.mp h1382).le ha2 (not_le.mp h1439).le h1438
                  · -- right
                    by_cases h1440 : z ≤ ((19199/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B013.c263_pos (not_le.mp h1382).le ha2 (not_le.mp h1438).le h1440
                    · -- right
                      exact CKLaneC2R.Cells.S00.B013.c264_pos (not_le.mp h1382).le ha2 (not_le.mp h1440).le h1417
            · -- right
              by_cases h1441 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1442 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1443 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1444 : z ≤ ((841/2560 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c307_pos (not_le.mp h1382).le ha2 (not_le.mp h1417).le h1444
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c308_pos (not_le.mp h1382).le ha2 (not_le.mp h1444).le h1443
                  · -- right
                    by_cases h1445 : z ≤ ((22851/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B015.c311_pos (not_le.mp h1382).le ha2 (not_le.mp h1443).le h1445
                    · -- right
                      exact CKLaneC2R.Cells.S00.B015.c312_pos (not_le.mp h1382).le ha2 (not_le.mp h1445).le h1442
                · -- right
                  by_cases h1446 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c1_pos (not_le.mp h1382).le ha2 (not_le.mp h1442).le h1446
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c3_pos (not_le.mp h1382).le ha2 (not_le.mp h1446).le h1441
              · -- right
                by_cases h1447 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1448 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B000.c13_pos (not_le.mp h1382).le ha2 (not_le.mp h1441).le h1448
                  · -- right
                    exact CKLaneC2R.Cells.S00.B000.c15_pos (not_le.mp h1382).le ha2 (not_le.mp h1448).le h1447
                · -- right
                  by_cases h1449 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c21_pos (not_le.mp h1382).le ha2 (not_le.mp h1447).le h1449
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c23_pos (not_le.mp h1382).le ha2 (not_le.mp h1449).le h1381
        · -- right
          by_cases h1450 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h1451 : a ≤ ((63/320 : ℚ) : ℝ)
            · -- left
              by_cases h1452 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1453 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1454 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c36_pos (not_le.mp h1238).le h1451 (not_le.mp h1381).le h1454
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c38_pos (not_le.mp h1238).le h1451 (not_le.mp h1454).le h1453
                · -- right
                  by_cases h1455 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c44_pos (not_le.mp h1238).le h1451 (not_le.mp h1453).le h1455
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c46_pos (not_le.mp h1238).le h1451 (not_le.mp h1455).le h1452
              · -- right
                by_cases h1456 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1457 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c55_pos (not_le.mp h1238).le h1451 (not_le.mp h1452).le h1457
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c57_pos (not_le.mp h1238).le h1451 (not_le.mp h1457).le h1456
                · -- right
                  by_cases h1458 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B003.c62_pos (not_le.mp h1238).le h1451 (not_le.mp h1456).le h1458
                  · -- right
                    exact CKLaneC2R.Cells.S00.B003.c64_pos (not_le.mp h1238).le h1451 (not_le.mp h1458).le h1450
            · -- right
              by_cases h1459 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h1460 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1461 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B001.c37_pos (not_le.mp h1451).le ha2 (not_le.mp h1381).le h1461
                  · -- right
                    exact CKLaneC2R.Cells.S00.B001.c39_pos (not_le.mp h1451).le ha2 (not_le.mp h1461).le h1460
                · -- right
                  by_cases h1462 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c45_pos (not_le.mp h1451).le ha2 (not_le.mp h1460).le h1462
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c47_pos (not_le.mp h1451).le ha2 (not_le.mp h1462).le h1459
              · -- right
                by_cases h1463 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h1464 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B002.c56_pos (not_le.mp h1451).le ha2 (not_le.mp h1459).le h1464
                  · -- right
                    exact CKLaneC2R.Cells.S00.B002.c58_pos (not_le.mp h1451).le ha2 (not_le.mp h1464).le h1463
                · -- right
                  by_cases h1465 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B003.c63_pos (not_le.mp h1451).le ha2 (not_le.mp h1463).le h1465
                  · -- right
                    exact CKLaneC2R.Cells.S00.B003.c65_pos (not_le.mp h1451).le ha2 (not_le.mp h1465).le h1450
          · -- right
            by_cases h1466 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h1467 : a ≤ ((63/320 : ℚ) : ℝ)
              · -- left
                by_cases h1468 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1469 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1470 : z ≤ ((50241/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c601_pos (not_le.mp h1238).le h1467 (not_le.mp h1450).le h1470
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c602_pos (not_le.mp h1238).le h1467 (not_le.mp h1470).le h1469
                  · -- right
                    by_cases h1471 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c603_pos (not_le.mp h1238).le h1467 (not_le.mp h1469).le h1471
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c605_pos (not_le.mp h1238).le h1467 (not_le.mp h1471).le h1468
                · -- right
                  by_cases h1472 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1473 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c627_pos (not_le.mp h1238).le h1467 (not_le.mp h1468).le h1473
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c629_pos (not_le.mp h1238).le h1467 (not_le.mp h1473).le h1472
                  · -- right
                    by_cases h1474 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c635_pos (not_le.mp h1238).le h1467 (not_le.mp h1472).le h1474
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c637_pos (not_le.mp h1238).le h1467 (not_le.mp h1474).le h1466
              · -- right
                by_cases h1475 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h1476 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S00.B003.c66_pos (not_le.mp h1467).le ha2 (not_le.mp h1450).le h1476
                  · -- right
                    by_cases h1477 : z ≤ ((52067/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B030.c604_pos (not_le.mp h1467).le ha2 (not_le.mp h1476).le h1477
                    · -- right
                      exact CKLaneC2R.Cells.S00.B030.c606_pos (not_le.mp h1467).le ha2 (not_le.mp h1477).le h1475
                · -- right
                  by_cases h1478 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1479 : z ≤ ((53893/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c628_pos (not_le.mp h1467).le ha2 (not_le.mp h1475).le h1479
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c630_pos (not_le.mp h1467).le ha2 (not_le.mp h1479).le h1478
                  · -- right
                    by_cases h1480 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B031.c636_pos (not_le.mp h1467).le ha2 (not_le.mp h1478).le h1480
                    · -- right
                      exact CKLaneC2R.Cells.S00.B031.c638_pos (not_le.mp h1467).le ha2 (not_le.mp h1480).le h1466
            · -- right
              by_cases h1481 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h1482 : z ≤ ((29229/32000 : ℚ) : ℝ)
                · -- left
                  by_cases h1483 : a ≤ ((63/320 : ℚ) : ℝ)
                  · -- left
                    by_cases h1484 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c660_pos (not_le.mp h1238).le h1483 (not_le.mp h1466).le h1484
                    · -- right
                      exact CKLaneC2R.Cells.S00.B033.c662_pos (not_le.mp h1238).le h1483 (not_le.mp h1484).le h1482
                  · -- right
                    by_cases h1485 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c661_pos (not_le.mp h1483).le ha2 (not_le.mp h1466).le h1485
                    · -- right
                      exact CKLaneC2R.Cells.S00.B033.c663_pos (not_le.mp h1483).le ha2 (not_le.mp h1485).le h1482
                · -- right
                  by_cases h1486 : z ≤ ((59371/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1487 : a ≤ ((63/320 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c666_pos (not_le.mp h1238).le h1487 (not_le.mp h1482).le h1486
                    · -- right
                      exact CKLaneC2R.Cells.S00.B033.c667_pos (not_le.mp h1487).le ha2 (not_le.mp h1482).le h1486
                  · -- right
                    by_cases h1488 : z ≤ ((23931/25600 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c668_pos (not_le.mp h1238).le ha2 (not_le.mp h1486).le h1488
                    · -- right
                      exact CKLaneC2R.Cells.S00.B033.c669_pos (not_le.mp h1238).le ha2 (not_le.mp h1488).le h1481
              · -- right
                by_cases h1489 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h1490 : z ≤ ((61197/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1491 : z ≤ ((121481/128000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S00.B033.c670_pos (not_le.mp h1238).le ha2 (not_le.mp h1481).le h1491
                    · -- right
                      exact CKLaneC2R.Cells.S00.B033.c671_pos (not_le.mp h1238).le ha2 (not_le.mp h1491).le h1490
                  · -- right
                    by_cases h1492 : a ≤ ((63/320 : ℚ) : ℝ)
                    · -- left
                      by_cases h1493 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1046_pos (not_le.mp h1238).le h1492 (not_le.mp h1490).le h1493
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1048_pos (not_le.mp h1238).le h1492 (not_le.mp h1493).le h1489
                    · -- right
                      by_cases h1494 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1047_pos (not_le.mp h1492).le ha2 (not_le.mp h1490).le h1494
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1049_pos (not_le.mp h1492).le ha2 (not_le.mp h1494).le h1489
                · -- right
                  by_cases h1495 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1496 : z ≤ ((125133/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1497 : a ≤ ((63/320 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1055_pos (not_le.mp h1238).le h1497 (not_le.mp h1489).le h1496
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1056_pos (not_le.mp h1497).le ha2 (not_le.mp h1489).le h1496
                    · -- right
                      by_cases h1498 : z ≤ ((251179/256000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S00.B052.c1058_pos (not_le.mp h1238).le ha2 (not_le.mp h1496).le h1498
                      · -- right
                        exact CKLaneC2R.Cells.S00.B052.c1059_pos (not_le.mp h1238).le ha2 (not_le.mp h1498).le h1495
                  · -- right
                    by_cases h1499 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1500 : a ≤ ((63/320 : ℚ) : ℝ)
                      · -- left
                        by_cases h1501 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B068.c1363_pos (not_le.mp h1238).le h1500 (not_le.mp h1495).le h1501
                        · -- right
                          exact CKLaneC2R.Cells.S00.B068.c1365_pos (not_le.mp h1238).le h1500 (not_le.mp h1501).le h1499
                      · -- right
                        by_cases h1502 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B068.c1364_pos (not_le.mp h1500).le ha2 (not_le.mp h1495).le h1502
                        · -- right
                          exact CKLaneC2R.Cells.S00.B068.c1366_pos (not_le.mp h1500).le ha2 (not_le.mp h1502).le h1499
                    · -- right
                      by_cases h1503 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1504 : z ≤ ((508749/512000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S00.B068.c1368_pos (not_le.mp h1238).le ha2 (not_le.mp h1499).le h1504
                        · -- right
                          exact CKLaneC2R.Cells.S00.B068.c1369_pos (not_le.mp h1238).le ha2 (not_le.mp h1504).le h1503
                      · -- right
                        by_cases h1505 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          by_cases h1506 : z ≤ ((1020237/1024000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1452_pos (not_le.mp h1238).le ha2 (not_le.mp h1503).le h1506
                          · -- right
                            exact CKLaneC2R.Cells.S00.B072.c1453_pos (not_le.mp h1238).le ha2 (not_le.mp h1506).le h1505
                        · -- right
                          by_cases h1507 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S00.B072.c1455_pos (not_le.mp h1238).le ha2 (not_le.mp h1505).le h1507
                          · -- right
                            by_cases h1508 : z ≤ ((2045039/2048000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S00.B074.c1488_pos (not_le.mp h1238).le ha2 (not_le.mp h1507).le h1508
                            · -- right
                              exact CKLaneC2R.Cells.S00.B074.c1489_pos (not_le.mp h1238).le ha2 (not_le.mp h1508).le hz2

end CKLaneC2R.CompactCover

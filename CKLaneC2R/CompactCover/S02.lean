import CKLaneC2R.Cells.S02.B000
import CKLaneC2R.Cells.S02.B001
import CKLaneC2R.Cells.S02.B002
import CKLaneC2R.Cells.S02.B003
import CKLaneC2R.Cells.S02.B004
import CKLaneC2R.Cells.S02.B005
import CKLaneC2R.Cells.S02.B006
import CKLaneC2R.Cells.S02.B007
import CKLaneC2R.Cells.S02.B008
import CKLaneC2R.Cells.S02.B009
import CKLaneC2R.Cells.S02.B010
import CKLaneC2R.Cells.S02.B011
import CKLaneC2R.Cells.S02.B012
import CKLaneC2R.Cells.S02.B013
import CKLaneC2R.Cells.S02.B014
import CKLaneC2R.Cells.S02.B015
import CKLaneC2R.Cells.S02.B016
import CKLaneC2R.Cells.S02.B017
import CKLaneC2R.Cells.S02.B018
import CKLaneC2R.Cells.S02.B019
import CKLaneC2R.Cells.S02.B020
import CKLaneC2R.Cells.S02.B021
import CKLaneC2R.Cells.S02.B022
import CKLaneC2R.Cells.S02.B023
import CKLaneC2R.Cells.S02.B024
import CKLaneC2R.Cells.S02.B025
import CKLaneC2R.Cells.S02.B026
import CKLaneC2R.Cells.S02.B027
import CKLaneC2R.Cells.S02.B028
import CKLaneC2R.Cells.S02.B029
import CKLaneC2R.Cells.S02.B030
import CKLaneC2R.Cells.S02.B031
import CKLaneC2R.Cells.S02.B032
import CKLaneC2R.Cells.S02.B033
import CKLaneC2R.Cells.S02.B034
import CKLaneC2R.Cells.S02.B035
import CKLaneC2R.Cells.S02.B036
import CKLaneC2R.Cells.S02.B037
import CKLaneC2R.Cells.S02.B038
import CKLaneC2R.Cells.S02.B039
import CKLaneC2R.Cells.S02.B040
import CKLaneC2R.Cells.S02.B041
import CKLaneC2R.Cells.S02.B042

namespace CKLaneC2R.CompactCover

/-- Compact cover of strip 2: a ∈ [3/10,1/2], z ∈ [43/500,999/1000] (858 cells, BSP depth 14). -/
theorem strip2 {a z : ℝ} (ha1 : ((3/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((1/2 : ℚ) : ℝ))
    (hz1 : ((43/500 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((999/1000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((2/5 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((7/20 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((13/40 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((5/16 : ℚ) : ℝ)
        · -- left
          by_cases h4 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h5 : a ≤ ((49/160 : ℚ) : ℝ)
            · -- left
              by_cases h6 : z ≤ ((1257/4000 : ℚ) : ℝ)
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
                          exact CKLaneC2R.Cells.S02.B037.c755_pos ha1 h5 hz1 h11
                        · -- right
                          exact CKLaneC2R.Cells.S02.B037.c756_pos ha1 h5 (not_le.mp h11).le h10
                      · -- right
                        by_cases h12 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B037.c759_pos ha1 h5 (not_le.mp h10).le h12
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c760_pos ha1 h5 (not_le.mp h12).le h9
                    · -- right
                      by_cases h13 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B028.c579_pos ha1 h5 (not_le.mp h9).le h13
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c581_pos ha1 h5 (not_le.mp h13).le h8
                  · -- right
                    by_cases h14 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h15 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c587_pos ha1 h5 (not_le.mp h8).le h15
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c588_pos ha1 h5 (not_le.mp h15).le h14
                    · -- right
                      by_cases h16 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c591_pos ha1 h5 (not_le.mp h14).le h16
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c592_pos ha1 h5 (not_le.mp h16).le h7
                · -- right
                  by_cases h17 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h18 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h19 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c629_pos ha1 h5 (not_le.mp h7).le h19
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c630_pos ha1 h5 (not_le.mp h19).le h18
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c291_pos ha1 h5 (not_le.mp h18).le h17
                  · -- right
                    by_cases h20 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B014.c296_pos ha1 h5 (not_le.mp h17).le h20
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c298_pos ha1 h5 (not_le.mp h20).le h6
              · -- right
                by_cases h21 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h22 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h23 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c320_pos ha1 h5 (not_le.mp h6).le h23
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c322_pos ha1 h5 (not_le.mp h23).le h22
                  · -- right
                    by_cases h24 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c328_pos ha1 h5 (not_le.mp h22).le h24
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c330_pos ha1 h5 (not_le.mp h24).le h21
                · -- right
                  by_cases h25 : z ≤ ((7767/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h26 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c336_pos ha1 h5 (not_le.mp h21).le h26
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c338_pos ha1 h5 (not_le.mp h26).le h25
                  · -- right
                    by_cases h27 : z ≤ ((16447/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c344_pos ha1 h5 (not_le.mp h25).le h27
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c346_pos ha1 h5 (not_le.mp h27).le h4
            · -- right
              by_cases h28 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h29 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h30 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h31 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h32 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h33 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B037.c757_pos (not_le.mp h5).le h3 hz1 h33
                        · -- right
                          exact CKLaneC2R.Cells.S02.B037.c758_pos (not_le.mp h5).le h3 (not_le.mp h33).le h32
                      · -- right
                        by_cases h34 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c761_pos (not_le.mp h5).le h3 (not_le.mp h32).le h34
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c762_pos (not_le.mp h5).le h3 (not_le.mp h34).le h31
                    · -- right
                      by_cases h35 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c580_pos (not_le.mp h5).le h3 (not_le.mp h31).le h35
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c582_pos (not_le.mp h5).le h3 (not_le.mp h35).le h30
                  · -- right
                    by_cases h36 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h37 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c589_pos (not_le.mp h5).le h3 (not_le.mp h30).le h37
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c590_pos (not_le.mp h5).le h3 (not_le.mp h37).le h36
                    · -- right
                      by_cases h38 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c593_pos (not_le.mp h5).le h3 (not_le.mp h36).le h38
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c594_pos (not_le.mp h5).le h3 (not_le.mp h38).le h29
                · -- right
                  by_cases h39 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h40 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h41 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c631_pos (not_le.mp h5).le h3 (not_le.mp h29).le h41
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c632_pos (not_le.mp h5).le h3 (not_le.mp h41).le h40
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c292_pos (not_le.mp h5).le h3 (not_le.mp h40).le h39
                  · -- right
                    by_cases h42 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B014.c297_pos (not_le.mp h5).le h3 (not_le.mp h39).le h42
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c299_pos (not_le.mp h5).le h3 (not_le.mp h42).le h28
              · -- right
                by_cases h43 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h44 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h45 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c321_pos (not_le.mp h5).le h3 (not_le.mp h28).le h45
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c323_pos (not_le.mp h5).le h3 (not_le.mp h45).le h44
                  · -- right
                    by_cases h46 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c329_pos (not_le.mp h5).le h3 (not_le.mp h44).le h46
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c331_pos (not_le.mp h5).le h3 (not_le.mp h46).le h43
                · -- right
                  by_cases h47 : z ≤ ((7767/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h48 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c337_pos (not_le.mp h5).le h3 (not_le.mp h43).le h48
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c339_pos (not_le.mp h5).le h3 (not_le.mp h48).le h47
                  · -- right
                    by_cases h49 : z ≤ ((16447/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c345_pos (not_le.mp h5).le h3 (not_le.mp h47).le h49
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c347_pos (not_le.mp h5).le h3 (not_le.mp h49).le h4
          · -- right
            by_cases h50 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h51 : a ≤ ((49/160 : ℚ) : ℝ)
              · -- left
                by_cases h52 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h53 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h54 : z ≤ ((18273/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c457_pos ha1 h51 (not_le.mp h4).le h54
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c459_pos ha1 h51 (not_le.mp h54).le h53
                  · -- right
                    by_cases h55 : z ≤ ((20099/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c465_pos ha1 h51 (not_le.mp h53).le h55
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c467_pos ha1 h51 (not_le.mp h55).le h52
                · -- right
                  by_cases h56 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h57 : z ≤ ((877/1280 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c473_pos ha1 h51 (not_le.mp h52).le h57
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c475_pos ha1 h51 (not_le.mp h57).le h56
                  · -- right
                    by_cases h58 : z ≤ ((23751/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c481_pos ha1 h51 (not_le.mp h56).le h58
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c483_pos ha1 h51 (not_le.mp h58).le h50
              · -- right
                by_cases h59 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h60 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h61 : z ≤ ((18273/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c458_pos (not_le.mp h51).le h3 (not_le.mp h4).le h61
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c460_pos (not_le.mp h51).le h3 (not_le.mp h61).le h60
                  · -- right
                    by_cases h62 : z ≤ ((20099/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c466_pos (not_le.mp h51).le h3 (not_le.mp h60).le h62
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c468_pos (not_le.mp h51).le h3 (not_le.mp h62).le h59
                · -- right
                  by_cases h63 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h64 : z ≤ ((877/1280 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c474_pos (not_le.mp h51).le h3 (not_le.mp h59).le h64
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c476_pos (not_le.mp h51).le h3 (not_le.mp h64).le h63
                  · -- right
                    by_cases h65 : z ≤ ((23751/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c482_pos (not_le.mp h51).le h3 (not_le.mp h63).le h65
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c484_pos (not_le.mp h51).le h3 (not_le.mp h65).le h50
            · -- right
              by_cases h66 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h67 : a ≤ ((49/160 : ℚ) : ℝ)
                · -- left
                  by_cases h68 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h69 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c489_pos ha1 h67 (not_le.mp h50).le h69
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c491_pos ha1 h67 (not_le.mp h69).le h68
                  · -- right
                    by_cases h70 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c497_pos ha1 h67 (not_le.mp h68).le h70
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c499_pos ha1 h67 (not_le.mp h70).le h66
                · -- right
                  by_cases h71 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h72 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c490_pos (not_le.mp h67).le h3 (not_le.mp h50).le h72
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c492_pos (not_le.mp h67).le h3 (not_le.mp h72).le h71
                  · -- right
                    by_cases h73 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c498_pos (not_le.mp h67).le h3 (not_le.mp h71).le h73
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c500_pos (not_le.mp h67).le h3 (not_le.mp h73).le h66
              · -- right
                by_cases h74 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h75 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h76 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c519_pos ha1 h3 (not_le.mp h66).le h76
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c520_pos ha1 h3 (not_le.mp h76).le h75
                  · -- right
                    by_cases h77 : a ≤ ((49/160 : ℚ) : ℝ)
                    · -- left
                      by_cases h78 : z ≤ ((59371/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c697_pos ha1 h77 (not_le.mp h75).le h78
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c699_pos ha1 h77 (not_le.mp h78).le h74
                    · -- right
                      by_cases h79 : z ≤ ((59371/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c698_pos (not_le.mp h77).le h3 (not_le.mp h75).le h79
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c700_pos (not_le.mp h77).le h3 (not_le.mp h79).le h74
                · -- right
                  by_cases h80 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h81 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h82 : a ≤ ((49/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c701_pos ha1 h82 (not_le.mp h74).le h81
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c702_pos (not_le.mp h82).le h3 (not_le.mp h74).le h81
                    · -- right
                      by_cases h83 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c705_pos ha1 h3 (not_le.mp h81).le h83
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c706_pos ha1 h3 (not_le.mp h83).le h80
                  · -- right
                    by_cases h84 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h85 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c717_pos ha1 h3 (not_le.mp h80).le h85
                      · -- right
                        by_cases h86 : a ≤ ((49/160 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c779_pos ha1 h86 (not_le.mp h85).le h84
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c780_pos (not_le.mp h86).le h3 (not_le.mp h85).le h84
                    · -- right
                      by_cases h87 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h88 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c783_pos ha1 h3 (not_le.mp h84).le h88
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c784_pos ha1 h3 (not_le.mp h88).le h87
                      · -- right
                        by_cases h89 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h90 : a ≤ ((49/160 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B040.c814_pos ha1 h90 (not_le.mp h87).le h89
                          · -- right
                            exact CKLaneC2R.Cells.S02.B040.c815_pos (not_le.mp h90).le h3 (not_le.mp h87).le h89
                        · -- right
                          by_cases h91 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B040.c818_pos ha1 h3 (not_le.mp h89).le h91
                          · -- right
                            by_cases h92 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B041.c838_pos ha1 h3 (not_le.mp h91).le h92
                            · -- right
                              exact CKLaneC2R.Cells.S02.B041.c839_pos ha1 h3 (not_le.mp h92).le hz2
        · -- right
          by_cases h93 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h94 : a ≤ ((51/160 : ℚ) : ℝ)
            · -- left
              by_cases h95 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h96 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h97 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h98 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h99 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h100 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c763_pos (not_le.mp h3).le h94 hz1 h100
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c764_pos (not_le.mp h3).le h94 (not_le.mp h100).le h99
                      · -- right
                        by_cases h101 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c767_pos (not_le.mp h3).le h94 (not_le.mp h99).le h101
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c768_pos (not_le.mp h3).le h94 (not_le.mp h101).le h98
                    · -- right
                      by_cases h102 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c583_pos (not_le.mp h3).le h94 (not_le.mp h98).le h102
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c585_pos (not_le.mp h3).le h94 (not_le.mp h102).le h97
                  · -- right
                    by_cases h103 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h104 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c595_pos (not_le.mp h3).le h94 (not_le.mp h97).le h104
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c596_pos (not_le.mp h3).le h94 (not_le.mp h104).le h103
                    · -- right
                      by_cases h105 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c599_pos (not_le.mp h3).le h94 (not_le.mp h103).le h105
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c600_pos (not_le.mp h3).le h94 (not_le.mp h105).le h96
                · -- right
                  by_cases h106 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h107 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h108 : z ≤ ((13721/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c633_pos (not_le.mp h3).le h94 (not_le.mp h96).le h108
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c634_pos (not_le.mp h3).le h94 (not_le.mp h108).le h107
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c294_pos (not_le.mp h3).le h94 (not_le.mp h107).le h106
                  · -- right
                    by_cases h109 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c300_pos (not_le.mp h3).le h94 (not_le.mp h106).le h109
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c302_pos (not_le.mp h3).le h94 (not_le.mp h109).le h95
              · -- right
                by_cases h110 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h111 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h112 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c324_pos (not_le.mp h3).le h94 (not_le.mp h95).le h112
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c326_pos (not_le.mp h3).le h94 (not_le.mp h112).le h111
                  · -- right
                    by_cases h113 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c332_pos (not_le.mp h3).le h94 (not_le.mp h111).le h113
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c334_pos (not_le.mp h3).le h94 (not_le.mp h113).le h110
                · -- right
                  by_cases h114 : z ≤ ((7767/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h115 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c340_pos (not_le.mp h3).le h94 (not_le.mp h110).le h115
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c342_pos (not_le.mp h3).le h94 (not_le.mp h115).le h114
                  · -- right
                    by_cases h116 : z ≤ ((16447/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c348_pos (not_le.mp h3).le h94 (not_le.mp h114).le h116
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c350_pos (not_le.mp h3).le h94 (not_le.mp h116).le h93
            · -- right
              by_cases h117 : z ≤ ((1257/4000 : ℚ) : ℝ)
              · -- left
                by_cases h118 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h119 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h120 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h121 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h122 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c765_pos (not_le.mp h94).le h2 hz1 h122
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c766_pos (not_le.mp h94).le h2 (not_le.mp h122).le h121
                      · -- right
                        by_cases h123 : z ≤ ((13747/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c769_pos (not_le.mp h94).le h2 (not_le.mp h121).le h123
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c770_pos (not_le.mp h94).le h2 (not_le.mp h123).le h120
                    · -- right
                      by_cases h124 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c584_pos (not_le.mp h94).le h2 (not_le.mp h120).le h124
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c586_pos (not_le.mp h94).le h2 (not_le.mp h124).le h119
                  · -- right
                    by_cases h125 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h126 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B029.c597_pos (not_le.mp h94).le h2 (not_le.mp h119).le h126
                      · -- right
                        exact CKLaneC2R.Cells.S02.B029.c598_pos (not_le.mp h94).le h2 (not_le.mp h126).le h125
                    · -- right
                      by_cases h127 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c601_pos (not_le.mp h94).le h2 (not_le.mp h125).le h127
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c602_pos (not_le.mp h94).le h2 (not_le.mp h127).le h118
                · -- right
                  by_cases h128 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h129 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B014.c293_pos (not_le.mp h94).le h2 (not_le.mp h118).le h129
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c295_pos (not_le.mp h94).le h2 (not_le.mp h129).le h128
                  · -- right
                    by_cases h130 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c301_pos (not_le.mp h94).le h2 (not_le.mp h128).le h130
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c303_pos (not_le.mp h94).le h2 (not_le.mp h130).le h117
              · -- right
                by_cases h131 : z ≤ ((3427/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h132 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h133 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c325_pos (not_le.mp h94).le h2 (not_le.mp h117).le h133
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c327_pos (not_le.mp h94).le h2 (not_le.mp h133).le h132
                  · -- right
                    by_cases h134 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B016.c333_pos (not_le.mp h94).le h2 (not_le.mp h132).le h134
                    · -- right
                      exact CKLaneC2R.Cells.S02.B016.c335_pos (not_le.mp h94).le h2 (not_le.mp h134).le h131
                · -- right
                  by_cases h135 : z ≤ ((7767/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h136 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c341_pos (not_le.mp h94).le h2 (not_le.mp h131).le h136
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c343_pos (not_le.mp h94).le h2 (not_le.mp h136).le h135
                  · -- right
                    by_cases h137 : z ≤ ((16447/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c349_pos (not_le.mp h94).le h2 (not_le.mp h135).le h137
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c351_pos (not_le.mp h94).le h2 (not_le.mp h137).le h93
          · -- right
            by_cases h138 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h139 : a ≤ ((51/160 : ℚ) : ℝ)
              · -- left
                by_cases h140 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h141 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h142 : z ≤ ((18273/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c461_pos (not_le.mp h3).le h139 (not_le.mp h93).le h142
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c463_pos (not_le.mp h3).le h139 (not_le.mp h142).le h141
                  · -- right
                    by_cases h143 : z ≤ ((20099/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c469_pos (not_le.mp h3).le h139 (not_le.mp h141).le h143
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c471_pos (not_le.mp h3).le h139 (not_le.mp h143).le h140
                · -- right
                  by_cases h144 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h145 : z ≤ ((877/1280 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c477_pos (not_le.mp h3).le h139 (not_le.mp h140).le h145
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c479_pos (not_le.mp h3).le h139 (not_le.mp h145).le h144
                  · -- right
                    by_cases h146 : z ≤ ((23751/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c485_pos (not_le.mp h3).le h139 (not_le.mp h144).le h146
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c487_pos (not_le.mp h3).le h139 (not_le.mp h146).le h138
              · -- right
                by_cases h147 : z ≤ ((5253/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h148 : z ≤ ((9593/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h149 : z ≤ ((18273/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c462_pos (not_le.mp h139).le h2 (not_le.mp h93).le h149
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c464_pos (not_le.mp h139).le h2 (not_le.mp h149).le h148
                  · -- right
                    by_cases h150 : z ≤ ((20099/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c470_pos (not_le.mp h139).le h2 (not_le.mp h148).le h150
                    · -- right
                      exact CKLaneC2R.Cells.S02.B023.c472_pos (not_le.mp h139).le h2 (not_le.mp h150).le h147
                · -- right
                  by_cases h151 : z ≤ ((11419/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h152 : z ≤ ((877/1280 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B023.c478_pos (not_le.mp h139).le h2 (not_le.mp h147).le h152
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c480_pos (not_le.mp h139).le h2 (not_le.mp h152).le h151
                  · -- right
                    by_cases h153 : z ≤ ((23751/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c486_pos (not_le.mp h139).le h2 (not_le.mp h151).le h153
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c488_pos (not_le.mp h139).le h2 (not_le.mp h153).le h138
            · -- right
              by_cases h154 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h155 : a ≤ ((51/160 : ℚ) : ℝ)
                · -- left
                  by_cases h156 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h157 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c493_pos (not_le.mp h3).le h155 (not_le.mp h138).le h157
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c495_pos (not_le.mp h3).le h155 (not_le.mp h157).le h156
                  · -- right
                    by_cases h158 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c501_pos (not_le.mp h3).le h155 (not_le.mp h156).le h158
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c503_pos (not_le.mp h3).le h155 (not_le.mp h158).le h154
                · -- right
                  by_cases h159 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h160 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B024.c494_pos (not_le.mp h155).le h2 (not_le.mp h138).le h160
                    · -- right
                      exact CKLaneC2R.Cells.S02.B024.c496_pos (not_le.mp h155).le h2 (not_le.mp h160).le h159
                  · -- right
                    by_cases h161 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c502_pos (not_le.mp h155).le h2 (not_le.mp h159).le h161
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c504_pos (not_le.mp h155).le h2 (not_le.mp h161).le h154
              · -- right
                by_cases h162 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h163 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h164 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c521_pos (not_le.mp h3).le h2 (not_le.mp h154).le h164
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c522_pos (not_le.mp h3).le h2 (not_le.mp h164).le h163
                  · -- right
                    by_cases h165 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c523_pos (not_le.mp h3).le h2 (not_le.mp h163).le h165
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c524_pos (not_le.mp h3).le h2 (not_le.mp h165).le h162
                · -- right
                  by_cases h166 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h167 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h168 : a ≤ ((51/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c703_pos (not_le.mp h3).le h168 (not_le.mp h162).le h167
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c704_pos (not_le.mp h168).le h2 (not_le.mp h162).le h167
                    · -- right
                      by_cases h169 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c707_pos (not_le.mp h3).le h2 (not_le.mp h167).le h169
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c708_pos (not_le.mp h3).le h2 (not_le.mp h169).le h166
                  · -- right
                    by_cases h170 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h171 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c718_pos (not_le.mp h3).le h2 (not_le.mp h166).le h171
                      · -- right
                        by_cases h172 : a ≤ ((51/160 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c781_pos (not_le.mp h3).le h172 (not_le.mp h171).le h170
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c782_pos (not_le.mp h172).le h2 (not_le.mp h171).le h170
                    · -- right
                      by_cases h173 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h174 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c785_pos (not_le.mp h3).le h2 (not_le.mp h170).le h174
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c786_pos (not_le.mp h3).le h2 (not_le.mp h174).le h173
                      · -- right
                        by_cases h175 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          by_cases h176 : z ≤ ((508749/512000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B040.c816_pos (not_le.mp h3).le h2 (not_le.mp h173).le h176
                          · -- right
                            exact CKLaneC2R.Cells.S02.B040.c817_pos (not_le.mp h3).le h2 (not_le.mp h176).le h175
                        · -- right
                          by_cases h177 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B040.c819_pos (not_le.mp h3).le h2 (not_le.mp h175).le h177
                          · -- right
                            by_cases h178 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c840_pos (not_le.mp h3).le h2 (not_le.mp h177).le h178
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c841_pos (not_le.mp h3).le h2 (not_le.mp h178).le hz2
      · -- right
        by_cases h179 : a ≤ ((27/80 : ℚ) : ℝ)
        · -- left
          by_cases h180 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h181 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h182 : a ≤ ((53/160 : ℚ) : ℝ)
              · -- left
                by_cases h183 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h184 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h185 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h186 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h187 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c771_pos (not_le.mp h2).le h182 hz1 h187
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c772_pos (not_le.mp h2).le h182 (not_le.mp h187).le h186
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c603_pos (not_le.mp h2).le h182 (not_le.mp h186).le h185
                    · -- right
                      by_cases h188 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c607_pos (not_le.mp h2).le h182 (not_le.mp h185).le h188
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c609_pos (not_le.mp h2).le h182 (not_le.mp h188).le h184
                  · -- right
                    by_cases h189 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h190 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c615_pos (not_le.mp h2).le h182 (not_le.mp h184).le h190
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c616_pos (not_le.mp h2).le h182 (not_le.mp h190).le h189
                    · -- right
                      by_cases h191 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c619_pos (not_le.mp h2).le h182 (not_le.mp h189).le h191
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c620_pos (not_le.mp h2).le h182 (not_le.mp h191).le h183
                · -- right
                  by_cases h192 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h193 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c304_pos (not_le.mp h2).le h182 (not_le.mp h183).le h193
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c306_pos (not_le.mp h2).le h182 (not_le.mp h193).le h192
                  · -- right
                    by_cases h194 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c312_pos (not_le.mp h2).le h182 (not_le.mp h192).le h194
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c314_pos (not_le.mp h2).le h182 (not_le.mp h194).le h181
              · -- right
                by_cases h195 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h196 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h197 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h198 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h199 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c773_pos (not_le.mp h182).le h179 hz1 h199
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c774_pos (not_le.mp h182).le h179 (not_le.mp h199).le h198
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c604_pos (not_le.mp h182).le h179 (not_le.mp h198).le h197
                    · -- right
                      by_cases h200 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c608_pos (not_le.mp h182).le h179 (not_le.mp h197).le h200
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c610_pos (not_le.mp h182).le h179 (not_le.mp h200).le h196
                  · -- right
                    by_cases h201 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h202 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c617_pos (not_le.mp h182).le h179 (not_le.mp h196).le h202
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c618_pos (not_le.mp h182).le h179 (not_le.mp h202).le h201
                    · -- right
                      by_cases h203 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c621_pos (not_le.mp h182).le h179 (not_le.mp h201).le h203
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c622_pos (not_le.mp h182).le h179 (not_le.mp h203).le h195
                · -- right
                  by_cases h204 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h205 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c305_pos (not_le.mp h182).le h179 (not_le.mp h195).le h205
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c307_pos (not_le.mp h182).le h179 (not_le.mp h205).le h204
                  · -- right
                    by_cases h206 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c313_pos (not_le.mp h182).le h179 (not_le.mp h204).le h206
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c315_pos (not_le.mp h182).le h179 (not_le.mp h206).le h181
            · -- right
              by_cases h207 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h208 : a ≤ ((53/160 : ℚ) : ℝ)
                · -- left
                  by_cases h209 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h210 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c352_pos (not_le.mp h2).le h208 (not_le.mp h181).le h210
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c354_pos (not_le.mp h2).le h208 (not_le.mp h210).le h209
                  · -- right
                    by_cases h211 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c360_pos (not_le.mp h2).le h208 (not_le.mp h209).le h211
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c362_pos (not_le.mp h2).le h208 (not_le.mp h211).le h207
                · -- right
                  by_cases h212 : z ≤ ((5941/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h213 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c353_pos (not_le.mp h208).le h179 (not_le.mp h181).le h213
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c355_pos (not_le.mp h208).le h179 (not_le.mp h213).le h212
                  · -- right
                    by_cases h214 : z ≤ ((2559/6400 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c361_pos (not_le.mp h208).le h179 (not_le.mp h212).le h214
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c363_pos (not_le.mp h208).le h179 (not_le.mp h214).le h207
              · -- right
                by_cases h215 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h216 : a ≤ ((53/160 : ℚ) : ℝ)
                  · -- left
                    by_cases h217 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c366_pos (not_le.mp h2).le h216 (not_le.mp h207).le h217
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c368_pos (not_le.mp h2).le h216 (not_le.mp h217).le h215
                  · -- right
                    by_cases h218 : z ≤ ((14621/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c367_pos (not_le.mp h216).le h179 (not_le.mp h207).le h218
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c369_pos (not_le.mp h216).le h179 (not_le.mp h218).le h215
                · -- right
                  by_cases h219 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c27_pos (not_le.mp h2).le h179 (not_le.mp h215).le h219
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c28_pos (not_le.mp h2).le h179 (not_le.mp h219).le h180
          · -- right
            by_cases h220 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h221 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h222 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h223 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c146_pos (not_le.mp h2).le h179 (not_le.mp h180).le h223
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c147_pos (not_le.mp h2).le h179 (not_le.mp h223).le h222
                · -- right
                  by_cases h224 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c150_pos (not_le.mp h2).le h179 (not_le.mp h222).le h224
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c151_pos (not_le.mp h2).le h179 (not_le.mp h224).le h221
              · -- right
                by_cases h225 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h226 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c154_pos (not_le.mp h2).le h179 (not_le.mp h221).le h226
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c155_pos (not_le.mp h2).le h179 (not_le.mp h226).le h225
                · -- right
                  by_cases h227 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c158_pos (not_le.mp h2).le h179 (not_le.mp h225).le h227
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c159_pos (not_le.mp h2).le h179 (not_le.mp h227).le h220
            · -- right
              by_cases h228 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h229 : a ≤ ((53/160 : ℚ) : ℝ)
                · -- left
                  by_cases h230 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h231 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c505_pos (not_le.mp h2).le h229 (not_le.mp h220).le h231
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c507_pos (not_le.mp h2).le h229 (not_le.mp h231).le h230
                  · -- right
                    by_cases h232 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c509_pos (not_le.mp h2).le h229 (not_le.mp h230).le h232
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c511_pos (not_le.mp h2).le h229 (not_le.mp h232).le h228
                · -- right
                  by_cases h233 : z ≤ ((2649/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h234 : z ≤ ((25577/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c506_pos (not_le.mp h229).le h179 (not_le.mp h220).le h234
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c508_pos (not_le.mp h229).le h179 (not_le.mp h234).le h233
                  · -- right
                    by_cases h235 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c510_pos (not_le.mp h229).le h179 (not_le.mp h233).le h235
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c512_pos (not_le.mp h229).le h179 (not_le.mp h235).le h228
              · -- right
                by_cases h236 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h237 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h238 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c525_pos (not_le.mp h2).le h179 (not_le.mp h228).le h238
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c526_pos (not_le.mp h2).le h179 (not_le.mp h238).le h237
                  · -- right
                    by_cases h239 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c529_pos (not_le.mp h2).le h179 (not_le.mp h237).le h239
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c530_pos (not_le.mp h2).le h179 (not_le.mp h239).le h236
                · -- right
                  by_cases h240 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h241 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h242 : a ≤ ((53/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c709_pos (not_le.mp h2).le h242 (not_le.mp h236).le h241
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c710_pos (not_le.mp h242).le h179 (not_le.mp h236).le h241
                    · -- right
                      by_cases h243 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c711_pos (not_le.mp h2).le h179 (not_le.mp h241).le h243
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c712_pos (not_le.mp h2).le h179 (not_le.mp h243).le h240
                  · -- right
                    by_cases h244 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h245 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c719_pos (not_le.mp h2).le h179 (not_le.mp h240).le h245
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c720_pos (not_le.mp h2).le h179 (not_le.mp h245).le h244
                    · -- right
                      by_cases h246 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h247 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c787_pos (not_le.mp h2).le h179 (not_le.mp h244).le h247
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c788_pos (not_le.mp h2).le h179 (not_le.mp h247).le h246
                      · -- right
                        by_cases h248 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c799_pos (not_le.mp h2).le h179 (not_le.mp h246).le h248
                        · -- right
                          by_cases h249 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c820_pos (not_le.mp h2).le h179 (not_le.mp h248).le h249
                          · -- right
                            by_cases h250 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c842_pos (not_le.mp h2).le h179 (not_le.mp h249).le h250
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c843_pos (not_le.mp h2).le h179 (not_le.mp h250).le hz2
        · -- right
          by_cases h251 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h252 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h253 : a ≤ ((11/32 : ℚ) : ℝ)
              · -- left
                by_cases h254 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h255 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h256 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h257 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h258 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c775_pos (not_le.mp h179).le h253 hz1 h258
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c776_pos (not_le.mp h179).le h253 (not_le.mp h258).le h257
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c605_pos (not_le.mp h179).le h253 (not_le.mp h257).le h256
                    · -- right
                      by_cases h259 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c611_pos (not_le.mp h179).le h253 (not_le.mp h256).le h259
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c613_pos (not_le.mp h179).le h253 (not_le.mp h259).le h255
                  · -- right
                    by_cases h260 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h261 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c623_pos (not_le.mp h179).le h253 (not_le.mp h255).le h261
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c625_pos (not_le.mp h179).le h253 (not_le.mp h261).le h260
                    · -- right
                      by_cases h262 : z ≤ ((2379/12800 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c627_pos (not_le.mp h179).le h253 (not_le.mp h260).le h262
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c628_pos (not_le.mp h179).le h253 (not_le.mp h262).le h254
                · -- right
                  by_cases h263 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h264 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c308_pos (not_le.mp h179).le h253 (not_le.mp h254).le h264
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c310_pos (not_le.mp h179).le h253 (not_le.mp h264).le h263
                  · -- right
                    by_cases h265 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c316_pos (not_le.mp h179).le h253 (not_le.mp h263).le h265
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c318_pos (not_le.mp h179).le h253 (not_le.mp h265).le h252
              · -- right
                by_cases h266 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h267 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h268 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h269 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        by_cases h270 : z ≤ ((11921/128000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B038.c777_pos (not_le.mp h253).le h1 hz1 h270
                        · -- right
                          exact CKLaneC2R.Cells.S02.B038.c778_pos (not_le.mp h253).le h1 (not_le.mp h270).le h269
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c606_pos (not_le.mp h253).le h1 (not_le.mp h269).le h268
                    · -- right
                      by_cases h271 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B030.c612_pos (not_le.mp h253).le h1 (not_le.mp h268).le h271
                      · -- right
                        exact CKLaneC2R.Cells.S02.B030.c614_pos (not_le.mp h253).le h1 (not_le.mp h271).le h267
                  · -- right
                    by_cases h272 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h273 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c624_pos (not_le.mp h253).le h1 (not_le.mp h267).le h273
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c626_pos (not_le.mp h253).le h1 (not_le.mp h273).le h272
                    · -- right
                      exact CKLaneC2R.Cells.S02.B014.c290_pos (not_le.mp h253).le h1 (not_le.mp h272).le h266
                · -- right
                  by_cases h274 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h275 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c309_pos (not_le.mp h253).le h1 (not_le.mp h266).le h275
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c311_pos (not_le.mp h253).le h1 (not_le.mp h275).le h274
                  · -- right
                    by_cases h276 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B015.c317_pos (not_le.mp h253).le h1 (not_le.mp h274).le h276
                    · -- right
                      exact CKLaneC2R.Cells.S02.B015.c319_pos (not_le.mp h253).le h1 (not_le.mp h276).le h252
            · -- right
              by_cases h277 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h278 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h279 : a ≤ ((11/32 : ℚ) : ℝ)
                  · -- left
                    by_cases h280 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c356_pos (not_le.mp h179).le h279 (not_le.mp h252).le h280
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c358_pos (not_le.mp h179).le h279 (not_le.mp h280).le h278
                  · -- right
                    by_cases h281 : z ≤ ((10969/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B017.c357_pos (not_le.mp h279).le h1 (not_le.mp h252).le h281
                    · -- right
                      exact CKLaneC2R.Cells.S02.B017.c359_pos (not_le.mp h279).le h1 (not_le.mp h281).le h278
                · -- right
                  by_cases h282 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h283 : a ≤ ((11/32 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c364_pos (not_le.mp h179).le h283 (not_le.mp h278).le h282
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c365_pos (not_le.mp h283).le h1 (not_le.mp h278).le h282
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c24_pos (not_le.mp h179).le h1 (not_le.mp h282).le h277
              · -- right
                by_cases h284 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h285 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c25_pos (not_le.mp h179).le h1 (not_le.mp h277).le h285
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c26_pos (not_le.mp h179).le h1 (not_le.mp h285).le h284
                · -- right
                  by_cases h286 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c29_pos (not_le.mp h179).le h1 (not_le.mp h284).le h286
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c30_pos (not_le.mp h179).le h1 (not_le.mp h286).le h251
          · -- right
            by_cases h287 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h288 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h289 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h290 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c148_pos (not_le.mp h179).le h1 (not_le.mp h251).le h290
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c149_pos (not_le.mp h179).le h1 (not_le.mp h290).le h289
                · -- right
                  by_cases h291 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c152_pos (not_le.mp h179).le h1 (not_le.mp h289).le h291
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c153_pos (not_le.mp h179).le h1 (not_le.mp h291).le h288
              · -- right
                by_cases h292 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h293 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c156_pos (not_le.mp h179).le h1 (not_le.mp h288).le h293
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c157_pos (not_le.mp h179).le h1 (not_le.mp h293).le h292
                · -- right
                  by_cases h294 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c160_pos (not_le.mp h179).le h1 (not_le.mp h292).le h294
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c161_pos (not_le.mp h179).le h1 (not_le.mp h294).le h287
            · -- right
              by_cases h295 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h296 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h297 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c228_pos (not_le.mp h179).le h1 (not_le.mp h287).le h297
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c229_pos (not_le.mp h179).le h1 (not_le.mp h297).le h296
                · -- right
                  by_cases h298 : a ≤ ((11/32 : ℚ) : ℝ)
                  · -- left
                    by_cases h299 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c513_pos (not_le.mp h179).le h298 (not_le.mp h296).le h299
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c515_pos (not_le.mp h179).le h298 (not_le.mp h299).le h295
                  · -- right
                    by_cases h300 : z ≤ ((27403/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c514_pos (not_le.mp h298).le h1 (not_le.mp h296).le h300
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c516_pos (not_le.mp h298).le h1 (not_le.mp h300).le h295
              · -- right
                by_cases h301 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h302 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h303 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c527_pos (not_le.mp h179).le h1 (not_le.mp h295).le h303
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c528_pos (not_le.mp h179).le h1 (not_le.mp h303).le h302
                  · -- right
                    by_cases h304 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c531_pos (not_le.mp h179).le h1 (not_le.mp h302).le h304
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c532_pos (not_le.mp h179).le h1 (not_le.mp h304).le h301
                · -- right
                  by_cases h305 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h306 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c555_pos (not_le.mp h179).le h1 (not_le.mp h301).le h306
                    · -- right
                      by_cases h307 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c713_pos (not_le.mp h179).le h1 (not_le.mp h306).le h307
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c714_pos (not_le.mp h179).le h1 (not_le.mp h307).le h305
                  · -- right
                    by_cases h308 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h309 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c721_pos (not_le.mp h179).le h1 (not_le.mp h305).le h309
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c722_pos (not_le.mp h179).le h1 (not_le.mp h309).le h308
                    · -- right
                      by_cases h310 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h311 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c789_pos (not_le.mp h179).le h1 (not_le.mp h308).le h311
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c790_pos (not_le.mp h179).le h1 (not_le.mp h311).le h310
                      · -- right
                        by_cases h312 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c800_pos (not_le.mp h179).le h1 (not_le.mp h310).le h312
                        · -- right
                          by_cases h313 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c821_pos (not_le.mp h179).le h1 (not_le.mp h312).le h313
                          · -- right
                            by_cases h314 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c844_pos (not_le.mp h179).le h1 (not_le.mp h313).le h314
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c845_pos (not_le.mp h179).le h1 (not_le.mp h314).le hz2
    · -- right
      by_cases h315 : a ≤ ((3/8 : ℚ) : ℝ)
      · -- left
        by_cases h316 : a ≤ ((29/80 : ℚ) : ℝ)
        · -- left
          by_cases h317 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h318 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h319 : a ≤ ((57/160 : ℚ) : ℝ)
              · -- left
                by_cases h320 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h321 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h322 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h323 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c635_pos (not_le.mp h1).le h319 hz1 h323
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c637_pos (not_le.mp h1).le h319 (not_le.mp h323).le h322
                    · -- right
                      by_cases h324 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c643_pos (not_le.mp h1).le h319 (not_le.mp h322).le h324
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c645_pos (not_le.mp h1).le h319 (not_le.mp h324).le h321
                  · -- right
                    by_cases h325 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h326 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c667_pos (not_le.mp h1).le h319 (not_le.mp h321).le h326
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c669_pos (not_le.mp h1).le h319 (not_le.mp h326).le h325
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c370_pos (not_le.mp h1).le h319 (not_le.mp h325).le h320
                · -- right
                  by_cases h327 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h328 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c381_pos (not_le.mp h1).le h319 (not_le.mp h320).le h328
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c383_pos (not_le.mp h1).le h319 (not_le.mp h328).le h327
                  · -- right
                    by_cases h329 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c389_pos (not_le.mp h1).le h319 (not_le.mp h327).le h329
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c391_pos (not_le.mp h1).le h319 (not_le.mp h329).le h318
              · -- right
                by_cases h330 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h331 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h332 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h333 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c636_pos (not_le.mp h319).le h316 hz1 h333
                      · -- right
                        exact CKLaneC2R.Cells.S02.B031.c638_pos (not_le.mp h319).le h316 (not_le.mp h333).le h332
                    · -- right
                      by_cases h334 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c644_pos (not_le.mp h319).le h316 (not_le.mp h332).le h334
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c646_pos (not_le.mp h319).le h316 (not_le.mp h334).le h331
                  · -- right
                    by_cases h335 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h336 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c668_pos (not_le.mp h319).le h316 (not_le.mp h331).le h336
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c670_pos (not_le.mp h319).le h316 (not_le.mp h336).le h335
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c371_pos (not_le.mp h319).le h316 (not_le.mp h335).le h330
                · -- right
                  by_cases h337 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h338 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c382_pos (not_le.mp h319).le h316 (not_le.mp h330).le h338
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c384_pos (not_le.mp h319).le h316 (not_le.mp h338).le h337
                  · -- right
                    by_cases h339 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c390_pos (not_le.mp h319).le h316 (not_le.mp h337).le h339
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c392_pos (not_le.mp h319).le h316 (not_le.mp h339).le h318
            · -- right
              by_cases h340 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h341 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h342 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h343 : a ≤ ((57/160 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c407_pos (not_le.mp h1).le h343 (not_le.mp h318).le h342
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c408_pos (not_le.mp h343).le h316 (not_le.mp h318).le h342
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c34_pos (not_le.mp h1).le h316 (not_le.mp h342).le h341
                · -- right
                  by_cases h344 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c37_pos (not_le.mp h1).le h316 (not_le.mp h341).le h344
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c38_pos (not_le.mp h1).le h316 (not_le.mp h344).le h340
              · -- right
                by_cases h345 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h346 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c49_pos (not_le.mp h1).le h316 (not_le.mp h340).le h346
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c50_pos (not_le.mp h1).le h316 (not_le.mp h346).le h345
                · -- right
                  by_cases h347 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c53_pos (not_le.mp h1).le h316 (not_le.mp h345).le h347
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c54_pos (not_le.mp h1).le h316 (not_le.mp h347).le h317
          · -- right
            by_cases h348 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h349 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h350 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h351 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c162_pos (not_le.mp h1).le h316 (not_le.mp h317).le h351
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c163_pos (not_le.mp h1).le h316 (not_le.mp h351).le h350
                · -- right
                  by_cases h352 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c166_pos (not_le.mp h1).le h316 (not_le.mp h350).le h352
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c167_pos (not_le.mp h1).le h316 (not_le.mp h352).le h349
              · -- right
                by_cases h353 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h354 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c178_pos (not_le.mp h1).le h316 (not_le.mp h349).le h354
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c179_pos (not_le.mp h1).le h316 (not_le.mp h354).le h353
                · -- right
                  by_cases h355 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c182_pos (not_le.mp h1).le h316 (not_le.mp h353).le h355
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c183_pos (not_le.mp h1).le h316 (not_le.mp h355).le h348
            · -- right
              by_cases h356 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h357 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h358 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c230_pos (not_le.mp h1).le h316 (not_le.mp h348).le h358
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c231_pos (not_le.mp h1).le h316 (not_le.mp h358).le h357
                · -- right
                  by_cases h359 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c238_pos (not_le.mp h1).le h316 (not_le.mp h357).le h359
                  · -- right
                    by_cases h360 : z ≤ ((55719/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B025.c517_pos (not_le.mp h1).le h316 (not_le.mp h359).le h360
                    · -- right
                      exact CKLaneC2R.Cells.S02.B025.c518_pos (not_le.mp h1).le h316 (not_le.mp h360).le h356
              · -- right
                by_cases h361 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h362 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h363 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c533_pos (not_le.mp h1).le h316 (not_le.mp h356).le h363
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c534_pos (not_le.mp h1).le h316 (not_le.mp h363).le h362
                  · -- right
                    by_cases h364 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c537_pos (not_le.mp h1).le h316 (not_le.mp h362).le h364
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c538_pos (not_le.mp h1).le h316 (not_le.mp h364).le h361
                · -- right
                  by_cases h365 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h366 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c556_pos (not_le.mp h1).le h316 (not_le.mp h361).le h366
                    · -- right
                      by_cases h367 : z ≤ ((123307/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B035.c715_pos (not_le.mp h1).le h316 (not_le.mp h366).le h367
                      · -- right
                        exact CKLaneC2R.Cells.S02.B035.c716_pos (not_le.mp h1).le h316 (not_le.mp h367).le h365
                  · -- right
                    by_cases h368 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h369 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c723_pos (not_le.mp h1).le h316 (not_le.mp h365).le h369
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c724_pos (not_le.mp h1).le h316 (not_le.mp h369).le h368
                    · -- right
                      by_cases h370 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h371 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c791_pos (not_le.mp h1).le h316 (not_le.mp h368).le h371
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c792_pos (not_le.mp h1).le h316 (not_le.mp h371).le h370
                      · -- right
                        by_cases h372 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c801_pos (not_le.mp h1).le h316 (not_le.mp h370).le h372
                        · -- right
                          by_cases h373 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c822_pos (not_le.mp h1).le h316 (not_le.mp h372).le h373
                          · -- right
                            by_cases h374 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c846_pos (not_le.mp h1).le h316 (not_le.mp h373).le h374
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c847_pos (not_le.mp h1).le h316 (not_le.mp h374).le hz2
        · -- right
          by_cases h375 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h376 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h377 : a ≤ ((59/160 : ℚ) : ℝ)
              · -- left
                by_cases h378 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h379 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h380 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h381 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B031.c639_pos (not_le.mp h316).le h377 hz1 h381
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c641_pos (not_le.mp h316).le h377 (not_le.mp h381).le h380
                    · -- right
                      by_cases h382 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c647_pos (not_le.mp h316).le h377 (not_le.mp h380).le h382
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c649_pos (not_le.mp h316).le h377 (not_le.mp h382).le h379
                  · -- right
                    by_cases h383 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h384 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c671_pos (not_le.mp h316).le h377 (not_le.mp h379).le h384
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c673_pos (not_le.mp h316).le h377 (not_le.mp h384).le h383
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c372_pos (not_le.mp h316).le h377 (not_le.mp h383).le h378
                · -- right
                  by_cases h385 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h386 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c385_pos (not_le.mp h316).le h377 (not_le.mp h378).le h386
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c387_pos (not_le.mp h316).le h377 (not_le.mp h386).le h385
                  · -- right
                    by_cases h387 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c393_pos (not_le.mp h316).le h377 (not_le.mp h385).le h387
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c395_pos (not_le.mp h316).le h377 (not_le.mp h387).le h376
              · -- right
                by_cases h388 : z ≤ ((1601/8000 : ℚ) : ℝ)
                · -- left
                  by_cases h389 : z ≤ ((2289/16000 : ℚ) : ℝ)
                  · -- left
                    by_cases h390 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h391 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c640_pos (not_le.mp h377).le h315 hz1 h391
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c642_pos (not_le.mp h377).le h315 (not_le.mp h391).le h390
                    · -- right
                      by_cases h392 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c648_pos (not_le.mp h377).le h315 (not_le.mp h390).le h392
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c650_pos (not_le.mp h377).le h315 (not_le.mp h392).le h389
                  · -- right
                    by_cases h393 : z ≤ ((5491/32000 : ℚ) : ℝ)
                    · -- left
                      by_cases h394 : z ≤ ((10069/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c672_pos (not_le.mp h377).le h315 (not_le.mp h389).le h394
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c674_pos (not_le.mp h377).le h315 (not_le.mp h394).le h393
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c373_pos (not_le.mp h377).le h315 (not_le.mp h393).le h388
                · -- right
                  by_cases h395 : z ≤ ((823/3200 : ℚ) : ℝ)
                  · -- left
                    by_cases h396 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c386_pos (not_le.mp h377).le h315 (not_le.mp h388).le h396
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c388_pos (not_le.mp h377).le h315 (not_le.mp h396).le h395
                  · -- right
                    by_cases h397 : z ≤ ((9143/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c394_pos (not_le.mp h377).le h315 (not_le.mp h395).le h397
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c396_pos (not_le.mp h377).le h315 (not_le.mp h397).le h376
            · -- right
              by_cases h398 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h399 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h400 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c35_pos (not_le.mp h316).le h315 (not_le.mp h376).le h400
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c36_pos (not_le.mp h316).le h315 (not_le.mp h400).le h399
                · -- right
                  by_cases h401 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c39_pos (not_le.mp h316).le h315 (not_le.mp h399).le h401
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c40_pos (not_le.mp h316).le h315 (not_le.mp h401).le h398
              · -- right
                by_cases h402 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h403 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c51_pos (not_le.mp h316).le h315 (not_le.mp h398).le h403
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c52_pos (not_le.mp h316).le h315 (not_le.mp h403).le h402
                · -- right
                  by_cases h404 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c55_pos (not_le.mp h316).le h315 (not_le.mp h402).le h404
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c56_pos (not_le.mp h316).le h315 (not_le.mp h404).le h375
          · -- right
            by_cases h405 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h406 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h407 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h408 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c164_pos (not_le.mp h316).le h315 (not_le.mp h375).le h408
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c165_pos (not_le.mp h316).le h315 (not_le.mp h408).le h407
                · -- right
                  by_cases h409 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c168_pos (not_le.mp h316).le h315 (not_le.mp h407).le h409
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c169_pos (not_le.mp h316).le h315 (not_le.mp h409).le h406
              · -- right
                by_cases h410 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h411 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c180_pos (not_le.mp h316).le h315 (not_le.mp h406).le h411
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c181_pos (not_le.mp h316).le h315 (not_le.mp h411).le h410
                · -- right
                  by_cases h412 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c184_pos (not_le.mp h316).le h315 (not_le.mp h410).le h412
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c185_pos (not_le.mp h316).le h315 (not_le.mp h412).le h405
            · -- right
              by_cases h413 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h414 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h415 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c232_pos (not_le.mp h316).le h315 (not_le.mp h405).le h415
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c233_pos (not_le.mp h316).le h315 (not_le.mp h415).le h414
                · -- right
                  by_cases h416 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c239_pos (not_le.mp h316).le h315 (not_le.mp h414).le h416
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c240_pos (not_le.mp h316).le h315 (not_le.mp h416).le h413
              · -- right
                by_cases h417 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h418 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h419 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c535_pos (not_le.mp h316).le h315 (not_le.mp h413).le h419
                    · -- right
                      exact CKLaneC2R.Cells.S02.B026.c536_pos (not_le.mp h316).le h315 (not_le.mp h419).le h418
                  · -- right
                    by_cases h420 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B026.c539_pos (not_le.mp h316).le h315 (not_le.mp h418).le h420
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c540_pos (not_le.mp h316).le h315 (not_le.mp h420).le h417
                · -- right
                  by_cases h421 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h422 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c557_pos (not_le.mp h316).le h315 (not_le.mp h417).le h422
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c558_pos (not_le.mp h316).le h315 (not_le.mp h422).le h421
                  · -- right
                    by_cases h423 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h424 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c725_pos (not_le.mp h316).le h315 (not_le.mp h421).le h424
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c726_pos (not_le.mp h316).le h315 (not_le.mp h424).le h423
                    · -- right
                      by_cases h425 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h426 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c793_pos (not_le.mp h316).le h315 (not_le.mp h423).le h426
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c794_pos (not_le.mp h316).le h315 (not_le.mp h426).le h425
                      · -- right
                        by_cases h427 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c802_pos (not_le.mp h316).le h315 (not_le.mp h425).le h427
                        · -- right
                          by_cases h428 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c823_pos (not_le.mp h316).le h315 (not_le.mp h427).le h428
                          · -- right
                            by_cases h429 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c848_pos (not_le.mp h316).le h315 (not_le.mp h428).le h429
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c849_pos (not_le.mp h316).le h315 (not_le.mp h429).le hz2
      · -- right
        by_cases h430 : a ≤ ((31/80 : ℚ) : ℝ)
        · -- left
          by_cases h431 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h432 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h433 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h434 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h435 : a ≤ ((61/160 : ℚ) : ℝ)
                  · -- left
                    by_cases h436 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h437 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c651_pos (not_le.mp h315).le h435 hz1 h437
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c653_pos (not_le.mp h315).le h435 (not_le.mp h437).le h436
                    · -- right
                      by_cases h438 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c659_pos (not_le.mp h315).le h435 (not_le.mp h436).le h438
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c661_pos (not_le.mp h315).le h435 (not_le.mp h438).le h434
                  · -- right
                    by_cases h439 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h440 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c652_pos (not_le.mp h435).le h430 hz1 h440
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c654_pos (not_le.mp h435).le h430 (not_le.mp h440).le h439
                    · -- right
                      by_cases h441 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c660_pos (not_le.mp h435).le h430 (not_le.mp h439).le h441
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c662_pos (not_le.mp h435).le h430 (not_le.mp h441).le h434
                · -- right
                  by_cases h442 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h443 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h444 : a ≤ ((61/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c675_pos (not_le.mp h315).le h444 (not_le.mp h434).le h443
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c676_pos (not_le.mp h444).le h430 (not_le.mp h434).le h443
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c374_pos (not_le.mp h315).le h430 (not_le.mp h443).le h442
                  · -- right
                    by_cases h445 : a ≤ ((61/160 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c377_pos (not_le.mp h315).le h445 (not_le.mp h442).le h433
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c378_pos (not_le.mp h445).le h430 (not_le.mp h442).le h433
              · -- right
                by_cases h446 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h447 : a ≤ ((61/160 : ℚ) : ℝ)
                  · -- left
                    by_cases h448 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c397_pos (not_le.mp h315).le h447 (not_le.mp h433).le h448
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c399_pos (not_le.mp h315).le h447 (not_le.mp h448).le h446
                  · -- right
                    by_cases h449 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B019.c398_pos (not_le.mp h447).le h430 (not_le.mp h433).le h449
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c400_pos (not_le.mp h447).le h430 (not_le.mp h449).le h446
                · -- right
                  by_cases h450 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h451 : a ≤ ((61/160 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c405_pos (not_le.mp h315).le h451 (not_le.mp h446).le h450
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c406_pos (not_le.mp h451).le h430 (not_le.mp h446).le h450
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c31_pos (not_le.mp h315).le h430 (not_le.mp h450).le h432
            · -- right
              by_cases h452 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h453 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h454 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c41_pos (not_le.mp h315).le h430 (not_le.mp h432).le h454
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c42_pos (not_le.mp h315).le h430 (not_le.mp h454).le h453
                · -- right
                  by_cases h455 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c45_pos (not_le.mp h315).le h430 (not_le.mp h453).le h455
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c46_pos (not_le.mp h315).le h430 (not_le.mp h455).le h452
              · -- right
                by_cases h456 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h457 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c57_pos (not_le.mp h315).le h430 (not_le.mp h452).le h457
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c58_pos (not_le.mp h315).le h430 (not_le.mp h457).le h456
                · -- right
                  by_cases h458 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c61_pos (not_le.mp h315).le h430 (not_le.mp h456).le h458
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c62_pos (not_le.mp h315).le h430 (not_le.mp h458).le h431
          · -- right
            by_cases h459 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h460 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h461 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h462 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c170_pos (not_le.mp h315).le h430 (not_le.mp h431).le h462
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c171_pos (not_le.mp h315).le h430 (not_le.mp h462).le h461
                · -- right
                  by_cases h463 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c174_pos (not_le.mp h315).le h430 (not_le.mp h461).le h463
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c175_pos (not_le.mp h315).le h430 (not_le.mp h463).le h460
              · -- right
                by_cases h464 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h465 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c186_pos (not_le.mp h315).le h430 (not_le.mp h460).le h465
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c187_pos (not_le.mp h315).le h430 (not_le.mp h465).le h464
                · -- right
                  by_cases h466 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c190_pos (not_le.mp h315).le h430 (not_le.mp h464).le h466
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c191_pos (not_le.mp h315).le h430 (not_le.mp h466).le h459
            · -- right
              by_cases h467 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h468 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h469 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c234_pos (not_le.mp h315).le h430 (not_le.mp h459).le h469
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c235_pos (not_le.mp h315).le h430 (not_le.mp h469).le h468
                · -- right
                  by_cases h470 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c241_pos (not_le.mp h315).le h430 (not_le.mp h468).le h470
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c243_pos (not_le.mp h315).le h430 (not_le.mp h470).le h467
              · -- right
                by_cases h471 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h472 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h473 : z ≤ ((11509/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c541_pos (not_le.mp h315).le h430 (not_le.mp h467).le h473
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c542_pos (not_le.mp h315).le h430 (not_le.mp h473).le h472
                  · -- right
                    by_cases h474 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c543_pos (not_le.mp h315).le h430 (not_le.mp h472).le h474
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c544_pos (not_le.mp h315).le h430 (not_le.mp h474).le h471
                · -- right
                  by_cases h475 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h476 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c559_pos (not_le.mp h315).le h430 (not_le.mp h471).le h476
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c561_pos (not_le.mp h315).le h430 (not_le.mp h476).le h475
                  · -- right
                    by_cases h477 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h478 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c727_pos (not_le.mp h315).le h430 (not_le.mp h475).le h478
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c728_pos (not_le.mp h315).le h430 (not_le.mp h478).le h477
                    · -- right
                      by_cases h479 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h480 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c795_pos (not_le.mp h315).le h430 (not_le.mp h477).le h480
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c796_pos (not_le.mp h315).le h430 (not_le.mp h480).le h479
                      · -- right
                        by_cases h481 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c803_pos (not_le.mp h315).le h430 (not_le.mp h479).le h481
                        · -- right
                          by_cases h482 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c824_pos (not_le.mp h315).le h430 (not_le.mp h481).le h482
                          · -- right
                            by_cases h483 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c850_pos (not_le.mp h315).le h430 (not_le.mp h482).le h483
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c851_pos (not_le.mp h315).le h430 (not_le.mp h483).le hz2
        · -- right
          by_cases h484 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h485 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h486 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h487 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h488 : a ≤ ((63/160 : ℚ) : ℝ)
                  · -- left
                    by_cases h489 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h490 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c655_pos (not_le.mp h430).le h488 hz1 h490
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c657_pos (not_le.mp h430).le h488 (not_le.mp h490).le h489
                    · -- right
                      by_cases h491 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c663_pos (not_le.mp h430).le h488 (not_le.mp h489).le h491
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c665_pos (not_le.mp h430).le h488 (not_le.mp h491).le h487
                  · -- right
                    by_cases h492 : z ≤ ((733/6400 : ℚ) : ℝ)
                    · -- left
                      by_cases h493 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B032.c656_pos (not_le.mp h488).le h0 hz1 h493
                      · -- right
                        exact CKLaneC2R.Cells.S02.B032.c658_pos (not_le.mp h488).le h0 (not_le.mp h493).le h492
                    · -- right
                      by_cases h494 : z ≤ ((8243/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c664_pos (not_le.mp h488).le h0 (not_le.mp h492).le h494
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c666_pos (not_le.mp h488).le h0 (not_le.mp h494).le h487
                · -- right
                  by_cases h495 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h496 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c375_pos (not_le.mp h430).le h0 (not_le.mp h487).le h496
                    · -- right
                      exact CKLaneC2R.Cells.S02.B018.c376_pos (not_le.mp h430).le h0 (not_le.mp h496).le h495
                  · -- right
                    by_cases h497 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B018.c379_pos (not_le.mp h430).le h0 (not_le.mp h495).le h497
                    · -- right
                      exact CKLaneC2R.Cells.S02.B019.c380_pos (not_le.mp h430).le h0 (not_le.mp h497).le h486
              · -- right
                by_cases h498 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h499 : a ≤ ((63/160 : ℚ) : ℝ)
                  · -- left
                    by_cases h500 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c401_pos (not_le.mp h430).le h499 (not_le.mp h486).le h500
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c403_pos (not_le.mp h430).le h499 (not_le.mp h500).le h498
                  · -- right
                    by_cases h501 : z ≤ ((7317/32000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c402_pos (not_le.mp h499).le h0 (not_le.mp h486).le h501
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c404_pos (not_le.mp h499).le h0 (not_le.mp h501).le h498
                · -- right
                  by_cases h502 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B001.c32_pos (not_le.mp h430).le h0 (not_le.mp h498).le h502
                  · -- right
                    exact CKLaneC2R.Cells.S02.B001.c33_pos (not_le.mp h430).le h0 (not_le.mp h502).le h485
            · -- right
              by_cases h503 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h504 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h505 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c43_pos (not_le.mp h430).le h0 (not_le.mp h485).le h505
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c44_pos (not_le.mp h430).le h0 (not_le.mp h505).le h504
                · -- right
                  by_cases h506 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c47_pos (not_le.mp h430).le h0 (not_le.mp h504).le h506
                  · -- right
                    exact CKLaneC2R.Cells.S02.B002.c48_pos (not_le.mp h430).le h0 (not_le.mp h506).le h503
              · -- right
                by_cases h507 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h508 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B002.c59_pos (not_le.mp h430).le h0 (not_le.mp h503).le h508
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c60_pos (not_le.mp h430).le h0 (not_le.mp h508).le h507
                · -- right
                  by_cases h509 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c63_pos (not_le.mp h430).le h0 (not_le.mp h507).le h509
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c64_pos (not_le.mp h430).le h0 (not_le.mp h509).le h484
          · -- right
            by_cases h510 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h511 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h512 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h513 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c172_pos (not_le.mp h430).le h0 (not_le.mp h484).le h513
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c173_pos (not_le.mp h430).le h0 (not_le.mp h513).le h512
                · -- right
                  by_cases h514 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B008.c176_pos (not_le.mp h430).le h0 (not_le.mp h512).le h514
                  · -- right
                    exact CKLaneC2R.Cells.S02.B008.c177_pos (not_le.mp h430).le h0 (not_le.mp h514).le h511
              · -- right
                by_cases h515 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h516 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c188_pos (not_le.mp h430).le h0 (not_le.mp h511).le h516
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c189_pos (not_le.mp h430).le h0 (not_le.mp h516).le h515
                · -- right
                  by_cases h517 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c192_pos (not_le.mp h430).le h0 (not_le.mp h515).le h517
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c193_pos (not_le.mp h430).le h0 (not_le.mp h517).le h510
            · -- right
              by_cases h518 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h519 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h520 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c236_pos (not_le.mp h430).le h0 (not_le.mp h510).le h520
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c237_pos (not_le.mp h430).le h0 (not_le.mp h520).le h519
                · -- right
                  by_cases h521 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c242_pos (not_le.mp h430).le h0 (not_le.mp h519).le h521
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c244_pos (not_le.mp h430).le h0 (not_le.mp h521).le h518
              · -- right
                by_cases h522 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h523 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c277_pos (not_le.mp h430).le h0 (not_le.mp h518).le h523
                  · -- right
                    by_cases h524 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c545_pos (not_le.mp h430).le h0 (not_le.mp h523).le h524
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c546_pos (not_le.mp h430).le h0 (not_le.mp h524).le h522
                · -- right
                  by_cases h525 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h526 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c560_pos (not_le.mp h430).le h0 (not_le.mp h522).le h526
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c562_pos (not_le.mp h430).le h0 (not_le.mp h526).le h525
                  · -- right
                    by_cases h527 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h528 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c729_pos (not_le.mp h430).le h0 (not_le.mp h525).le h528
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c730_pos (not_le.mp h430).le h0 (not_le.mp h528).le h527
                    · -- right
                      by_cases h529 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        by_cases h530 : z ≤ ((50601/51200 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B039.c797_pos (not_le.mp h430).le h0 (not_le.mp h527).le h530
                        · -- right
                          exact CKLaneC2R.Cells.S02.B039.c798_pos (not_le.mp h430).le h0 (not_le.mp h530).le h529
                      · -- right
                        by_cases h531 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c804_pos (not_le.mp h430).le h0 (not_le.mp h529).le h531
                        · -- right
                          by_cases h532 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c825_pos (not_le.mp h430).le h0 (not_le.mp h531).le h532
                          · -- right
                            by_cases h533 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c852_pos (not_le.mp h430).le h0 (not_le.mp h532).le h533
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c853_pos (not_le.mp h430).le h0 (not_le.mp h533).le hz2
  · -- right
    by_cases h534 : a ≤ ((9/20 : ℚ) : ℝ)
    · -- left
      by_cases h535 : a ≤ ((17/40 : ℚ) : ℝ)
      · -- left
        by_cases h536 : a ≤ ((33/80 : ℚ) : ℝ)
        · -- left
          by_cases h537 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h538 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h539 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h540 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h541 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h542 : a ≤ ((13/32 : ℚ) : ℝ)
                    · -- left
                      by_cases h543 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c677_pos (not_le.mp h0).le h542 hz1 h543
                      · -- right
                        exact CKLaneC2R.Cells.S02.B033.c679_pos (not_le.mp h0).le h542 (not_le.mp h543).le h541
                    · -- right
                      by_cases h544 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B033.c678_pos (not_le.mp h542).le h536 hz1 h544
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c680_pos (not_le.mp h542).le h536 (not_le.mp h544).le h541
                  · -- right
                    by_cases h545 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h546 : a ≤ ((13/32 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c685_pos (not_le.mp h0).le h546 (not_le.mp h541).le h545
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c686_pos (not_le.mp h546).le h536 (not_le.mp h541).le h545
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c409_pos (not_le.mp h0).le h536 (not_le.mp h545).le h540
                · -- right
                  by_cases h547 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h548 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c417_pos (not_le.mp h0).le h536 (not_le.mp h540).le h548
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c418_pos (not_le.mp h0).le h536 (not_le.mp h548).le h547
                  · -- right
                    by_cases h549 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c421_pos (not_le.mp h0).le h536 (not_le.mp h547).le h549
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c422_pos (not_le.mp h0).le h536 (not_le.mp h549).le h539
              · -- right
                by_cases h550 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h551 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h552 : a ≤ ((13/32 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c433_pos (not_le.mp h0).le h552 (not_le.mp h539).le h551
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c434_pos (not_le.mp h552).le h536 (not_le.mp h539).le h551
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c65_pos (not_le.mp h0).le h536 (not_le.mp h551).le h550
                · -- right
                  by_cases h553 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c67_pos (not_le.mp h0).le h536 (not_le.mp h550).le h553
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c68_pos (not_le.mp h0).le h536 (not_le.mp h553).le h538
            · -- right
              by_cases h554 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h555 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h556 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c100_pos (not_le.mp h0).le h536 (not_le.mp h538).le h556
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c101_pos (not_le.mp h0).le h536 (not_le.mp h556).le h555
                · -- right
                  by_cases h557 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c104_pos (not_le.mp h0).le h536 (not_le.mp h555).le h557
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c105_pos (not_le.mp h0).le h536 (not_le.mp h557).le h554
              · -- right
                by_cases h558 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h559 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c116_pos (not_le.mp h0).le h536 (not_le.mp h554).le h559
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c117_pos (not_le.mp h0).le h536 (not_le.mp h559).le h558
                · -- right
                  by_cases h560 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c120_pos (not_le.mp h0).le h536 (not_le.mp h558).le h560
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c121_pos (not_le.mp h0).le h536 (not_le.mp h560).le h537
          · -- right
            by_cases h561 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h562 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h563 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h564 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c194_pos (not_le.mp h0).le h536 (not_le.mp h537).le h564
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c195_pos (not_le.mp h0).le h536 (not_le.mp h564).le h563
                · -- right
                  by_cases h565 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c198_pos (not_le.mp h0).le h536 (not_le.mp h563).le h565
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c199_pos (not_le.mp h0).le h536 (not_le.mp h565).le h562
              · -- right
                by_cases h566 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h567 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c208_pos (not_le.mp h0).le h536 (not_le.mp h562).le h567
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c209_pos (not_le.mp h0).le h536 (not_le.mp h567).le h566
                · -- right
                  by_cases h568 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c212_pos (not_le.mp h0).le h536 (not_le.mp h566).le h568
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c213_pos (not_le.mp h0).le h536 (not_le.mp h568).le h561
            · -- right
              by_cases h569 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h570 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h571 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c245_pos (not_le.mp h0).le h536 (not_le.mp h561).le h571
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c246_pos (not_le.mp h0).le h536 (not_le.mp h571).le h570
                · -- right
                  by_cases h572 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c253_pos (not_le.mp h0).le h536 (not_le.mp h570).le h572
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c255_pos (not_le.mp h0).le h536 (not_le.mp h572).le h569
              · -- right
                by_cases h573 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h574 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c278_pos (not_le.mp h0).le h536 (not_le.mp h569).le h574
                  · -- right
                    by_cases h575 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c547_pos (not_le.mp h0).le h536 (not_le.mp h574).le h575
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c548_pos (not_le.mp h0).le h536 (not_le.mp h575).le h573
                · -- right
                  by_cases h576 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h577 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c563_pos (not_le.mp h0).le h536 (not_le.mp h573).le h577
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c565_pos (not_le.mp h0).le h536 (not_le.mp h577).le h576
                  · -- right
                    by_cases h578 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h579 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c731_pos (not_le.mp h0).le h536 (not_le.mp h576).le h579
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c733_pos (not_le.mp h0).le h536 (not_le.mp h579).le h578
                    · -- right
                      by_cases h580 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c747_pos (not_le.mp h0).le h536 (not_le.mp h578).le h580
                      · -- right
                        by_cases h581 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c805_pos (not_le.mp h0).le h536 (not_le.mp h580).le h581
                        · -- right
                          by_cases h582 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c826_pos (not_le.mp h0).le h536 (not_le.mp h581).le h582
                          · -- right
                            by_cases h583 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c854_pos (not_le.mp h0).le h536 (not_le.mp h582).le h583
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c855_pos (not_le.mp h0).le h536 (not_le.mp h583).le hz2
        · -- right
          by_cases h584 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h585 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h586 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h587 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h588 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h589 : a ≤ ((67/160 : ℚ) : ℝ)
                    · -- left
                      by_cases h590 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c681_pos (not_le.mp h536).le h589 hz1 h590
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c683_pos (not_le.mp h536).le h589 (not_le.mp h590).le h588
                    · -- right
                      by_cases h591 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c682_pos (not_le.mp h589).le h535 hz1 h591
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c684_pos (not_le.mp h589).le h535 (not_le.mp h591).le h588
                  · -- right
                    by_cases h592 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c410_pos (not_le.mp h536).le h535 (not_le.mp h588).le h592
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c411_pos (not_le.mp h536).le h535 (not_le.mp h592).le h587
                · -- right
                  by_cases h593 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h594 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c419_pos (not_le.mp h536).le h535 (not_le.mp h587).le h594
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c420_pos (not_le.mp h536).le h535 (not_le.mp h594).le h593
                  · -- right
                    by_cases h595 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c423_pos (not_le.mp h536).le h535 (not_le.mp h593).le h595
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c424_pos (not_le.mp h536).le h535 (not_le.mp h595).le h586
              · -- right
                by_cases h596 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h597 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h598 : a ≤ ((67/160 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c435_pos (not_le.mp h536).le h598 (not_le.mp h586).le h597
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c436_pos (not_le.mp h598).le h535 (not_le.mp h586).le h597
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c66_pos (not_le.mp h536).le h535 (not_le.mp h597).le h596
                · -- right
                  by_cases h599 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c69_pos (not_le.mp h536).le h535 (not_le.mp h596).le h599
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c70_pos (not_le.mp h536).le h535 (not_le.mp h599).le h585
            · -- right
              by_cases h600 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h601 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h602 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c102_pos (not_le.mp h536).le h535 (not_le.mp h585).le h602
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c103_pos (not_le.mp h536).le h535 (not_le.mp h602).le h601
                · -- right
                  by_cases h603 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c106_pos (not_le.mp h536).le h535 (not_le.mp h601).le h603
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c107_pos (not_le.mp h536).le h535 (not_le.mp h603).le h600
              · -- right
                by_cases h604 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h605 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c118_pos (not_le.mp h536).le h535 (not_le.mp h600).le h605
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c119_pos (not_le.mp h536).le h535 (not_le.mp h605).le h604
                · -- right
                  by_cases h606 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c122_pos (not_le.mp h536).le h535 (not_le.mp h604).le h606
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c123_pos (not_le.mp h536).le h535 (not_le.mp h606).le h584
          · -- right
            by_cases h607 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h608 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h609 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h610 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B009.c196_pos (not_le.mp h536).le h535 (not_le.mp h584).le h610
                  · -- right
                    exact CKLaneC2R.Cells.S02.B009.c197_pos (not_le.mp h536).le h535 (not_le.mp h610).le h609
                · -- right
                  by_cases h611 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c200_pos (not_le.mp h536).le h535 (not_le.mp h609).le h611
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c201_pos (not_le.mp h536).le h535 (not_le.mp h611).le h608
              · -- right
                by_cases h612 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h613 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c210_pos (not_le.mp h536).le h535 (not_le.mp h608).le h613
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c211_pos (not_le.mp h536).le h535 (not_le.mp h613).le h612
                · -- right
                  by_cases h614 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c214_pos (not_le.mp h536).le h535 (not_le.mp h612).le h614
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c215_pos (not_le.mp h536).le h535 (not_le.mp h614).le h607
            · -- right
              by_cases h615 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h616 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h617 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c247_pos (not_le.mp h536).le h535 (not_le.mp h607).le h617
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c248_pos (not_le.mp h536).le h535 (not_le.mp h617).le h616
                · -- right
                  by_cases h618 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c254_pos (not_le.mp h536).le h535 (not_le.mp h616).le h618
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c256_pos (not_le.mp h536).le h535 (not_le.mp h618).le h615
              · -- right
                by_cases h619 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h620 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c279_pos (not_le.mp h536).le h535 (not_le.mp h615).le h620
                  · -- right
                    by_cases h621 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c549_pos (not_le.mp h536).le h535 (not_le.mp h620).le h621
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c550_pos (not_le.mp h536).le h535 (not_le.mp h621).le h619
                · -- right
                  by_cases h622 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h623 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c564_pos (not_le.mp h536).le h535 (not_le.mp h619).le h623
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c566_pos (not_le.mp h536).le h535 (not_le.mp h623).le h622
                  · -- right
                    by_cases h624 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h625 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c732_pos (not_le.mp h536).le h535 (not_le.mp h622).le h625
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c734_pos (not_le.mp h536).le h535 (not_le.mp h625).le h624
                    · -- right
                      by_cases h626 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c748_pos (not_le.mp h536).le h535 (not_le.mp h624).le h626
                      · -- right
                        by_cases h627 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c806_pos (not_le.mp h536).le h535 (not_le.mp h626).le h627
                        · -- right
                          by_cases h628 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c827_pos (not_le.mp h536).le h535 (not_le.mp h627).le h628
                          · -- right
                            by_cases h629 : z ≤ ((1022063/1024000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.Cells.S02.B042.c856_pos (not_le.mp h536).le h535 (not_le.mp h628).le h629
                            · -- right
                              exact CKLaneC2R.Cells.S02.B042.c857_pos (not_le.mp h536).le h535 (not_le.mp h629).le hz2
      · -- right
        by_cases h630 : a ≤ ((7/16 : ℚ) : ℝ)
        · -- left
          by_cases h631 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h632 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h633 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h634 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h635 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h636 : a ≤ ((69/160 : ℚ) : ℝ)
                    · -- left
                      by_cases h637 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c687_pos (not_le.mp h535).le h636 hz1 h637
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c689_pos (not_le.mp h535).le h636 (not_le.mp h637).le h635
                    · -- right
                      by_cases h638 : z ≤ ((6417/64000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c688_pos (not_le.mp h636).le h630 hz1 h638
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c690_pos (not_le.mp h636).le h630 (not_le.mp h638).le h635
                  · -- right
                    by_cases h639 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c413_pos (not_le.mp h535).le h630 (not_le.mp h635).le h639
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c414_pos (not_le.mp h535).le h630 (not_le.mp h639).le h634
                · -- right
                  by_cases h640 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h641 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c425_pos (not_le.mp h535).le h630 (not_le.mp h634).le h641
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c426_pos (not_le.mp h535).le h630 (not_le.mp h641).le h640
                  · -- right
                    by_cases h642 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c429_pos (not_le.mp h535).le h630 (not_le.mp h640).le h642
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c430_pos (not_le.mp h535).le h630 (not_le.mp h642).le h633
              · -- right
                by_cases h643 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h644 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c71_pos (not_le.mp h535).le h630 (not_le.mp h633).le h644
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c72_pos (not_le.mp h535).le h630 (not_le.mp h644).le h643
                · -- right
                  by_cases h645 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c75_pos (not_le.mp h535).le h630 (not_le.mp h643).le h645
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c76_pos (not_le.mp h535).le h630 (not_le.mp h645).le h632
            · -- right
              by_cases h646 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h647 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h648 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c108_pos (not_le.mp h535).le h630 (not_le.mp h632).le h648
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c109_pos (not_le.mp h535).le h630 (not_le.mp h648).le h647
                · -- right
                  by_cases h649 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c112_pos (not_le.mp h535).le h630 (not_le.mp h647).le h649
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c113_pos (not_le.mp h535).le h630 (not_le.mp h649).le h646
              · -- right
                by_cases h650 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h651 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c124_pos (not_le.mp h535).le h630 (not_le.mp h646).le h651
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c125_pos (not_le.mp h535).le h630 (not_le.mp h651).le h650
                · -- right
                  by_cases h652 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c128_pos (not_le.mp h535).le h630 (not_le.mp h650).le h652
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c129_pos (not_le.mp h535).le h630 (not_le.mp h652).le h631
          · -- right
            by_cases h653 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h654 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h655 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h656 : z ≤ ((18273/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c202_pos (not_le.mp h535).le h630 (not_le.mp h631).le h656
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c203_pos (not_le.mp h535).le h630 (not_le.mp h656).le h655
                · -- right
                  by_cases h657 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c204_pos (not_le.mp h535).le h630 (not_le.mp h655).le h657
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c205_pos (not_le.mp h535).le h630 (not_le.mp h657).le h654
              · -- right
                by_cases h658 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h659 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c216_pos (not_le.mp h535).le h630 (not_le.mp h654).le h659
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c217_pos (not_le.mp h535).le h630 (not_le.mp h659).le h658
                · -- right
                  by_cases h660 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c220_pos (not_le.mp h535).le h630 (not_le.mp h658).le h660
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c221_pos (not_le.mp h535).le h630 (not_le.mp h660).le h653
            · -- right
              by_cases h661 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h662 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h663 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c249_pos (not_le.mp h535).le h630 (not_le.mp h653).le h663
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c250_pos (not_le.mp h535).le h630 (not_le.mp h663).le h662
                · -- right
                  by_cases h664 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c257_pos (not_le.mp h535).le h630 (not_le.mp h662).le h664
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c259_pos (not_le.mp h535).le h630 (not_le.mp h664).le h661
              · -- right
                by_cases h665 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h666 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c280_pos (not_le.mp h535).le h630 (not_le.mp h661).le h666
                  · -- right
                    by_cases h667 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c551_pos (not_le.mp h535).le h630 (not_le.mp h666).le h667
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c552_pos (not_le.mp h535).le h630 (not_le.mp h667).le h665
                · -- right
                  by_cases h668 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h669 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c567_pos (not_le.mp h535).le h630 (not_le.mp h665).le h669
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c569_pos (not_le.mp h535).le h630 (not_le.mp h669).le h668
                  · -- right
                    by_cases h670 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h671 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c735_pos (not_le.mp h535).le h630 (not_le.mp h668).le h671
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c737_pos (not_le.mp h535).le h630 (not_le.mp h671).le h670
                    · -- right
                      by_cases h672 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c749_pos (not_le.mp h535).le h630 (not_le.mp h670).le h672
                      · -- right
                        by_cases h673 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c807_pos (not_le.mp h535).le h630 (not_le.mp h672).le h673
                        · -- right
                          by_cases h674 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c828_pos (not_le.mp h535).le h630 (not_le.mp h673).le h674
                          · -- right
                            exact CKLaneC2R.Cells.S02.B041.c830_pos (not_le.mp h535).le h630 (not_le.mp h674).le hz2
        · -- right
          by_cases h675 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h676 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h677 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h678 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h679 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h680 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h681 : a ≤ ((71/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c691_pos (not_le.mp h630).le h681 hz1 h680
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c692_pos (not_le.mp h681).le h534 hz1 h680
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c412_pos (not_le.mp h630).le h534 (not_le.mp h680).le h679
                  · -- right
                    by_cases h682 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B020.c415_pos (not_le.mp h630).le h534 (not_le.mp h679).le h682
                    · -- right
                      exact CKLaneC2R.Cells.S02.B020.c416_pos (not_le.mp h630).le h534 (not_le.mp h682).le h678
                · -- right
                  by_cases h683 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h684 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c427_pos (not_le.mp h630).le h534 (not_le.mp h678).le h684
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c428_pos (not_le.mp h630).le h534 (not_le.mp h684).le h683
                  · -- right
                    by_cases h685 : z ≤ ((2379/12800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c431_pos (not_le.mp h630).le h534 (not_le.mp h683).le h685
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c432_pos (not_le.mp h630).le h534 (not_le.mp h685).le h677
              · -- right
                by_cases h686 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h687 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c73_pos (not_le.mp h630).le h534 (not_le.mp h677).le h687
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c74_pos (not_le.mp h630).le h534 (not_le.mp h687).le h686
                · -- right
                  by_cases h688 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B003.c77_pos (not_le.mp h630).le h534 (not_le.mp h686).le h688
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c78_pos (not_le.mp h630).le h534 (not_le.mp h688).le h676
            · -- right
              by_cases h689 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h690 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h691 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c110_pos (not_le.mp h630).le h534 (not_le.mp h676).le h691
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c111_pos (not_le.mp h630).le h534 (not_le.mp h691).le h690
                · -- right
                  by_cases h692 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B005.c114_pos (not_le.mp h630).le h534 (not_le.mp h690).le h692
                  · -- right
                    exact CKLaneC2R.Cells.S02.B005.c115_pos (not_le.mp h630).le h534 (not_le.mp h692).le h689
              · -- right
                by_cases h693 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h694 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c126_pos (not_le.mp h630).le h534 (not_le.mp h689).le h694
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c127_pos (not_le.mp h630).le h534 (not_le.mp h694).le h693
                · -- right
                  by_cases h695 : z ≤ ((16447/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c130_pos (not_le.mp h630).le h534 (not_le.mp h693).le h695
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c131_pos (not_le.mp h630).le h534 (not_le.mp h695).le h675
          · -- right
            by_cases h696 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h697 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h698 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c9_pos (not_le.mp h630).le h534 (not_le.mp h675).le h698
                · -- right
                  by_cases h699 : z ≤ ((20099/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c206_pos (not_le.mp h630).le h534 (not_le.mp h698).le h699
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c207_pos (not_le.mp h630).le h534 (not_le.mp h699).le h697
              · -- right
                by_cases h700 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h701 : z ≤ ((877/1280 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B010.c218_pos (not_le.mp h630).le h534 (not_le.mp h697).le h701
                  · -- right
                    exact CKLaneC2R.Cells.S02.B010.c219_pos (not_le.mp h630).le h534 (not_le.mp h701).le h700
                · -- right
                  by_cases h702 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c222_pos (not_le.mp h630).le h534 (not_le.mp h700).le h702
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c223_pos (not_le.mp h630).le h534 (not_le.mp h702).le h696
            · -- right
              by_cases h703 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h704 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h705 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c251_pos (not_le.mp h630).le h534 (not_le.mp h696).le h705
                  · -- right
                    exact CKLaneC2R.Cells.S02.B012.c252_pos (not_le.mp h630).le h534 (not_le.mp h705).le h704
                · -- right
                  by_cases h706 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B012.c258_pos (not_le.mp h630).le h534 (not_le.mp h704).le h706
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c260_pos (not_le.mp h630).le h534 (not_le.mp h706).le h703
              · -- right
                by_cases h707 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h708 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c281_pos (not_le.mp h630).le h534 (not_le.mp h703).le h708
                  · -- right
                    by_cases h709 : z ≤ ((59371/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B027.c553_pos (not_le.mp h630).le h534 (not_le.mp h708).le h709
                    · -- right
                      exact CKLaneC2R.Cells.S02.B027.c554_pos (not_le.mp h630).le h534 (not_le.mp h709).le h707
                · -- right
                  by_cases h710 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h711 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c568_pos (not_le.mp h630).le h534 (not_le.mp h707).le h711
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c570_pos (not_le.mp h630).le h534 (not_le.mp h711).le h710
                  · -- right
                    by_cases h712 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h713 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c736_pos (not_le.mp h630).le h534 (not_le.mp h710).le h713
                      · -- right
                        exact CKLaneC2R.Cells.S02.B036.c738_pos (not_le.mp h630).le h534 (not_le.mp h713).le h712
                    · -- right
                      by_cases h714 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c750_pos (not_le.mp h630).le h534 (not_le.mp h712).le h714
                      · -- right
                        by_cases h715 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c808_pos (not_le.mp h630).le h534 (not_le.mp h714).le h715
                        · -- right
                          by_cases h716 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c829_pos (not_le.mp h630).le h534 (not_le.mp h715).le h716
                          · -- right
                            exact CKLaneC2R.Cells.S02.B041.c831_pos (not_le.mp h630).le h534 (not_le.mp h716).le hz2
    · -- right
      by_cases h717 : a ≤ ((19/40 : ℚ) : ℝ)
      · -- left
        by_cases h718 : a ≤ ((37/80 : ℚ) : ℝ)
        · -- left
          by_cases h719 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h720 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h721 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h722 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h723 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h724 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h725 : a ≤ ((73/160 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c693_pos (not_le.mp h534).le h725 hz1 h724
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c694_pos (not_le.mp h725).le h718 hz1 h724
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c437_pos (not_le.mp h534).le h718 (not_le.mp h724).le h723
                  · -- right
                    by_cases h726 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B021.c439_pos (not_le.mp h534).le h718 (not_le.mp h723).le h726
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c440_pos (not_le.mp h534).le h718 (not_le.mp h726).le h722
                · -- right
                  by_cases h727 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h728 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c451_pos (not_le.mp h534).le h718 (not_le.mp h722).le h728
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c452_pos (not_le.mp h534).le h718 (not_le.mp h728).le h727
                  · -- right
                    exact CKLaneC2R.Cells.S02.B003.c79_pos (not_le.mp h534).le h718 (not_le.mp h727).le h721
              · -- right
                by_cases h729 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h730 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c84_pos (not_le.mp h534).le h718 (not_le.mp h721).le h730
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c85_pos (not_le.mp h534).le h718 (not_le.mp h730).le h729
                · -- right
                  by_cases h731 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c88_pos (not_le.mp h534).le h718 (not_le.mp h729).le h731
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c89_pos (not_le.mp h534).le h718 (not_le.mp h731).le h720
            · -- right
              by_cases h732 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h733 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h734 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c132_pos (not_le.mp h534).le h718 (not_le.mp h720).le h734
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c133_pos (not_le.mp h534).le h718 (not_le.mp h734).le h733
                · -- right
                  by_cases h735 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c136_pos (not_le.mp h534).le h718 (not_le.mp h733).le h735
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c137_pos (not_le.mp h534).le h718 (not_le.mp h735).le h732
              · -- right
                by_cases h736 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h737 : z ≤ ((14621/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c144_pos (not_le.mp h534).le h718 (not_le.mp h732).le h737
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c145_pos (not_le.mp h534).le h718 (not_le.mp h737).le h736
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c3_pos (not_le.mp h534).le h718 (not_le.mp h736).le h719
          · -- right
            by_cases h738 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h739 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h740 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c10_pos (not_le.mp h534).le h718 (not_le.mp h719).le h740
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c12_pos (not_le.mp h534).le h718 (not_le.mp h740).le h739
              · -- right
                by_cases h741 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c18_pos (not_le.mp h534).le h718 (not_le.mp h739).le h741
                · -- right
                  by_cases h742 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c224_pos (not_le.mp h534).le h718 (not_le.mp h741).le h742
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c225_pos (not_le.mp h534).le h718 (not_le.mp h742).le h738
            · -- right
              by_cases h743 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h744 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h745 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c261_pos (not_le.mp h534).le h718 (not_le.mp h738).le h745
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c262_pos (not_le.mp h534).le h718 (not_le.mp h745).le h744
                · -- right
                  by_cases h746 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c269_pos (not_le.mp h534).le h718 (not_le.mp h744).le h746
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c271_pos (not_le.mp h534).le h718 (not_le.mp h746).le h743
              · -- right
                by_cases h747 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h748 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c282_pos (not_le.mp h534).le h718 (not_le.mp h743).le h748
                  · -- right
                    exact CKLaneC2R.Cells.S02.B014.c284_pos (not_le.mp h534).le h718 (not_le.mp h748).le h747
                · -- right
                  by_cases h749 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h750 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c571_pos (not_le.mp h534).le h718 (not_le.mp h747).le h750
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c573_pos (not_le.mp h534).le h718 (not_le.mp h750).le h749
                  · -- right
                    by_cases h751 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h752 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B036.c739_pos (not_le.mp h534).le h718 (not_le.mp h749).le h752
                      · -- right
                        exact CKLaneC2R.Cells.S02.B037.c741_pos (not_le.mp h534).le h718 (not_le.mp h752).le h751
                    · -- right
                      by_cases h753 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c751_pos (not_le.mp h534).le h718 (not_le.mp h751).le h753
                      · -- right
                        by_cases h754 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c809_pos (not_le.mp h534).le h718 (not_le.mp h753).le h754
                        · -- right
                          by_cases h755 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c832_pos (not_le.mp h534).le h718 (not_le.mp h754).le h755
                          · -- right
                            exact CKLaneC2R.Cells.S02.B041.c834_pos (not_le.mp h534).le h718 (not_le.mp h755).le hz2
        · -- right
          by_cases h756 : z ≤ ((217/400 : ℚ) : ℝ)
          · -- left
            by_cases h757 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h758 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h759 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h760 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h761 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h762 : a ≤ ((15/32 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B034.c695_pos (not_le.mp h718).le h762 hz1 h761
                      · -- right
                        exact CKLaneC2R.Cells.S02.B034.c696_pos (not_le.mp h762).le h717 hz1 h761
                    · -- right
                      exact CKLaneC2R.Cells.S02.B021.c438_pos (not_le.mp h718).le h717 (not_le.mp h761).le h760
                  · -- right
                    by_cases h763 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c441_pos (not_le.mp h718).le h717 (not_le.mp h760).le h763
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c442_pos (not_le.mp h718).le h717 (not_le.mp h763).le h759
                · -- right
                  by_cases h764 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h765 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c453_pos (not_le.mp h718).le h717 (not_le.mp h759).le h765
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c454_pos (not_le.mp h718).le h717 (not_le.mp h765).le h764
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c80_pos (not_le.mp h718).le h717 (not_le.mp h764).le h758
              · -- right
                by_cases h766 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h767 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c86_pos (not_le.mp h718).le h717 (not_le.mp h758).le h767
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c87_pos (not_le.mp h718).le h717 (not_le.mp h767).le h766
                · -- right
                  by_cases h768 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c90_pos (not_le.mp h718).le h717 (not_le.mp h766).le h768
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c91_pos (not_le.mp h718).le h717 (not_le.mp h768).le h757
            · -- right
              by_cases h769 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h770 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h771 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c134_pos (not_le.mp h718).le h717 (not_le.mp h757).le h771
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c135_pos (not_le.mp h718).le h717 (not_le.mp h771).le h770
                · -- right
                  by_cases h772 : z ≤ ((2559/6400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B006.c138_pos (not_le.mp h718).le h717 (not_le.mp h770).le h772
                  · -- right
                    exact CKLaneC2R.Cells.S02.B006.c139_pos (not_le.mp h718).le h717 (not_le.mp h772).le h769
              · -- right
                by_cases h773 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c2_pos (not_le.mp h718).le h717 (not_le.mp h769).le h773
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c4_pos (not_le.mp h718).le h717 (not_le.mp h773).le h756
          · -- right
            by_cases h774 : z ≤ ((3083/4000 : ℚ) : ℝ)
            · -- left
              by_cases h775 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h776 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c11_pos (not_le.mp h718).le h717 (not_le.mp h756).le h776
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c13_pos (not_le.mp h718).le h717 (not_le.mp h776).le h775
              · -- right
                by_cases h777 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c19_pos (not_le.mp h718).le h717 (not_le.mp h775).le h777
                · -- right
                  by_cases h778 : z ≤ ((23751/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B011.c226_pos (not_le.mp h718).le h717 (not_le.mp h777).le h778
                  · -- right
                    exact CKLaneC2R.Cells.S02.B011.c227_pos (not_le.mp h718).le h717 (not_le.mp h778).le h774
            · -- right
              by_cases h779 : z ≤ ((7079/8000 : ℚ) : ℝ)
              · -- left
                by_cases h780 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h781 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c263_pos (not_le.mp h718).le h717 (not_le.mp h774).le h781
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c264_pos (not_le.mp h718).le h717 (not_le.mp h781).le h780
                · -- right
                  by_cases h782 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c270_pos (not_le.mp h718).le h717 (not_le.mp h780).le h782
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c272_pos (not_le.mp h718).le h717 (not_le.mp h782).le h779
              · -- right
                by_cases h783 : z ≤ ((15071/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h784 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c283_pos (not_le.mp h718).le h717 (not_le.mp h779).le h784
                  · -- right
                    exact CKLaneC2R.Cells.S02.B014.c285_pos (not_le.mp h718).le h717 (not_le.mp h784).le h783
                · -- right
                  by_cases h785 : z ≤ ((6211/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h786 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c572_pos (not_le.mp h718).le h717 (not_le.mp h783).le h786
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c574_pos (not_le.mp h718).le h717 (not_le.mp h786).le h785
                  · -- right
                    by_cases h787 : z ≤ ((63023/64000 : ℚ) : ℝ)
                    · -- left
                      by_cases h788 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c740_pos (not_le.mp h718).le h717 (not_le.mp h785).le h788
                      · -- right
                        exact CKLaneC2R.Cells.S02.B037.c742_pos (not_le.mp h718).le h717 (not_le.mp h788).le h787
                    · -- right
                      by_cases h789 : z ≤ ((126959/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c752_pos (not_le.mp h718).le h717 (not_le.mp h787).le h789
                      · -- right
                        by_cases h790 : z ≤ ((254831/256000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c810_pos (not_le.mp h718).le h717 (not_le.mp h789).le h790
                        · -- right
                          by_cases h791 : z ≤ ((20423/20480 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c833_pos (not_le.mp h718).le h717 (not_le.mp h790).le h791
                          · -- right
                            exact CKLaneC2R.Cells.S02.B041.c835_pos (not_le.mp h718).le h717 (not_le.mp h791).le hz2
      · -- right
        by_cases h792 : z ≤ ((217/400 : ℚ) : ℝ)
        · -- left
          by_cases h793 : a ≤ ((39/80 : ℚ) : ℝ)
          · -- left
            by_cases h794 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h795 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h796 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h797 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h798 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c443_pos (not_le.mp h717).le h793 hz1 h798
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c444_pos (not_le.mp h717).le h793 (not_le.mp h798).le h797
                  · -- right
                    by_cases h799 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c447_pos (not_le.mp h717).le h793 (not_le.mp h797).le h799
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c448_pos (not_le.mp h717).le h793 (not_le.mp h799).le h796
                · -- right
                  by_cases h800 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    by_cases h801 : z ≤ ((10069/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c455_pos (not_le.mp h717).le h793 (not_le.mp h796).le h801
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c456_pos (not_le.mp h717).le h793 (not_le.mp h801).le h800
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c82_pos (not_le.mp h717).le h793 (not_le.mp h800).le h795
              · -- right
                by_cases h802 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h803 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c92_pos (not_le.mp h717).le h793 (not_le.mp h795).le h803
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c94_pos (not_le.mp h717).le h793 (not_le.mp h803).le h802
                · -- right
                  by_cases h804 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c96_pos (not_le.mp h717).le h793 (not_le.mp h802).le h804
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c97_pos (not_le.mp h717).le h793 (not_le.mp h804).le h794
            · -- right
              by_cases h805 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h806 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h807 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c140_pos (not_le.mp h717).le h793 (not_le.mp h794).le h807
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c141_pos (not_le.mp h717).le h793 (not_le.mp h807).le h806
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c0_pos (not_le.mp h717).le h793 (not_le.mp h806).le h805
              · -- right
                by_cases h808 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c5_pos (not_le.mp h717).le h793 (not_le.mp h805).le h808
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c7_pos (not_le.mp h717).le h793 (not_le.mp h808).le h792
          · -- right
            by_cases h809 : z ≤ ((1257/4000 : ℚ) : ℝ)
            · -- left
              by_cases h810 : z ≤ ((1601/8000 : ℚ) : ℝ)
              · -- left
                by_cases h811 : z ≤ ((2289/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h812 : z ≤ ((733/6400 : ℚ) : ℝ)
                  · -- left
                    by_cases h813 : z ≤ ((6417/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c445_pos (not_le.mp h793).le ha2 hz1 h813
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c446_pos (not_le.mp h793).le ha2 (not_le.mp h813).le h812
                  · -- right
                    by_cases h814 : z ≤ ((8243/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B022.c449_pos (not_le.mp h793).le ha2 (not_le.mp h812).le h814
                    · -- right
                      exact CKLaneC2R.Cells.S02.B022.c450_pos (not_le.mp h793).le ha2 (not_le.mp h814).le h811
                · -- right
                  by_cases h815 : z ≤ ((5491/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c81_pos (not_le.mp h793).le ha2 (not_le.mp h811).le h815
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c83_pos (not_le.mp h793).le ha2 (not_le.mp h815).le h810
              · -- right
                by_cases h816 : z ≤ ((823/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h817 : z ≤ ((7317/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c93_pos (not_le.mp h793).le ha2 (not_le.mp h810).le h817
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c95_pos (not_le.mp h793).le ha2 (not_le.mp h817).le h816
                · -- right
                  by_cases h818 : z ≤ ((9143/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B004.c98_pos (not_le.mp h793).le ha2 (not_le.mp h816).le h818
                  · -- right
                    exact CKLaneC2R.Cells.S02.B004.c99_pos (not_le.mp h793).le ha2 (not_le.mp h818).le h809
            · -- right
              by_cases h819 : z ≤ ((3427/8000 : ℚ) : ℝ)
              · -- left
                by_cases h820 : z ≤ ((5941/16000 : ℚ) : ℝ)
                · -- left
                  by_cases h821 : z ≤ ((10969/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B007.c142_pos (not_le.mp h793).le ha2 (not_le.mp h809).le h821
                  · -- right
                    exact CKLaneC2R.Cells.S02.B007.c143_pos (not_le.mp h793).le ha2 (not_le.mp h821).le h820
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c1_pos (not_le.mp h793).le ha2 (not_le.mp h820).le h819
              · -- right
                by_cases h822 : z ≤ ((7767/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c6_pos (not_le.mp h793).le ha2 (not_le.mp h819).le h822
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c8_pos (not_le.mp h793).le ha2 (not_le.mp h822).le h792
        · -- right
          by_cases h823 : z ≤ ((3083/4000 : ℚ) : ℝ)
          · -- left
            by_cases h824 : a ≤ ((39/80 : ℚ) : ℝ)
            · -- left
              by_cases h825 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h826 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c14_pos (not_le.mp h717).le h824 (not_le.mp h792).le h826
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c16_pos (not_le.mp h717).le h824 (not_le.mp h826).le h825
              · -- right
                by_cases h827 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B001.c20_pos (not_le.mp h717).le h824 (not_le.mp h825).le h827
                · -- right
                  exact CKLaneC2R.Cells.S02.B001.c22_pos (not_le.mp h717).le h824 (not_le.mp h827).le h823
            · -- right
              by_cases h828 : z ≤ ((5253/8000 : ℚ) : ℝ)
              · -- left
                by_cases h829 : z ≤ ((9593/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B000.c15_pos (not_le.mp h824).le ha2 (not_le.mp h792).le h829
                · -- right
                  exact CKLaneC2R.Cells.S02.B000.c17_pos (not_le.mp h824).le ha2 (not_le.mp h829).le h828
              · -- right
                by_cases h830 : z ≤ ((11419/16000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.Cells.S02.B001.c21_pos (not_le.mp h824).le ha2 (not_le.mp h828).le h830
                · -- right
                  exact CKLaneC2R.Cells.S02.B001.c23_pos (not_le.mp h824).le ha2 (not_le.mp h830).le h823
          · -- right
            by_cases h831 : z ≤ ((7079/8000 : ℚ) : ℝ)
            · -- left
              by_cases h832 : a ≤ ((39/80 : ℚ) : ℝ)
              · -- left
                by_cases h833 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h834 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c265_pos (not_le.mp h717).le h832 (not_le.mp h823).le h834
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c266_pos (not_le.mp h717).le h832 (not_le.mp h834).le h833
                · -- right
                  by_cases h835 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c273_pos (not_le.mp h717).le h832 (not_le.mp h833).le h835
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c275_pos (not_le.mp h717).le h832 (not_le.mp h835).le h831
              · -- right
                by_cases h836 : z ≤ ((2649/3200 : ℚ) : ℝ)
                · -- left
                  by_cases h837 : z ≤ ((25577/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c267_pos (not_le.mp h832).le ha2 (not_le.mp h823).le h837
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c268_pos (not_le.mp h832).le ha2 (not_le.mp h837).le h836
                · -- right
                  by_cases h838 : z ≤ ((27403/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B013.c274_pos (not_le.mp h832).le ha2 (not_le.mp h836).le h838
                  · -- right
                    exact CKLaneC2R.Cells.S02.B013.c276_pos (not_le.mp h832).le ha2 (not_le.mp h838).le h831
            · -- right
              by_cases h839 : z ≤ ((15071/16000 : ℚ) : ℝ)
              · -- left
                by_cases h840 : a ≤ ((39/80 : ℚ) : ℝ)
                · -- left
                  by_cases h841 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c286_pos (not_le.mp h717).le h840 (not_le.mp h831).le h841
                  · -- right
                    exact CKLaneC2R.Cells.S02.B014.c288_pos (not_le.mp h717).le h840 (not_le.mp h841).le h839
                · -- right
                  by_cases h842 : z ≤ ((29229/32000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.Cells.S02.B014.c287_pos (not_le.mp h840).le ha2 (not_le.mp h831).le h842
                  · -- right
                    exact CKLaneC2R.Cells.S02.B014.c289_pos (not_le.mp h840).le ha2 (not_le.mp h842).le h839
              · -- right
                by_cases h843 : z ≤ ((6211/6400 : ℚ) : ℝ)
                · -- left
                  by_cases h844 : a ≤ ((39/80 : ℚ) : ℝ)
                  · -- left
                    by_cases h845 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c575_pos (not_le.mp h717).le h844 (not_le.mp h839).le h845
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c577_pos (not_le.mp h717).le h844 (not_le.mp h845).le h843
                  · -- right
                    by_cases h846 : z ≤ ((61197/64000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.Cells.S02.B028.c576_pos (not_le.mp h844).le ha2 (not_le.mp h839).le h846
                    · -- right
                      exact CKLaneC2R.Cells.S02.B028.c578_pos (not_le.mp h844).le ha2 (not_le.mp h846).le h843
                · -- right
                  by_cases h847 : z ≤ ((63023/64000 : ℚ) : ℝ)
                  · -- left
                    by_cases h848 : a ≤ ((39/80 : ℚ) : ℝ)
                    · -- left
                      by_cases h849 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c743_pos (not_le.mp h717).le h848 (not_le.mp h843).le h849
                      · -- right
                        exact CKLaneC2R.Cells.S02.B037.c745_pos (not_le.mp h717).le h848 (not_le.mp h849).le h847
                    · -- right
                      by_cases h850 : z ≤ ((125133/128000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c744_pos (not_le.mp h848).le ha2 (not_le.mp h843).le h850
                      · -- right
                        exact CKLaneC2R.Cells.S02.B037.c746_pos (not_le.mp h848).le ha2 (not_le.mp h850).le h847
                  · -- right
                    by_cases h851 : z ≤ ((126959/128000 : ℚ) : ℝ)
                    · -- left
                      by_cases h852 : a ≤ ((39/80 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.Cells.S02.B037.c753_pos (not_le.mp h717).le h852 (not_le.mp h847).le h851
                      · -- right
                        exact CKLaneC2R.Cells.S02.B037.c754_pos (not_le.mp h852).le ha2 (not_le.mp h847).le h851
                    · -- right
                      by_cases h853 : z ≤ ((254831/256000 : ℚ) : ℝ)
                      · -- left
                        by_cases h854 : a ≤ ((39/80 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c811_pos (not_le.mp h717).le h854 (not_le.mp h851).le h853
                        · -- right
                          exact CKLaneC2R.Cells.S02.B040.c812_pos (not_le.mp h854).le ha2 (not_le.mp h851).le h853
                      · -- right
                        by_cases h855 : z ≤ ((20423/20480 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.Cells.S02.B040.c813_pos (not_le.mp h717).le ha2 (not_le.mp h853).le h855
                        · -- right
                          by_cases h856 : a ≤ ((39/80 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.Cells.S02.B041.c836_pos (not_le.mp h717).le h856 (not_le.mp h855).le hz2
                          · -- right
                            exact CKLaneC2R.Cells.S02.B041.c837_pos (not_le.mp h856).le ha2 (not_le.mp h855).le hz2

end CKLaneC2R.CompactCover

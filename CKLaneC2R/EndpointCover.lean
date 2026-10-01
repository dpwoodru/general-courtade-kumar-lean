import CKLaneC2R.EpCells.B000
import CKLaneC2R.EpCells.B001
import CKLaneC2R.EpCells.B002
import CKLaneC2R.EpCells.B003
import CKLaneC2R.EpCells.B004
import CKLaneC2R.EpCells.B005
import CKLaneC2R.EpCells.B006
import CKLaneC2R.EpCells.B007
import CKLaneC2R.EpCells.B008
import CKLaneC2R.EpCells.B009
import CKLaneC2R.EpCells.B010
import CKLaneC2R.EpCells.B011
import CKLaneC2R.EpCells.B012
import CKLaneC2R.EpCells.B013
import CKLaneC2R.EpCells.B014
import CKLaneC2R.EpCells.B015
import CKLaneC2R.EpCells.B016
import CKLaneC2R.EpCells.B017
import CKLaneC2R.EpCells.B018
import CKLaneC2R.EpCells.B019
import CKLaneC2R.EpCells.B020
import CKLaneC2R.EpCells.B021
import CKLaneC2R.EpCells.B022
import CKLaneC2R.EpCells.B023
import CKLaneC2R.EpCells.B024
import CKLaneC2R.EpCells.B025
import CKLaneC2R.EpCells.B026
import CKLaneC2R.EpCells.B027
import CKLaneC2R.EpCells.B028
import CKLaneC2R.EpCells.B029
import CKLaneC2R.EpCells.B030
import CKLaneC2R.EpCells.B031
import CKLaneC2R.EpCells.B032
import CKLaneC2R.EpCells.B033
import CKLaneC2R.EpCells.B034
import CKLaneC2R.EpCells.B035
import CKLaneC2R.EpCells.B036
import CKLaneC2R.EpCells.B037
import CKLaneC2R.EpCells.B038
import CKLaneC2R.EpCells.B039
import CKLaneC2R.EpCells.B040
import CKLaneC2R.EpCells.B041
import CKLaneC2R.EpCells.B042
import CKLaneC2R.EpCells.B043
import CKLaneC2R.EpCells.B044
import CKLaneC2R.EpCells.B045
import CKLaneC2R.EpCells.B046
import CKLaneC2R.EpCells.B047
import CKLaneC2R.EpCells.B048

namespace CKLaneC2R.EndpointCover

/-- Endpoint cover: a ∈ [3/20,999/1000], z ∈ [999/1000,1], z < 1 (2922 cells, BSP depth 16). -/
theorem cover {a z : ℝ} (ha1 : ((3/20 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((999/1000 : ℚ) : ℝ))
    (hz1 : ((999/1000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((1 : ℚ) : ℝ)) (hz : z < 1) :
    0 < GeneralCK.Reflection.curvature a (a * z) := by
  by_cases h0 : a ≤ ((1149/2000 : ℚ) : ℝ)
  · -- left
    by_cases h1 : a ≤ ((1449/4000 : ℚ) : ℝ)
    · -- left
      by_cases h2 : a ≤ ((2049/8000 : ℚ) : ℝ)
      · -- left
        by_cases h3 : a ≤ ((3249/16000 : ℚ) : ℝ)
        · -- left
          by_cases h4 : a ≤ ((5649/32000 : ℚ) : ℝ)
          · -- left
            by_cases h5 : a ≤ ((10449/64000 : ℚ) : ℝ)
            · -- left
              by_cases h6 : a ≤ ((20049/128000 : ℚ) : ℝ)
              · -- left
                by_cases h7 : a ≤ ((39249/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h8 : a ≤ ((77649/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h9 : a ≤ ((154449/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h10 : a ≤ ((308049/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h11 : a ≤ ((615249/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h12 : a ≤ ((1229649/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h13 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h14 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h15 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1528_pos ha1 h12 hz1 h15 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1530_pos ha1 h12 (not_le.mp h15).le h14 hz
                              · -- right
                                by_cases h16 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1536_pos ha1 h12 (not_le.mp h14).le h16 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1538_pos ha1 h12 (not_le.mp h16).le h13 hz
                            · -- right
                              by_cases h17 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h18 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1560_pos ha1 h12 (not_le.mp h13).le h18 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1562_pos ha1 h12 (not_le.mp h18).le h17 hz
                              · -- right
                                by_cases h19 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1568_pos ha1 h12 (not_le.mp h17).le h19 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1570_pos ha1 h12 (not_le.mp h19).le hz2 hz
                          · -- right
                            by_cases h20 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h21 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h22 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1529_pos (not_le.mp h12).le h11 hz1 h22 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1531_pos (not_le.mp h12).le h11 (not_le.mp h22).le h21 hz
                              · -- right
                                by_cases h23 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1537_pos (not_le.mp h12).le h11 (not_le.mp h21).le h23 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1539_pos (not_le.mp h12).le h11 (not_le.mp h23).le h20 hz
                            · -- right
                              by_cases h24 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h25 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1561_pos (not_le.mp h12).le h11 (not_le.mp h20).le h25 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1563_pos (not_le.mp h12).le h11 (not_le.mp h25).le h24 hz
                              · -- right
                                by_cases h26 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1569_pos (not_le.mp h12).le h11 (not_le.mp h24).le h26 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1571_pos (not_le.mp h12).le h11 (not_le.mp h26).le hz2 hz
                        · -- right
                          by_cases h27 : a ≤ ((1231347/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h28 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h29 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h30 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1532_pos (not_le.mp h11).le h27 hz1 h30 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1534_pos (not_le.mp h11).le h27 (not_le.mp h30).le h29 hz
                              · -- right
                                by_cases h31 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1540_pos (not_le.mp h11).le h27 (not_le.mp h29).le h31 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1542_pos (not_le.mp h11).le h27 (not_le.mp h31).le h28 hz
                            · -- right
                              by_cases h32 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h33 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1564_pos (not_le.mp h11).le h27 (not_le.mp h28).le h33 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1566_pos (not_le.mp h11).le h27 (not_le.mp h33).le h32 hz
                              · -- right
                                by_cases h34 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1572_pos (not_le.mp h11).le h27 (not_le.mp h32).le h34 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1574_pos (not_le.mp h11).le h27 (not_le.mp h34).le hz2 hz
                          · -- right
                            by_cases h35 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h36 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h37 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1533_pos (not_le.mp h27).le h10 hz1 h37 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1535_pos (not_le.mp h27).le h10 (not_le.mp h37).le h36 hz
                              · -- right
                                by_cases h38 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1541_pos (not_le.mp h27).le h10 (not_le.mp h36).le h38 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1543_pos (not_le.mp h27).le h10 (not_le.mp h38).le h35 hz
                            · -- right
                              by_cases h39 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h40 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1565_pos (not_le.mp h27).le h10 (not_le.mp h35).le h40 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1567_pos (not_le.mp h27).le h10 (not_le.mp h40).le h39 hz
                              · -- right
                                by_cases h41 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1573_pos (not_le.mp h27).le h10 (not_le.mp h39).le h41 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1575_pos (not_le.mp h27).le h10 (not_le.mp h41).le hz2 hz
                      · -- right
                        by_cases h42 : a ≤ ((616947/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h43 : a ≤ ((246609/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h44 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h45 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h46 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1544_pos (not_le.mp h10).le h43 hz1 h46 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1546_pos (not_le.mp h10).le h43 (not_le.mp h46).le h45 hz
                              · -- right
                                by_cases h47 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1552_pos (not_le.mp h10).le h43 (not_le.mp h45).le h47 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1554_pos (not_le.mp h10).le h43 (not_le.mp h47).le h44 hz
                            · -- right
                              by_cases h48 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h49 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1576_pos (not_le.mp h10).le h43 (not_le.mp h44).le h49 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1578_pos (not_le.mp h10).le h43 (not_le.mp h49).le h48 hz
                              · -- right
                                by_cases h50 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1584_pos (not_le.mp h10).le h43 (not_le.mp h48).le h50 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1586_pos (not_le.mp h10).le h43 (not_le.mp h50).le hz2 hz
                          · -- right
                            by_cases h51 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h52 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h53 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1545_pos (not_le.mp h43).le h42 hz1 h53 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1547_pos (not_le.mp h43).le h42 (not_le.mp h53).le h52 hz
                              · -- right
                                by_cases h54 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1553_pos (not_le.mp h43).le h42 (not_le.mp h52).le h54 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1555_pos (not_le.mp h43).le h42 (not_le.mp h54).le h51 hz
                            · -- right
                              by_cases h55 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h56 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1577_pos (not_le.mp h43).le h42 (not_le.mp h51).le h56 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1579_pos (not_le.mp h43).le h42 (not_le.mp h56).le h55 hz
                              · -- right
                                by_cases h57 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1585_pos (not_le.mp h43).le h42 (not_le.mp h55).le h57 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1587_pos (not_le.mp h43).le h42 (not_le.mp h57).le hz2 hz
                        · -- right
                          by_cases h58 : a ≤ ((1234743/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h59 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h60 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h61 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1548_pos (not_le.mp h42).le h58 hz1 h61 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1550_pos (not_le.mp h42).le h58 (not_le.mp h61).le h60 hz
                              · -- right
                                by_cases h62 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1556_pos (not_le.mp h42).le h58 (not_le.mp h60).le h62 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1558_pos (not_le.mp h42).le h58 (not_le.mp h62).le h59 hz
                            · -- right
                              by_cases h63 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h64 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1580_pos (not_le.mp h42).le h58 (not_le.mp h59).le h64 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1582_pos (not_le.mp h42).le h58 (not_le.mp h64).le h63 hz
                              · -- right
                                by_cases h65 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1588_pos (not_le.mp h42).le h58 (not_le.mp h63).le h65 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1590_pos (not_le.mp h42).le h58 (not_le.mp h65).le hz2 hz
                          · -- right
                            by_cases h66 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h67 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h68 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1549_pos (not_le.mp h58).le h9 hz1 h68 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1551_pos (not_le.mp h58).le h9 (not_le.mp h68).le h67 hz
                              · -- right
                                by_cases h69 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B025.e1557_pos (not_le.mp h58).le h9 (not_le.mp h67).le h69 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B025.e1559_pos (not_le.mp h58).le h9 (not_le.mp h69).le h66 hz
                            · -- right
                              by_cases h70 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h71 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1581_pos (not_le.mp h58).le h9 (not_le.mp h66).le h71 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1583_pos (not_le.mp h58).le h9 (not_le.mp h71).le h70 hz
                              · -- right
                                by_cases h72 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1589_pos (not_le.mp h58).le h9 (not_le.mp h70).le h72 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1591_pos (not_le.mp h58).le h9 (not_le.mp h72).le hz2 hz
                    · -- right
                      by_cases h73 : a ≤ ((309747/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h74 : a ≤ ((123729/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h75 : a ≤ ((1236441/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h76 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h77 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h78 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1592_pos (not_le.mp h9).le h75 hz1 h78 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1594_pos (not_le.mp h9).le h75 (not_le.mp h78).le h77 hz
                              · -- right
                                by_cases h79 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1600_pos (not_le.mp h9).le h75 (not_le.mp h77).le h79 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1602_pos (not_le.mp h9).le h75 (not_le.mp h79).le h76 hz
                            · -- right
                              by_cases h80 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h81 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1624_pos (not_le.mp h9).le h75 (not_le.mp h76).le h81 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1626_pos (not_le.mp h9).le h75 (not_le.mp h81).le h80 hz
                              · -- right
                                by_cases h82 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1632_pos (not_le.mp h9).le h75 (not_le.mp h80).le h82 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1634_pos (not_le.mp h9).le h75 (not_le.mp h82).le hz2 hz
                          · -- right
                            by_cases h83 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h84 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h85 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1593_pos (not_le.mp h75).le h74 hz1 h85 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1595_pos (not_le.mp h75).le h74 (not_le.mp h85).le h84 hz
                              · -- right
                                by_cases h86 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1601_pos (not_le.mp h75).le h74 (not_le.mp h84).le h86 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1603_pos (not_le.mp h75).le h74 (not_le.mp h86).le h83 hz
                            · -- right
                              by_cases h87 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h88 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1625_pos (not_le.mp h75).le h74 (not_le.mp h83).le h88 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1627_pos (not_le.mp h75).le h74 (not_le.mp h88).le h87 hz
                              · -- right
                                by_cases h89 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1633_pos (not_le.mp h75).le h74 (not_le.mp h87).le h89 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1635_pos (not_le.mp h75).le h74 (not_le.mp h89).le hz2 hz
                        · -- right
                          by_cases h90 : a ≤ ((1238139/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h91 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h92 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h93 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1596_pos (not_le.mp h74).le h90 hz1 h93 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1598_pos (not_le.mp h74).le h90 (not_le.mp h93).le h92 hz
                              · -- right
                                by_cases h94 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1604_pos (not_le.mp h74).le h90 (not_le.mp h92).le h94 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1606_pos (not_le.mp h74).le h90 (not_le.mp h94).le h91 hz
                            · -- right
                              by_cases h95 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h96 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1628_pos (not_le.mp h74).le h90 (not_le.mp h91).le h96 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1630_pos (not_le.mp h74).le h90 (not_le.mp h96).le h95 hz
                              · -- right
                                by_cases h97 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1636_pos (not_le.mp h74).le h90 (not_le.mp h95).le h97 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1638_pos (not_le.mp h74).le h90 (not_le.mp h97).le hz2 hz
                          · -- right
                            by_cases h98 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h99 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h100 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1597_pos (not_le.mp h90).le h73 hz1 h100 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1599_pos (not_le.mp h90).le h73 (not_le.mp h100).le h99 hz
                              · -- right
                                by_cases h101 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1605_pos (not_le.mp h90).le h73 (not_le.mp h99).le h101 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1607_pos (not_le.mp h90).le h73 (not_le.mp h101).le h98 hz
                            · -- right
                              by_cases h102 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h103 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1629_pos (not_le.mp h90).le h73 (not_le.mp h98).le h103 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1631_pos (not_le.mp h90).le h73 (not_le.mp h103).le h102 hz
                              · -- right
                                by_cases h104 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1637_pos (not_le.mp h90).le h73 (not_le.mp h102).le h104 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1639_pos (not_le.mp h90).le h73 (not_le.mp h104).le hz2 hz
                      · -- right
                        by_cases h105 : a ≤ ((620343/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h106 : a ≤ ((1239837/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h107 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h108 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h109 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1608_pos (not_le.mp h73).le h106 hz1 h109 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1610_pos (not_le.mp h73).le h106 (not_le.mp h109).le h108 hz
                              · -- right
                                by_cases h110 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1616_pos (not_le.mp h73).le h106 (not_le.mp h108).le h110 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1618_pos (not_le.mp h73).le h106 (not_le.mp h110).le h107 hz
                            · -- right
                              by_cases h111 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h112 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1640_pos (not_le.mp h73).le h106 (not_le.mp h107).le h112 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1642_pos (not_le.mp h73).le h106 (not_le.mp h112).le h111 hz
                              · -- right
                                by_cases h113 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1648_pos (not_le.mp h73).le h106 (not_le.mp h111).le h113 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1650_pos (not_le.mp h73).le h106 (not_le.mp h113).le hz2 hz
                          · -- right
                            by_cases h114 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h115 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h116 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1609_pos (not_le.mp h106).le h105 hz1 h116 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1611_pos (not_le.mp h106).le h105 (not_le.mp h116).le h115 hz
                              · -- right
                                by_cases h117 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1617_pos (not_le.mp h106).le h105 (not_le.mp h115).le h117 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1619_pos (not_le.mp h106).le h105 (not_le.mp h117).le h114 hz
                            · -- right
                              by_cases h118 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h119 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1641_pos (not_le.mp h106).le h105 (not_le.mp h114).le h119 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1643_pos (not_le.mp h106).le h105 (not_le.mp h119).le h118 hz
                              · -- right
                                by_cases h120 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1649_pos (not_le.mp h106).le h105 (not_le.mp h118).le h120 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1651_pos (not_le.mp h106).le h105 (not_le.mp h120).le hz2 hz
                        · -- right
                          by_cases h121 : a ≤ ((248307/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h122 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h123 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h124 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1612_pos (not_le.mp h105).le h121 hz1 h124 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1614_pos (not_le.mp h105).le h121 (not_le.mp h124).le h123 hz
                              · -- right
                                by_cases h125 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1620_pos (not_le.mp h105).le h121 (not_le.mp h123).le h125 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1622_pos (not_le.mp h105).le h121 (not_le.mp h125).le h122 hz
                            · -- right
                              by_cases h126 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h127 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1644_pos (not_le.mp h105).le h121 (not_le.mp h122).le h127 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1646_pos (not_le.mp h105).le h121 (not_le.mp h127).le h126 hz
                              · -- right
                                by_cases h128 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1652_pos (not_le.mp h105).le h121 (not_le.mp h126).le h128 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1654_pos (not_le.mp h105).le h121 (not_le.mp h128).le hz2 hz
                          · -- right
                            by_cases h129 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h130 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h131 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B026.e1613_pos (not_le.mp h121).le h8 hz1 h131 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B026.e1615_pos (not_le.mp h121).le h8 (not_le.mp h131).le h130 hz
                              · -- right
                                by_cases h132 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1621_pos (not_le.mp h121).le h8 (not_le.mp h130).le h132 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1623_pos (not_le.mp h121).le h8 (not_le.mp h132).le h129 hz
                            · -- right
                              by_cases h133 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h134 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1645_pos (not_le.mp h121).le h8 (not_le.mp h129).le h134 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1647_pos (not_le.mp h121).le h8 (not_le.mp h134).le h133 hz
                              · -- right
                                by_cases h135 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1653_pos (not_le.mp h121).le h8 (not_le.mp h133).le h135 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1655_pos (not_le.mp h121).le h8 (not_le.mp h135).le hz2 hz
                  · -- right
                    by_cases h136 : a ≤ ((156147/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h137 : a ≤ ((62289/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h138 : a ≤ ((622041/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h139 : a ≤ ((1243233/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h140 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h141 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h142 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1656_pos (not_le.mp h8).le h139 hz1 h142 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1658_pos (not_le.mp h8).le h139 (not_le.mp h142).le h141 hz
                              · -- right
                                by_cases h143 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1664_pos (not_le.mp h8).le h139 (not_le.mp h141).le h143 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1666_pos (not_le.mp h8).le h139 (not_le.mp h143).le h140 hz
                            · -- right
                              by_cases h144 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h145 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1688_pos (not_le.mp h8).le h139 (not_le.mp h140).le h145 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1690_pos (not_le.mp h8).le h139 (not_le.mp h145).le h144 hz
                              · -- right
                                by_cases h146 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1696_pos (not_le.mp h8).le h139 (not_le.mp h144).le h146 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1698_pos (not_le.mp h8).le h139 (not_le.mp h146).le hz2 hz
                          · -- right
                            by_cases h147 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h148 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h149 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1657_pos (not_le.mp h139).le h138 hz1 h149 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1659_pos (not_le.mp h139).le h138 (not_le.mp h149).le h148 hz
                              · -- right
                                by_cases h150 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1665_pos (not_le.mp h139).le h138 (not_le.mp h148).le h150 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1667_pos (not_le.mp h139).le h138 (not_le.mp h150).le h147 hz
                            · -- right
                              by_cases h151 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h152 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1689_pos (not_le.mp h139).le h138 (not_le.mp h147).le h152 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1691_pos (not_le.mp h139).le h138 (not_le.mp h152).le h151 hz
                              · -- right
                                by_cases h153 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1697_pos (not_le.mp h139).le h138 (not_le.mp h151).le h153 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1699_pos (not_le.mp h139).le h138 (not_le.mp h153).le hz2 hz
                        · -- right
                          by_cases h154 : a ≤ ((1244931/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h155 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h156 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h157 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1660_pos (not_le.mp h138).le h154 hz1 h157 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1662_pos (not_le.mp h138).le h154 (not_le.mp h157).le h156 hz
                              · -- right
                                by_cases h158 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1668_pos (not_le.mp h138).le h154 (not_le.mp h156).le h158 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1670_pos (not_le.mp h138).le h154 (not_le.mp h158).le h155 hz
                            · -- right
                              by_cases h159 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h160 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1692_pos (not_le.mp h138).le h154 (not_le.mp h155).le h160 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1694_pos (not_le.mp h138).le h154 (not_le.mp h160).le h159 hz
                              · -- right
                                by_cases h161 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1700_pos (not_le.mp h138).le h154 (not_le.mp h159).le h161 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1702_pos (not_le.mp h138).le h154 (not_le.mp h161).le hz2 hz
                          · -- right
                            by_cases h162 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h163 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h164 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1661_pos (not_le.mp h154).le h137 hz1 h164 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1663_pos (not_le.mp h154).le h137 (not_le.mp h164).le h163 hz
                              · -- right
                                by_cases h165 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1669_pos (not_le.mp h154).le h137 (not_le.mp h163).le h165 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1671_pos (not_le.mp h154).le h137 (not_le.mp h165).le h162 hz
                            · -- right
                              by_cases h166 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h167 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1693_pos (not_le.mp h154).le h137 (not_le.mp h162).le h167 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1695_pos (not_le.mp h154).le h137 (not_le.mp h167).le h166 hz
                              · -- right
                                by_cases h168 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1701_pos (not_le.mp h154).le h137 (not_le.mp h166).le h168 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1703_pos (not_le.mp h154).le h137 (not_le.mp h168).le hz2 hz
                      · -- right
                        by_cases h169 : a ≤ ((623739/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h170 : a ≤ ((1246629/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h171 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h172 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h173 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1672_pos (not_le.mp h137).le h170 hz1 h173 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1674_pos (not_le.mp h137).le h170 (not_le.mp h173).le h172 hz
                              · -- right
                                by_cases h174 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1680_pos (not_le.mp h137).le h170 (not_le.mp h172).le h174 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1682_pos (not_le.mp h137).le h170 (not_le.mp h174).le h171 hz
                            · -- right
                              by_cases h175 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h176 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1704_pos (not_le.mp h137).le h170 (not_le.mp h171).le h176 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1706_pos (not_le.mp h137).le h170 (not_le.mp h176).le h175 hz
                              · -- right
                                by_cases h177 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1712_pos (not_le.mp h137).le h170 (not_le.mp h175).le h177 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1714_pos (not_le.mp h137).le h170 (not_le.mp h177).le hz2 hz
                          · -- right
                            by_cases h178 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h179 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h180 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1673_pos (not_le.mp h170).le h169 hz1 h180 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1675_pos (not_le.mp h170).le h169 (not_le.mp h180).le h179 hz
                              · -- right
                                by_cases h181 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1681_pos (not_le.mp h170).le h169 (not_le.mp h179).le h181 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1683_pos (not_le.mp h170).le h169 (not_le.mp h181).le h178 hz
                            · -- right
                              by_cases h182 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h183 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1705_pos (not_le.mp h170).le h169 (not_le.mp h178).le h183 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1707_pos (not_le.mp h170).le h169 (not_le.mp h183).le h182 hz
                              · -- right
                                by_cases h184 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1713_pos (not_le.mp h170).le h169 (not_le.mp h182).le h184 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1715_pos (not_le.mp h170).le h169 (not_le.mp h184).le hz2 hz
                        · -- right
                          by_cases h185 : a ≤ ((1248327/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h186 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h187 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h188 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1676_pos (not_le.mp h169).le h185 hz1 h188 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1678_pos (not_le.mp h169).le h185 (not_le.mp h188).le h187 hz
                              · -- right
                                by_cases h189 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1684_pos (not_le.mp h169).le h185 (not_le.mp h187).le h189 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1686_pos (not_le.mp h169).le h185 (not_le.mp h189).le h186 hz
                            · -- right
                              by_cases h190 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h191 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1708_pos (not_le.mp h169).le h185 (not_le.mp h186).le h191 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1710_pos (not_le.mp h169).le h185 (not_le.mp h191).le h190 hz
                              · -- right
                                by_cases h192 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1716_pos (not_le.mp h169).le h185 (not_le.mp h190).le h192 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1718_pos (not_le.mp h169).le h185 (not_le.mp h192).le hz2 hz
                          · -- right
                            by_cases h193 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h194 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h195 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B027.e1677_pos (not_le.mp h185).le h136 hz1 h195 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B027.e1679_pos (not_le.mp h185).le h136 (not_le.mp h195).le h194 hz
                              · -- right
                                by_cases h196 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1685_pos (not_le.mp h185).le h136 (not_le.mp h194).le h196 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1687_pos (not_le.mp h185).le h136 (not_le.mp h196).le h193 hz
                            · -- right
                              by_cases h197 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h198 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1709_pos (not_le.mp h185).le h136 (not_le.mp h193).le h198 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1711_pos (not_le.mp h185).le h136 (not_le.mp h198).le h197 hz
                              · -- right
                                by_cases h199 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1717_pos (not_le.mp h185).le h136 (not_le.mp h197).le h199 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1719_pos (not_le.mp h185).le h136 (not_le.mp h199).le hz2 hz
                    · -- right
                      by_cases h200 : a ≤ ((313143/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h201 : a ≤ ((625437/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h202 : a ≤ ((50001/327680 : ℚ) : ℝ)
                          · -- left
                            by_cases h203 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h204 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h205 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1720_pos (not_le.mp h136).le h202 hz1 h205 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1722_pos (not_le.mp h136).le h202 (not_le.mp h205).le h204 hz
                              · -- right
                                by_cases h206 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1728_pos (not_le.mp h136).le h202 (not_le.mp h204).le h206 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1730_pos (not_le.mp h136).le h202 (not_le.mp h206).le h203 hz
                            · -- right
                              by_cases h207 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h208 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1752_pos (not_le.mp h136).le h202 (not_le.mp h203).le h208 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1754_pos (not_le.mp h136).le h202 (not_le.mp h208).le h207 hz
                              · -- right
                                by_cases h209 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1760_pos (not_le.mp h136).le h202 (not_le.mp h207).le h209 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1762_pos (not_le.mp h136).le h202 (not_le.mp h209).le hz2 hz
                          · -- right
                            by_cases h210 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h211 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h212 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1721_pos (not_le.mp h202).le h201 hz1 h212 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1723_pos (not_le.mp h202).le h201 (not_le.mp h212).le h211 hz
                              · -- right
                                by_cases h213 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1729_pos (not_le.mp h202).le h201 (not_le.mp h211).le h213 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1731_pos (not_le.mp h202).le h201 (not_le.mp h213).le h210 hz
                            · -- right
                              by_cases h214 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h215 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1753_pos (not_le.mp h202).le h201 (not_le.mp h210).le h215 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1755_pos (not_le.mp h202).le h201 (not_le.mp h215).le h214 hz
                              · -- right
                                by_cases h216 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1761_pos (not_le.mp h202).le h201 (not_le.mp h214).le h216 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1763_pos (not_le.mp h202).le h201 (not_le.mp h216).le hz2 hz
                        · -- right
                          by_cases h217 : a ≤ ((1251723/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h218 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h219 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h220 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1724_pos (not_le.mp h201).le h217 hz1 h220 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1726_pos (not_le.mp h201).le h217 (not_le.mp h220).le h219 hz
                              · -- right
                                by_cases h221 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1732_pos (not_le.mp h201).le h217 (not_le.mp h219).le h221 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1734_pos (not_le.mp h201).le h217 (not_le.mp h221).le h218 hz
                            · -- right
                              by_cases h222 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h223 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1756_pos (not_le.mp h201).le h217 (not_le.mp h218).le h223 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1758_pos (not_le.mp h201).le h217 (not_le.mp h223).le h222 hz
                              · -- right
                                by_cases h224 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1764_pos (not_le.mp h201).le h217 (not_le.mp h222).le h224 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1766_pos (not_le.mp h201).le h217 (not_le.mp h224).le hz2 hz
                          · -- right
                            by_cases h225 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h226 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h227 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1725_pos (not_le.mp h217).le h200 hz1 h227 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1727_pos (not_le.mp h217).le h200 (not_le.mp h227).le h226 hz
                              · -- right
                                by_cases h228 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1733_pos (not_le.mp h217).le h200 (not_le.mp h226).le h228 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1735_pos (not_le.mp h217).le h200 (not_le.mp h228).le h225 hz
                            · -- right
                              by_cases h229 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h230 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1757_pos (not_le.mp h217).le h200 (not_le.mp h225).le h230 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1759_pos (not_le.mp h217).le h200 (not_le.mp h230).le h229 hz
                              · -- right
                                by_cases h231 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1765_pos (not_le.mp h217).le h200 (not_le.mp h229).le h231 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1767_pos (not_le.mp h217).le h200 (not_le.mp h231).le hz2 hz
                      · -- right
                        by_cases h232 : a ≤ ((125427/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h233 : a ≤ ((1253421/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h234 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h235 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h236 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1736_pos (not_le.mp h200).le h233 hz1 h236 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1738_pos (not_le.mp h200).le h233 (not_le.mp h236).le h235 hz
                              · -- right
                                by_cases h237 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1744_pos (not_le.mp h200).le h233 (not_le.mp h235).le h237 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1746_pos (not_le.mp h200).le h233 (not_le.mp h237).le h234 hz
                            · -- right
                              by_cases h238 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h239 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1768_pos (not_le.mp h200).le h233 (not_le.mp h234).le h239 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1770_pos (not_le.mp h200).le h233 (not_le.mp h239).le h238 hz
                              · -- right
                                by_cases h240 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1776_pos (not_le.mp h200).le h233 (not_le.mp h238).le h240 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1778_pos (not_le.mp h200).le h233 (not_le.mp h240).le hz2 hz
                          · -- right
                            by_cases h241 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h242 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h243 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B028.e1737_pos (not_le.mp h233).le h232 hz1 h243 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B028.e1739_pos (not_le.mp h233).le h232 (not_le.mp h243).le h242 hz
                              · -- right
                                by_cases h244 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1745_pos (not_le.mp h233).le h232 (not_le.mp h242).le h244 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1747_pos (not_le.mp h233).le h232 (not_le.mp h244).le h241 hz
                            · -- right
                              by_cases h245 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h246 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1769_pos (not_le.mp h233).le h232 (not_le.mp h241).le h246 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1771_pos (not_le.mp h233).le h232 (not_le.mp h246).le h245 hz
                              · -- right
                                by_cases h247 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1777_pos (not_le.mp h233).le h232 (not_le.mp h245).le h247 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1779_pos (not_le.mp h233).le h232 (not_le.mp h247).le hz2 hz
                        · -- right
                          by_cases h248 : a ≤ ((1255119/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h249 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h250 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h251 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1740_pos (not_le.mp h232).le h248 hz1 h251 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1742_pos (not_le.mp h232).le h248 (not_le.mp h251).le h250 hz
                              · -- right
                                by_cases h252 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1748_pos (not_le.mp h232).le h248 (not_le.mp h250).le h252 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1750_pos (not_le.mp h232).le h248 (not_le.mp h252).le h249 hz
                            · -- right
                              by_cases h253 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h254 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1772_pos (not_le.mp h232).le h248 (not_le.mp h249).le h254 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1774_pos (not_le.mp h232).le h248 (not_le.mp h254).le h253 hz
                              · -- right
                                by_cases h255 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1780_pos (not_le.mp h232).le h248 (not_le.mp h253).le h255 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1782_pos (not_le.mp h232).le h248 (not_le.mp h255).le hz2 hz
                          · -- right
                            by_cases h256 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h257 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h258 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1741_pos (not_le.mp h248).le h7 hz1 h258 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1743_pos (not_le.mp h248).le h7 (not_le.mp h258).le h257 hz
                              · -- right
                                by_cases h259 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1749_pos (not_le.mp h248).le h7 (not_le.mp h257).le h259 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1751_pos (not_le.mp h248).le h7 (not_le.mp h259).le h256 hz
                            · -- right
                              by_cases h260 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h261 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1773_pos (not_le.mp h248).le h7 (not_le.mp h256).le h261 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1775_pos (not_le.mp h248).le h7 (not_le.mp h261).le h260 hz
                              · -- right
                                by_cases h262 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1781_pos (not_le.mp h248).le h7 (not_le.mp h260).le h262 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1783_pos (not_le.mp h248).le h7 (not_le.mp h262).le hz2 hz
                · -- right
                  by_cases h263 : a ≤ ((79347/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h264 : a ≤ ((31569/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h265 : a ≤ ((314841/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h266 : a ≤ ((628833/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h267 : a ≤ ((1256817/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h268 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h269 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h270 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1784_pos (not_le.mp h7).le h267 hz1 h270 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1786_pos (not_le.mp h7).le h267 (not_le.mp h270).le h269 hz
                              · -- right
                                by_cases h271 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1792_pos (not_le.mp h7).le h267 (not_le.mp h269).le h271 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1794_pos (not_le.mp h7).le h267 (not_le.mp h271).le h268 hz
                            · -- right
                              by_cases h272 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h273 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1816_pos (not_le.mp h7).le h267 (not_le.mp h268).le h273 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1818_pos (not_le.mp h7).le h267 (not_le.mp h273).le h272 hz
                              · -- right
                                by_cases h274 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1824_pos (not_le.mp h7).le h267 (not_le.mp h272).le h274 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1826_pos (not_le.mp h7).le h267 (not_le.mp h274).le hz2 hz
                          · -- right
                            by_cases h275 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h276 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h277 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1785_pos (not_le.mp h267).le h266 hz1 h277 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1787_pos (not_le.mp h267).le h266 (not_le.mp h277).le h276 hz
                              · -- right
                                by_cases h278 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1793_pos (not_le.mp h267).le h266 (not_le.mp h276).le h278 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1795_pos (not_le.mp h267).le h266 (not_le.mp h278).le h275 hz
                            · -- right
                              by_cases h279 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h280 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1817_pos (not_le.mp h267).le h266 (not_le.mp h275).le h280 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1819_pos (not_le.mp h267).le h266 (not_le.mp h280).le h279 hz
                              · -- right
                                by_cases h281 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1825_pos (not_le.mp h267).le h266 (not_le.mp h279).le h281 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1827_pos (not_le.mp h267).le h266 (not_le.mp h281).le hz2 hz
                        · -- right
                          by_cases h282 : a ≤ ((251703/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h283 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h284 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h285 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1788_pos (not_le.mp h266).le h282 hz1 h285 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1790_pos (not_le.mp h266).le h282 (not_le.mp h285).le h284 hz
                              · -- right
                                by_cases h286 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1796_pos (not_le.mp h266).le h282 (not_le.mp h284).le h286 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1798_pos (not_le.mp h266).le h282 (not_le.mp h286).le h283 hz
                            · -- right
                              by_cases h287 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h288 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1820_pos (not_le.mp h266).le h282 (not_le.mp h283).le h288 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1822_pos (not_le.mp h266).le h282 (not_le.mp h288).le h287 hz
                              · -- right
                                by_cases h289 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1828_pos (not_le.mp h266).le h282 (not_le.mp h287).le h289 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1830_pos (not_le.mp h266).le h282 (not_le.mp h289).le hz2 hz
                          · -- right
                            by_cases h290 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h291 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h292 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1789_pos (not_le.mp h282).le h265 hz1 h292 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1791_pos (not_le.mp h282).le h265 (not_le.mp h292).le h291 hz
                              · -- right
                                by_cases h293 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B029.e1797_pos (not_le.mp h282).le h265 (not_le.mp h291).le h293 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B029.e1799_pos (not_le.mp h282).le h265 (not_le.mp h293).le h290 hz
                            · -- right
                              by_cases h294 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h295 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1821_pos (not_le.mp h282).le h265 (not_le.mp h290).le h295 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1823_pos (not_le.mp h282).le h265 (not_le.mp h295).le h294 hz
                              · -- right
                                by_cases h296 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1829_pos (not_le.mp h282).le h265 (not_le.mp h294).le h296 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1831_pos (not_le.mp h282).le h265 (not_le.mp h296).le hz2 hz
                      · -- right
                        by_cases h297 : a ≤ ((630531/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h298 : a ≤ ((1260213/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h299 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h300 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h301 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1800_pos (not_le.mp h265).le h298 hz1 h301 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1802_pos (not_le.mp h265).le h298 (not_le.mp h301).le h300 hz
                              · -- right
                                by_cases h302 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1808_pos (not_le.mp h265).le h298 (not_le.mp h300).le h302 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1810_pos (not_le.mp h265).le h298 (not_le.mp h302).le h299 hz
                            · -- right
                              by_cases h303 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h304 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1832_pos (not_le.mp h265).le h298 (not_le.mp h299).le h304 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1834_pos (not_le.mp h265).le h298 (not_le.mp h304).le h303 hz
                              · -- right
                                by_cases h305 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1840_pos (not_le.mp h265).le h298 (not_le.mp h303).le h305 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1842_pos (not_le.mp h265).le h298 (not_le.mp h305).le hz2 hz
                          · -- right
                            by_cases h306 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h307 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h308 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1801_pos (not_le.mp h298).le h297 hz1 h308 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1803_pos (not_le.mp h298).le h297 (not_le.mp h308).le h307 hz
                              · -- right
                                by_cases h309 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1809_pos (not_le.mp h298).le h297 (not_le.mp h307).le h309 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1811_pos (not_le.mp h298).le h297 (not_le.mp h309).le h306 hz
                            · -- right
                              by_cases h310 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h311 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1833_pos (not_le.mp h298).le h297 (not_le.mp h306).le h311 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1835_pos (not_le.mp h298).le h297 (not_le.mp h311).le h310 hz
                              · -- right
                                by_cases h312 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1841_pos (not_le.mp h298).le h297 (not_le.mp h310).le h312 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1843_pos (not_le.mp h298).le h297 (not_le.mp h312).le hz2 hz
                        · -- right
                          by_cases h313 : a ≤ ((1261911/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h314 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h315 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h316 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1804_pos (not_le.mp h297).le h313 hz1 h316 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1806_pos (not_le.mp h297).le h313 (not_le.mp h316).le h315 hz
                              · -- right
                                by_cases h317 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1812_pos (not_le.mp h297).le h313 (not_le.mp h315).le h317 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1814_pos (not_le.mp h297).le h313 (not_le.mp h317).le h314 hz
                            · -- right
                              by_cases h318 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h319 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1836_pos (not_le.mp h297).le h313 (not_le.mp h314).le h319 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1838_pos (not_le.mp h297).le h313 (not_le.mp h319).le h318 hz
                              · -- right
                                by_cases h320 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1844_pos (not_le.mp h297).le h313 (not_le.mp h318).le h320 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1846_pos (not_le.mp h297).le h313 (not_le.mp h320).le hz2 hz
                          · -- right
                            by_cases h321 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h322 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h323 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1805_pos (not_le.mp h313).le h264 hz1 h323 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1807_pos (not_le.mp h313).le h264 (not_le.mp h323).le h322 hz
                              · -- right
                                by_cases h324 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1813_pos (not_le.mp h313).le h264 (not_le.mp h322).le h324 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1815_pos (not_le.mp h313).le h264 (not_le.mp h324).le h321 hz
                            · -- right
                              by_cases h325 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h326 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1837_pos (not_le.mp h313).le h264 (not_le.mp h321).le h326 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1839_pos (not_le.mp h313).le h264 (not_le.mp h326).le h325 hz
                              · -- right
                                by_cases h327 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1845_pos (not_le.mp h313).le h264 (not_le.mp h325).le h327 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1847_pos (not_le.mp h313).le h264 (not_le.mp h327).le hz2 hz
                    · -- right
                      by_cases h328 : a ≤ ((316539/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h329 : a ≤ ((632229/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h330 : a ≤ ((1263609/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h331 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h332 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h333 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1848_pos (not_le.mp h264).le h330 hz1 h333 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1850_pos (not_le.mp h264).le h330 (not_le.mp h333).le h332 hz
                              · -- right
                                by_cases h334 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1856_pos (not_le.mp h264).le h330 (not_le.mp h332).le h334 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1858_pos (not_le.mp h264).le h330 (not_le.mp h334).le h331 hz
                            · -- right
                              by_cases h335 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h336 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1880_pos (not_le.mp h264).le h330 (not_le.mp h331).le h336 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1882_pos (not_le.mp h264).le h330 (not_le.mp h336).le h335 hz
                              · -- right
                                by_cases h337 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1888_pos (not_le.mp h264).le h330 (not_le.mp h335).le h337 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1890_pos (not_le.mp h264).le h330 (not_le.mp h337).le hz2 hz
                          · -- right
                            by_cases h338 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h339 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h340 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1849_pos (not_le.mp h330).le h329 hz1 h340 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1851_pos (not_le.mp h330).le h329 (not_le.mp h340).le h339 hz
                              · -- right
                                by_cases h341 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1857_pos (not_le.mp h330).le h329 (not_le.mp h339).le h341 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1859_pos (not_le.mp h330).le h329 (not_le.mp h341).le h338 hz
                            · -- right
                              by_cases h342 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h343 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1881_pos (not_le.mp h330).le h329 (not_le.mp h338).le h343 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1883_pos (not_le.mp h330).le h329 (not_le.mp h343).le h342 hz
                              · -- right
                                by_cases h344 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1889_pos (not_le.mp h330).le h329 (not_le.mp h342).le h344 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1891_pos (not_le.mp h330).le h329 (not_le.mp h344).le hz2 hz
                        · -- right
                          by_cases h345 : a ≤ ((1265307/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h346 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h347 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h348 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1852_pos (not_le.mp h329).le h345 hz1 h348 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1854_pos (not_le.mp h329).le h345 (not_le.mp h348).le h347 hz
                              · -- right
                                by_cases h349 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1860_pos (not_le.mp h329).le h345 (not_le.mp h347).le h349 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1862_pos (not_le.mp h329).le h345 (not_le.mp h349).le h346 hz
                            · -- right
                              by_cases h350 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h351 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1884_pos (not_le.mp h329).le h345 (not_le.mp h346).le h351 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1886_pos (not_le.mp h329).le h345 (not_le.mp h351).le h350 hz
                              · -- right
                                by_cases h352 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1892_pos (not_le.mp h329).le h345 (not_le.mp h350).le h352 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1894_pos (not_le.mp h329).le h345 (not_le.mp h352).le hz2 hz
                          · -- right
                            by_cases h353 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h354 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h355 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B030.e1853_pos (not_le.mp h345).le h328 hz1 h355 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B030.e1855_pos (not_le.mp h345).le h328 (not_le.mp h355).le h354 hz
                              · -- right
                                by_cases h356 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1861_pos (not_le.mp h345).le h328 (not_le.mp h354).le h356 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1863_pos (not_le.mp h345).le h328 (not_le.mp h356).le h353 hz
                            · -- right
                              by_cases h357 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h358 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1885_pos (not_le.mp h345).le h328 (not_le.mp h353).le h358 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1887_pos (not_le.mp h345).le h328 (not_le.mp h358).le h357 hz
                              · -- right
                                by_cases h359 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1893_pos (not_le.mp h345).le h328 (not_le.mp h357).le h359 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1895_pos (not_le.mp h345).le h328 (not_le.mp h359).le hz2 hz
                      · -- right
                        by_cases h360 : a ≤ ((633927/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h361 : a ≤ ((253401/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h362 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h363 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h364 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1864_pos (not_le.mp h328).le h361 hz1 h364 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1866_pos (not_le.mp h328).le h361 (not_le.mp h364).le h363 hz
                              · -- right
                                by_cases h365 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1872_pos (not_le.mp h328).le h361 (not_le.mp h363).le h365 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1874_pos (not_le.mp h328).le h361 (not_le.mp h365).le h362 hz
                            · -- right
                              by_cases h366 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h367 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1896_pos (not_le.mp h328).le h361 (not_le.mp h362).le h367 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1898_pos (not_le.mp h328).le h361 (not_le.mp h367).le h366 hz
                              · -- right
                                by_cases h368 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1904_pos (not_le.mp h328).le h361 (not_le.mp h366).le h368 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1906_pos (not_le.mp h328).le h361 (not_le.mp h368).le hz2 hz
                          · -- right
                            by_cases h369 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h370 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h371 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1865_pos (not_le.mp h361).le h360 hz1 h371 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1867_pos (not_le.mp h361).le h360 (not_le.mp h371).le h370 hz
                              · -- right
                                by_cases h372 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1873_pos (not_le.mp h361).le h360 (not_le.mp h370).le h372 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1875_pos (not_le.mp h361).le h360 (not_le.mp h372).le h369 hz
                            · -- right
                              by_cases h373 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h374 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1897_pos (not_le.mp h361).le h360 (not_le.mp h369).le h374 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1899_pos (not_le.mp h361).le h360 (not_le.mp h374).le h373 hz
                              · -- right
                                by_cases h375 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1905_pos (not_le.mp h361).le h360 (not_le.mp h373).le h375 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1907_pos (not_le.mp h361).le h360 (not_le.mp h375).le hz2 hz
                        · -- right
                          by_cases h376 : a ≤ ((1268703/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h377 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h378 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h379 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1868_pos (not_le.mp h360).le h376 hz1 h379 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1870_pos (not_le.mp h360).le h376 (not_le.mp h379).le h378 hz
                              · -- right
                                by_cases h380 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1876_pos (not_le.mp h360).le h376 (not_le.mp h378).le h380 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1878_pos (not_le.mp h360).le h376 (not_le.mp h380).le h377 hz
                            · -- right
                              by_cases h381 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h382 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1900_pos (not_le.mp h360).le h376 (not_le.mp h377).le h382 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1902_pos (not_le.mp h360).le h376 (not_le.mp h382).le h381 hz
                              · -- right
                                by_cases h383 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1908_pos (not_le.mp h360).le h376 (not_le.mp h381).le h383 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1910_pos (not_le.mp h360).le h376 (not_le.mp h383).le hz2 hz
                          · -- right
                            by_cases h384 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h385 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h386 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1869_pos (not_le.mp h376).le h263 hz1 h386 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1871_pos (not_le.mp h376).le h263 (not_le.mp h386).le h385 hz
                              · -- right
                                by_cases h387 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1877_pos (not_le.mp h376).le h263 (not_le.mp h385).le h387 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1879_pos (not_le.mp h376).le h263 (not_le.mp h387).le h384 hz
                            · -- right
                              by_cases h388 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h389 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1901_pos (not_le.mp h376).le h263 (not_le.mp h384).le h389 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1903_pos (not_le.mp h376).le h263 (not_le.mp h389).le h388 hz
                              · -- right
                                by_cases h390 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1909_pos (not_le.mp h376).le h263 (not_le.mp h388).le h390 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1911_pos (not_le.mp h376).le h263 (not_le.mp h390).le hz2 hz
                  · -- right
                    by_cases h391 : a ≤ ((159543/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h392 : a ≤ ((318237/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h393 : a ≤ ((5085/32768 : ℚ) : ℝ)
                        · -- left
                          by_cases h394 : a ≤ ((1270401/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h395 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h396 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h397 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1912_pos (not_le.mp h263).le h394 hz1 h397 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1914_pos (not_le.mp h263).le h394 (not_le.mp h397).le h396 hz
                              · -- right
                                by_cases h398 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1920_pos (not_le.mp h263).le h394 (not_le.mp h396).le h398 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1922_pos (not_le.mp h263).le h394 (not_le.mp h398).le h395 hz
                            · -- right
                              by_cases h399 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h400 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1944_pos (not_le.mp h263).le h394 (not_le.mp h395).le h400 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1946_pos (not_le.mp h263).le h394 (not_le.mp h400).le h399 hz
                              · -- right
                                by_cases h401 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1952_pos (not_le.mp h263).le h394 (not_le.mp h399).le h401 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1954_pos (not_le.mp h263).le h394 (not_le.mp h401).le hz2 hz
                          · -- right
                            by_cases h402 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h403 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h404 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1913_pos (not_le.mp h394).le h393 hz1 h404 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1915_pos (not_le.mp h394).le h393 (not_le.mp h404).le h403 hz
                              · -- right
                                by_cases h405 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1921_pos (not_le.mp h394).le h393 (not_le.mp h403).le h405 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1923_pos (not_le.mp h394).le h393 (not_le.mp h405).le h402 hz
                            · -- right
                              by_cases h406 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h407 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1945_pos (not_le.mp h394).le h393 (not_le.mp h402).le h407 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1947_pos (not_le.mp h394).le h393 (not_le.mp h407).le h406 hz
                              · -- right
                                by_cases h408 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1953_pos (not_le.mp h394).le h393 (not_le.mp h406).le h408 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1955_pos (not_le.mp h394).le h393 (not_le.mp h408).le hz2 hz
                        · -- right
                          by_cases h409 : a ≤ ((1272099/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h410 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h411 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h412 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1916_pos (not_le.mp h393).le h409 hz1 h412 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1918_pos (not_le.mp h393).le h409 (not_le.mp h412).le h411 hz
                              · -- right
                                by_cases h413 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1924_pos (not_le.mp h393).le h409 (not_le.mp h411).le h413 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1926_pos (not_le.mp h393).le h409 (not_le.mp h413).le h410 hz
                            · -- right
                              by_cases h414 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h415 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1948_pos (not_le.mp h393).le h409 (not_le.mp h410).le h415 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1950_pos (not_le.mp h393).le h409 (not_le.mp h415).le h414 hz
                              · -- right
                                by_cases h416 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1956_pos (not_le.mp h393).le h409 (not_le.mp h414).le h416 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1958_pos (not_le.mp h393).le h409 (not_le.mp h416).le hz2 hz
                          · -- right
                            by_cases h417 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h418 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h419 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B031.e1917_pos (not_le.mp h409).le h392 hz1 h419 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B031.e1919_pos (not_le.mp h409).le h392 (not_le.mp h419).le h418 hz
                              · -- right
                                by_cases h420 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1925_pos (not_le.mp h409).le h392 (not_le.mp h418).le h420 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1927_pos (not_le.mp h409).le h392 (not_le.mp h420).le h417 hz
                            · -- right
                              by_cases h421 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h422 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1949_pos (not_le.mp h409).le h392 (not_le.mp h417).le h422 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1951_pos (not_le.mp h409).le h392 (not_le.mp h422).le h421 hz
                              · -- right
                                by_cases h423 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1957_pos (not_le.mp h409).le h392 (not_le.mp h421).le h423 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1959_pos (not_le.mp h409).le h392 (not_le.mp h423).le hz2 hz
                      · -- right
                        by_cases h424 : a ≤ ((637323/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h425 : a ≤ ((1273797/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h426 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h427 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h428 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1928_pos (not_le.mp h392).le h425 hz1 h428 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1930_pos (not_le.mp h392).le h425 (not_le.mp h428).le h427 hz
                              · -- right
                                by_cases h429 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1936_pos (not_le.mp h392).le h425 (not_le.mp h427).le h429 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1938_pos (not_le.mp h392).le h425 (not_le.mp h429).le h426 hz
                            · -- right
                              by_cases h430 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h431 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1960_pos (not_le.mp h392).le h425 (not_le.mp h426).le h431 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1962_pos (not_le.mp h392).le h425 (not_le.mp h431).le h430 hz
                              · -- right
                                by_cases h432 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1968_pos (not_le.mp h392).le h425 (not_le.mp h430).le h432 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1970_pos (not_le.mp h392).le h425 (not_le.mp h432).le hz2 hz
                          · -- right
                            by_cases h433 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h434 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h435 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1929_pos (not_le.mp h425).le h424 hz1 h435 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1931_pos (not_le.mp h425).le h424 (not_le.mp h435).le h434 hz
                              · -- right
                                by_cases h436 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1937_pos (not_le.mp h425).le h424 (not_le.mp h434).le h436 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1939_pos (not_le.mp h425).le h424 (not_le.mp h436).le h433 hz
                            · -- right
                              by_cases h437 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h438 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1961_pos (not_le.mp h425).le h424 (not_le.mp h433).le h438 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1963_pos (not_le.mp h425).le h424 (not_le.mp h438).le h437 hz
                              · -- right
                                by_cases h439 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1969_pos (not_le.mp h425).le h424 (not_le.mp h437).le h439 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1971_pos (not_le.mp h425).le h424 (not_le.mp h439).le hz2 hz
                        · -- right
                          by_cases h440 : a ≤ ((255099/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h441 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h442 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h443 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1932_pos (not_le.mp h424).le h440 hz1 h443 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1934_pos (not_le.mp h424).le h440 (not_le.mp h443).le h442 hz
                              · -- right
                                by_cases h444 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1940_pos (not_le.mp h424).le h440 (not_le.mp h442).le h444 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1942_pos (not_le.mp h424).le h440 (not_le.mp h444).le h441 hz
                            · -- right
                              by_cases h445 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h446 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1964_pos (not_le.mp h424).le h440 (not_le.mp h441).le h446 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1966_pos (not_le.mp h424).le h440 (not_le.mp h446).le h445 hz
                              · -- right
                                by_cases h447 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1972_pos (not_le.mp h424).le h440 (not_le.mp h445).le h447 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1974_pos (not_le.mp h424).le h440 (not_le.mp h447).le hz2 hz
                          · -- right
                            by_cases h448 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h449 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h450 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1933_pos (not_le.mp h440).le h391 hz1 h450 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1935_pos (not_le.mp h440).le h391 (not_le.mp h450).le h449 hz
                              · -- right
                                by_cases h451 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1941_pos (not_le.mp h440).le h391 (not_le.mp h449).le h451 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1943_pos (not_le.mp h440).le h391 (not_le.mp h451).le h448 hz
                            · -- right
                              by_cases h452 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h453 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1965_pos (not_le.mp h440).le h391 (not_le.mp h448).le h453 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1967_pos (not_le.mp h440).le h391 (not_le.mp h453).le h452 hz
                              · -- right
                                by_cases h454 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1973_pos (not_le.mp h440).le h391 (not_le.mp h452).le h454 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1975_pos (not_le.mp h440).le h391 (not_le.mp h454).le hz2 hz
                    · -- right
                      by_cases h455 : a ≤ ((63987/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h456 : a ≤ ((639021/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h457 : a ≤ ((1277193/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h458 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h459 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h460 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1976_pos (not_le.mp h391).le h457 hz1 h460 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1978_pos (not_le.mp h391).le h457 (not_le.mp h460).le h459 hz
                              · -- right
                                by_cases h461 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1984_pos (not_le.mp h391).le h457 (not_le.mp h459).le h461 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1986_pos (not_le.mp h391).le h457 (not_le.mp h461).le h458 hz
                            · -- right
                              by_cases h462 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h463 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2008_pos (not_le.mp h391).le h457 (not_le.mp h458).le h463 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2010_pos (not_le.mp h391).le h457 (not_le.mp h463).le h462 hz
                              · -- right
                                by_cases h464 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2016_pos (not_le.mp h391).le h457 (not_le.mp h462).le h464 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2018_pos (not_le.mp h391).le h457 (not_le.mp h464).le hz2 hz
                          · -- right
                            by_cases h465 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h466 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h467 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B032.e1977_pos (not_le.mp h457).le h456 hz1 h467 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B032.e1979_pos (not_le.mp h457).le h456 (not_le.mp h467).le h466 hz
                              · -- right
                                by_cases h468 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1985_pos (not_le.mp h457).le h456 (not_le.mp h466).le h468 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1987_pos (not_le.mp h457).le h456 (not_le.mp h468).le h465 hz
                            · -- right
                              by_cases h469 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h470 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2009_pos (not_le.mp h457).le h456 (not_le.mp h465).le h470 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2011_pos (not_le.mp h457).le h456 (not_le.mp h470).le h469 hz
                              · -- right
                                by_cases h471 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2017_pos (not_le.mp h457).le h456 (not_le.mp h469).le h471 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2019_pos (not_le.mp h457).le h456 (not_le.mp h471).le hz2 hz
                        · -- right
                          by_cases h472 : a ≤ ((1278891/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h473 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h474 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h475 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1980_pos (not_le.mp h456).le h472 hz1 h475 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1982_pos (not_le.mp h456).le h472 (not_le.mp h475).le h474 hz
                              · -- right
                                by_cases h476 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1988_pos (not_le.mp h456).le h472 (not_le.mp h474).le h476 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1990_pos (not_le.mp h456).le h472 (not_le.mp h476).le h473 hz
                            · -- right
                              by_cases h477 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h478 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2012_pos (not_le.mp h456).le h472 (not_le.mp h473).le h478 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2014_pos (not_le.mp h456).le h472 (not_le.mp h478).le h477 hz
                              · -- right
                                by_cases h479 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2020_pos (not_le.mp h456).le h472 (not_le.mp h477).le h479 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2022_pos (not_le.mp h456).le h472 (not_le.mp h479).le hz2 hz
                          · -- right
                            by_cases h480 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h481 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h482 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1981_pos (not_le.mp h472).le h455 hz1 h482 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1983_pos (not_le.mp h472).le h455 (not_le.mp h482).le h481 hz
                              · -- right
                                by_cases h483 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1989_pos (not_le.mp h472).le h455 (not_le.mp h481).le h483 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1991_pos (not_le.mp h472).le h455 (not_le.mp h483).le h480 hz
                            · -- right
                              by_cases h484 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h485 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2013_pos (not_le.mp h472).le h455 (not_le.mp h480).le h485 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2015_pos (not_le.mp h472).le h455 (not_le.mp h485).le h484 hz
                              · -- right
                                by_cases h486 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2021_pos (not_le.mp h472).le h455 (not_le.mp h484).le h486 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2023_pos (not_le.mp h472).le h455 (not_le.mp h486).le hz2 hz
                      · -- right
                        by_cases h487 : a ≤ ((640719/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h488 : a ≤ ((1280589/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h489 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h490 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h491 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1992_pos (not_le.mp h455).le h488 hz1 h491 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1994_pos (not_le.mp h455).le h488 (not_le.mp h491).le h490 hz
                              · -- right
                                by_cases h492 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2000_pos (not_le.mp h455).le h488 (not_le.mp h490).le h492 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2002_pos (not_le.mp h455).le h488 (not_le.mp h492).le h489 hz
                            · -- right
                              by_cases h493 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h494 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2024_pos (not_le.mp h455).le h488 (not_le.mp h489).le h494 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2026_pos (not_le.mp h455).le h488 (not_le.mp h494).le h493 hz
                              · -- right
                                by_cases h495 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2032_pos (not_le.mp h455).le h488 (not_le.mp h493).le h495 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2034_pos (not_le.mp h455).le h488 (not_le.mp h495).le hz2 hz
                          · -- right
                            by_cases h496 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h497 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h498 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1993_pos (not_le.mp h488).le h487 hz1 h498 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1995_pos (not_le.mp h488).le h487 (not_le.mp h498).le h497 hz
                              · -- right
                                by_cases h499 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2001_pos (not_le.mp h488).le h487 (not_le.mp h497).le h499 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2003_pos (not_le.mp h488).le h487 (not_le.mp h499).le h496 hz
                            · -- right
                              by_cases h500 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h501 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2025_pos (not_le.mp h488).le h487 (not_le.mp h496).le h501 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2027_pos (not_le.mp h488).le h487 (not_le.mp h501).le h500 hz
                              · -- right
                                by_cases h502 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2033_pos (not_le.mp h488).le h487 (not_le.mp h500).le h502 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2035_pos (not_le.mp h488).le h487 (not_le.mp h502).le hz2 hz
                        · -- right
                          by_cases h503 : a ≤ ((1282287/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h504 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h505 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h506 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1996_pos (not_le.mp h487).le h503 hz1 h506 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1998_pos (not_le.mp h487).le h503 (not_le.mp h506).le h505 hz
                              · -- right
                                by_cases h507 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2004_pos (not_le.mp h487).le h503 (not_le.mp h505).le h507 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2006_pos (not_le.mp h487).le h503 (not_le.mp h507).le h504 hz
                            · -- right
                              by_cases h508 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h509 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2028_pos (not_le.mp h487).le h503 (not_le.mp h504).le h509 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2030_pos (not_le.mp h487).le h503 (not_le.mp h509).le h508 hz
                              · -- right
                                by_cases h510 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2036_pos (not_le.mp h487).le h503 (not_le.mp h508).le h510 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2038_pos (not_le.mp h487).le h503 (not_le.mp h510).le hz2 hz
                          · -- right
                            by_cases h511 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h512 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h513 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e1997_pos (not_le.mp h503).le h6 hz1 h513 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e1999_pos (not_le.mp h503).le h6 (not_le.mp h513).le h512 hz
                              · -- right
                                by_cases h514 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2005_pos (not_le.mp h503).le h6 (not_le.mp h512).le h514 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2007_pos (not_le.mp h503).le h6 (not_le.mp h514).le h511 hz
                            · -- right
                              by_cases h515 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h516 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2029_pos (not_le.mp h503).le h6 (not_le.mp h511).le h516 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2031_pos (not_le.mp h503).le h6 (not_le.mp h516).le h515 hz
                              · -- right
                                by_cases h517 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B033.e2037_pos (not_le.mp h503).le h6 (not_le.mp h515).le h517 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B033.e2039_pos (not_le.mp h503).le h6 (not_le.mp h517).le hz2 hz
              · -- right
                by_cases h518 : a ≤ ((40947/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h519 : a ≤ ((16209/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h520 : a ≤ ((161241/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h521 : a ≤ ((321633/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h522 : a ≤ ((642417/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h523 : a ≤ ((256797/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h524 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h525 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h526 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2040_pos (not_le.mp h6).le h523 hz1 h526 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2042_pos (not_le.mp h6).le h523 (not_le.mp h526).le h525 hz
                              · -- right
                                by_cases h527 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2048_pos (not_le.mp h6).le h523 (not_le.mp h525).le h527 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2050_pos (not_le.mp h6).le h523 (not_le.mp h527).le h524 hz
                            · -- right
                              by_cases h528 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h529 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2072_pos (not_le.mp h6).le h523 (not_le.mp h524).le h529 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2074_pos (not_le.mp h6).le h523 (not_le.mp h529).le h528 hz
                              · -- right
                                by_cases h530 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2080_pos (not_le.mp h6).le h523 (not_le.mp h528).le h530 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2082_pos (not_le.mp h6).le h523 (not_le.mp h530).le hz2 hz
                          · -- right
                            by_cases h531 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h532 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h533 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2041_pos (not_le.mp h523).le h522 hz1 h533 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2043_pos (not_le.mp h523).le h522 (not_le.mp h533).le h532 hz
                              · -- right
                                by_cases h534 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2049_pos (not_le.mp h523).le h522 (not_le.mp h532).le h534 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2051_pos (not_le.mp h523).le h522 (not_le.mp h534).le h531 hz
                            · -- right
                              by_cases h535 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h536 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2073_pos (not_le.mp h523).le h522 (not_le.mp h531).le h536 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2075_pos (not_le.mp h523).le h522 (not_le.mp h536).le h535 hz
                              · -- right
                                by_cases h537 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2081_pos (not_le.mp h523).le h522 (not_le.mp h535).le h537 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2083_pos (not_le.mp h523).le h522 (not_le.mp h537).le hz2 hz
                        · -- right
                          by_cases h538 : a ≤ ((1285683/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h539 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h540 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h541 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2044_pos (not_le.mp h522).le h538 hz1 h541 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2046_pos (not_le.mp h522).le h538 (not_le.mp h541).le h540 hz
                              · -- right
                                by_cases h542 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2052_pos (not_le.mp h522).le h538 (not_le.mp h540).le h542 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2054_pos (not_le.mp h522).le h538 (not_le.mp h542).le h539 hz
                            · -- right
                              by_cases h543 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h544 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2076_pos (not_le.mp h522).le h538 (not_le.mp h539).le h544 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2078_pos (not_le.mp h522).le h538 (not_le.mp h544).le h543 hz
                              · -- right
                                by_cases h545 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2084_pos (not_le.mp h522).le h538 (not_le.mp h543).le h545 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2086_pos (not_le.mp h522).le h538 (not_le.mp h545).le hz2 hz
                          · -- right
                            by_cases h546 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h547 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h548 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2045_pos (not_le.mp h538).le h521 hz1 h548 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2047_pos (not_le.mp h538).le h521 (not_le.mp h548).le h547 hz
                              · -- right
                                by_cases h549 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2053_pos (not_le.mp h538).le h521 (not_le.mp h547).le h549 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2055_pos (not_le.mp h538).le h521 (not_le.mp h549).le h546 hz
                            · -- right
                              by_cases h550 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h551 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2077_pos (not_le.mp h538).le h521 (not_le.mp h546).le h551 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2079_pos (not_le.mp h538).le h521 (not_le.mp h551).le h550 hz
                              · -- right
                                by_cases h552 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2085_pos (not_le.mp h538).le h521 (not_le.mp h550).le h552 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2087_pos (not_le.mp h538).le h521 (not_le.mp h552).le hz2 hz
                      · -- right
                        by_cases h553 : a ≤ ((128823/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h554 : a ≤ ((1287381/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h555 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h556 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h557 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2056_pos (not_le.mp h521).le h554 hz1 h557 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2058_pos (not_le.mp h521).le h554 (not_le.mp h557).le h556 hz
                              · -- right
                                by_cases h558 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2064_pos (not_le.mp h521).le h554 (not_le.mp h556).le h558 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2066_pos (not_le.mp h521).le h554 (not_le.mp h558).le h555 hz
                            · -- right
                              by_cases h559 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h560 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2088_pos (not_le.mp h521).le h554 (not_le.mp h555).le h560 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2090_pos (not_le.mp h521).le h554 (not_le.mp h560).le h559 hz
                              · -- right
                                by_cases h561 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2096_pos (not_le.mp h521).le h554 (not_le.mp h559).le h561 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2098_pos (not_le.mp h521).le h554 (not_le.mp h561).le hz2 hz
                          · -- right
                            by_cases h562 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h563 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h564 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2057_pos (not_le.mp h554).le h553 hz1 h564 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2059_pos (not_le.mp h554).le h553 (not_le.mp h564).le h563 hz
                              · -- right
                                by_cases h565 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2065_pos (not_le.mp h554).le h553 (not_le.mp h563).le h565 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2067_pos (not_le.mp h554).le h553 (not_le.mp h565).le h562 hz
                            · -- right
                              by_cases h566 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h567 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2089_pos (not_le.mp h554).le h553 (not_le.mp h562).le h567 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2091_pos (not_le.mp h554).le h553 (not_le.mp h567).le h566 hz
                              · -- right
                                by_cases h568 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2097_pos (not_le.mp h554).le h553 (not_le.mp h566).le h568 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2099_pos (not_le.mp h554).le h553 (not_le.mp h568).le hz2 hz
                        · -- right
                          by_cases h569 : a ≤ ((1289079/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h570 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h571 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h572 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2060_pos (not_le.mp h553).le h569 hz1 h572 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2062_pos (not_le.mp h553).le h569 (not_le.mp h572).le h571 hz
                              · -- right
                                by_cases h573 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2068_pos (not_le.mp h553).le h569 (not_le.mp h571).le h573 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2070_pos (not_le.mp h553).le h569 (not_le.mp h573).le h570 hz
                            · -- right
                              by_cases h574 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h575 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2092_pos (not_le.mp h553).le h569 (not_le.mp h570).le h575 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2094_pos (not_le.mp h553).le h569 (not_le.mp h575).le h574 hz
                              · -- right
                                by_cases h576 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2100_pos (not_le.mp h553).le h569 (not_le.mp h574).le h576 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2102_pos (not_le.mp h553).le h569 (not_le.mp h576).le hz2 hz
                          · -- right
                            by_cases h577 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h578 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h579 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2061_pos (not_le.mp h569).le h520 hz1 h579 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2063_pos (not_le.mp h569).le h520 (not_le.mp h579).le h578 hz
                              · -- right
                                by_cases h580 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2069_pos (not_le.mp h569).le h520 (not_le.mp h578).le h580 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2071_pos (not_le.mp h569).le h520 (not_le.mp h580).le h577 hz
                            · -- right
                              by_cases h581 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h582 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B034.e2093_pos (not_le.mp h569).le h520 (not_le.mp h577).le h582 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B034.e2095_pos (not_le.mp h569).le h520 (not_le.mp h582).le h581 hz
                              · -- right
                                by_cases h583 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2101_pos (not_le.mp h569).le h520 (not_le.mp h581).le h583 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2103_pos (not_le.mp h569).le h520 (not_le.mp h583).le hz2 hz
                    · -- right
                      by_cases h584 : a ≤ ((323331/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h585 : a ≤ ((645813/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h586 : a ≤ ((1290777/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h587 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h588 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h589 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2104_pos (not_le.mp h520).le h586 hz1 h589 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2106_pos (not_le.mp h520).le h586 (not_le.mp h589).le h588 hz
                              · -- right
                                by_cases h590 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2112_pos (not_le.mp h520).le h586 (not_le.mp h588).le h590 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2114_pos (not_le.mp h520).le h586 (not_le.mp h590).le h587 hz
                            · -- right
                              by_cases h591 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h592 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2136_pos (not_le.mp h520).le h586 (not_le.mp h587).le h592 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2138_pos (not_le.mp h520).le h586 (not_le.mp h592).le h591 hz
                              · -- right
                                by_cases h593 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2144_pos (not_le.mp h520).le h586 (not_le.mp h591).le h593 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2146_pos (not_le.mp h520).le h586 (not_le.mp h593).le hz2 hz
                          · -- right
                            by_cases h594 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h595 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h596 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2105_pos (not_le.mp h586).le h585 hz1 h596 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2107_pos (not_le.mp h586).le h585 (not_le.mp h596).le h595 hz
                              · -- right
                                by_cases h597 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2113_pos (not_le.mp h586).le h585 (not_le.mp h595).le h597 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2115_pos (not_le.mp h586).le h585 (not_le.mp h597).le h594 hz
                            · -- right
                              by_cases h598 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h599 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2137_pos (not_le.mp h586).le h585 (not_le.mp h594).le h599 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2139_pos (not_le.mp h586).le h585 (not_le.mp h599).le h598 hz
                              · -- right
                                by_cases h600 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2145_pos (not_le.mp h586).le h585 (not_le.mp h598).le h600 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2147_pos (not_le.mp h586).le h585 (not_le.mp h600).le hz2 hz
                        · -- right
                          by_cases h601 : a ≤ ((51699/327680 : ℚ) : ℝ)
                          · -- left
                            by_cases h602 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h603 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h604 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2108_pos (not_le.mp h585).le h601 hz1 h604 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2110_pos (not_le.mp h585).le h601 (not_le.mp h604).le h603 hz
                              · -- right
                                by_cases h605 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2116_pos (not_le.mp h585).le h601 (not_le.mp h603).le h605 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2118_pos (not_le.mp h585).le h601 (not_le.mp h605).le h602 hz
                            · -- right
                              by_cases h606 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h607 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2140_pos (not_le.mp h585).le h601 (not_le.mp h602).le h607 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2142_pos (not_le.mp h585).le h601 (not_le.mp h607).le h606 hz
                              · -- right
                                by_cases h608 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2148_pos (not_le.mp h585).le h601 (not_le.mp h606).le h608 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2150_pos (not_le.mp h585).le h601 (not_le.mp h608).le hz2 hz
                          · -- right
                            by_cases h609 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h610 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h611 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2109_pos (not_le.mp h601).le h584 hz1 h611 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2111_pos (not_le.mp h601).le h584 (not_le.mp h611).le h610 hz
                              · -- right
                                by_cases h612 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2117_pos (not_le.mp h601).le h584 (not_le.mp h610).le h612 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2119_pos (not_le.mp h601).le h584 (not_le.mp h612).le h609 hz
                            · -- right
                              by_cases h613 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h614 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2141_pos (not_le.mp h601).le h584 (not_le.mp h609).le h614 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2143_pos (not_le.mp h601).le h584 (not_le.mp h614).le h613 hz
                              · -- right
                                by_cases h615 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2149_pos (not_le.mp h601).le h584 (not_le.mp h613).le h615 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2151_pos (not_le.mp h601).le h584 (not_le.mp h615).le hz2 hz
                      · -- right
                        by_cases h616 : a ≤ ((647511/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h617 : a ≤ ((1294173/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h618 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h619 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h620 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2120_pos (not_le.mp h584).le h617 hz1 h620 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2122_pos (not_le.mp h584).le h617 (not_le.mp h620).le h619 hz
                              · -- right
                                by_cases h621 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2128_pos (not_le.mp h584).le h617 (not_le.mp h619).le h621 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2130_pos (not_le.mp h584).le h617 (not_le.mp h621).le h618 hz
                            · -- right
                              by_cases h622 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h623 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2152_pos (not_le.mp h584).le h617 (not_le.mp h618).le h623 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2154_pos (not_le.mp h584).le h617 (not_le.mp h623).le h622 hz
                              · -- right
                                by_cases h624 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2160_pos (not_le.mp h584).le h617 (not_le.mp h622).le h624 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2162_pos (not_le.mp h584).le h617 (not_le.mp h624).le hz2 hz
                          · -- right
                            by_cases h625 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h626 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h627 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2121_pos (not_le.mp h617).le h616 hz1 h627 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2123_pos (not_le.mp h617).le h616 (not_le.mp h627).le h626 hz
                              · -- right
                                by_cases h628 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2129_pos (not_le.mp h617).le h616 (not_le.mp h626).le h628 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2131_pos (not_le.mp h617).le h616 (not_le.mp h628).le h625 hz
                            · -- right
                              by_cases h629 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h630 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2153_pos (not_le.mp h617).le h616 (not_le.mp h625).le h630 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2155_pos (not_le.mp h617).le h616 (not_le.mp h630).le h629 hz
                              · -- right
                                by_cases h631 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2161_pos (not_le.mp h617).le h616 (not_le.mp h629).le h631 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2163_pos (not_le.mp h617).le h616 (not_le.mp h631).le hz2 hz
                        · -- right
                          by_cases h632 : a ≤ ((1295871/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h633 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h634 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h635 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2124_pos (not_le.mp h616).le h632 hz1 h635 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2126_pos (not_le.mp h616).le h632 (not_le.mp h635).le h634 hz
                              · -- right
                                by_cases h636 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2132_pos (not_le.mp h616).le h632 (not_le.mp h634).le h636 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2134_pos (not_le.mp h616).le h632 (not_le.mp h636).le h633 hz
                            · -- right
                              by_cases h637 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h638 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2156_pos (not_le.mp h616).le h632 (not_le.mp h633).le h638 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2158_pos (not_le.mp h616).le h632 (not_le.mp h638).le h637 hz
                              · -- right
                                by_cases h639 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2164_pos (not_le.mp h616).le h632 (not_le.mp h637).le h639 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2166_pos (not_le.mp h616).le h632 (not_le.mp h639).le hz2 hz
                          · -- right
                            by_cases h640 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h641 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h642 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2125_pos (not_le.mp h632).le h519 hz1 h642 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2127_pos (not_le.mp h632).le h519 (not_le.mp h642).le h641 hz
                              · -- right
                                by_cases h643 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2133_pos (not_le.mp h632).le h519 (not_le.mp h641).le h643 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2135_pos (not_le.mp h632).le h519 (not_le.mp h643).le h640 hz
                            · -- right
                              by_cases h644 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h645 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B035.e2157_pos (not_le.mp h632).le h519 (not_le.mp h640).le h645 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B035.e2159_pos (not_le.mp h632).le h519 (not_le.mp h645).le h644 hz
                              · -- right
                                by_cases h646 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2165_pos (not_le.mp h632).le h519 (not_le.mp h644).le h646 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2167_pos (not_le.mp h632).le h519 (not_le.mp h646).le hz2 hz
                  · -- right
                    by_cases h647 : a ≤ ((162939/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h648 : a ≤ ((325029/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h649 : a ≤ ((649209/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h650 : a ≤ ((1297569/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h651 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h652 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h653 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2168_pos (not_le.mp h519).le h650 hz1 h653 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2170_pos (not_le.mp h519).le h650 (not_le.mp h653).le h652 hz
                              · -- right
                                by_cases h654 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2176_pos (not_le.mp h519).le h650 (not_le.mp h652).le h654 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2178_pos (not_le.mp h519).le h650 (not_le.mp h654).le h651 hz
                            · -- right
                              by_cases h655 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h656 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2200_pos (not_le.mp h519).le h650 (not_le.mp h651).le h656 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2202_pos (not_le.mp h519).le h650 (not_le.mp h656).le h655 hz
                              · -- right
                                by_cases h657 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2208_pos (not_le.mp h519).le h650 (not_le.mp h655).le h657 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2210_pos (not_le.mp h519).le h650 (not_le.mp h657).le hz2 hz
                          · -- right
                            by_cases h658 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h659 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h660 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2169_pos (not_le.mp h650).le h649 hz1 h660 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2171_pos (not_le.mp h650).le h649 (not_le.mp h660).le h659 hz
                              · -- right
                                by_cases h661 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2177_pos (not_le.mp h650).le h649 (not_le.mp h659).le h661 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2179_pos (not_le.mp h650).le h649 (not_le.mp h661).le h658 hz
                            · -- right
                              by_cases h662 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h663 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2201_pos (not_le.mp h650).le h649 (not_le.mp h658).le h663 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2203_pos (not_le.mp h650).le h649 (not_le.mp h663).le h662 hz
                              · -- right
                                by_cases h664 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2209_pos (not_le.mp h650).le h649 (not_le.mp h662).le h664 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2211_pos (not_le.mp h650).le h649 (not_le.mp h664).le hz2 hz
                        · -- right
                          by_cases h665 : a ≤ ((1299267/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h666 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h667 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h668 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2172_pos (not_le.mp h649).le h665 hz1 h668 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2174_pos (not_le.mp h649).le h665 (not_le.mp h668).le h667 hz
                              · -- right
                                by_cases h669 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2180_pos (not_le.mp h649).le h665 (not_le.mp h667).le h669 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2182_pos (not_le.mp h649).le h665 (not_le.mp h669).le h666 hz
                            · -- right
                              by_cases h670 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h671 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2204_pos (not_le.mp h649).le h665 (not_le.mp h666).le h671 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2206_pos (not_le.mp h649).le h665 (not_le.mp h671).le h670 hz
                              · -- right
                                by_cases h672 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2212_pos (not_le.mp h649).le h665 (not_le.mp h670).le h672 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2214_pos (not_le.mp h649).le h665 (not_le.mp h672).le hz2 hz
                          · -- right
                            by_cases h673 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h674 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h675 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2173_pos (not_le.mp h665).le h648 hz1 h675 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2175_pos (not_le.mp h665).le h648 (not_le.mp h675).le h674 hz
                              · -- right
                                by_cases h676 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2181_pos (not_le.mp h665).le h648 (not_le.mp h674).le h676 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2183_pos (not_le.mp h665).le h648 (not_le.mp h676).le h673 hz
                            · -- right
                              by_cases h677 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h678 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2205_pos (not_le.mp h665).le h648 (not_le.mp h673).le h678 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2207_pos (not_le.mp h665).le h648 (not_le.mp h678).le h677 hz
                              · -- right
                                by_cases h679 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2213_pos (not_le.mp h665).le h648 (not_le.mp h677).le h679 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2215_pos (not_le.mp h665).le h648 (not_le.mp h679).le hz2 hz
                      · -- right
                        by_cases h680 : a ≤ ((650907/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h681 : a ≤ ((260193/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h682 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h683 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h684 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2184_pos (not_le.mp h648).le h681 hz1 h684 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2186_pos (not_le.mp h648).le h681 (not_le.mp h684).le h683 hz
                              · -- right
                                by_cases h685 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2192_pos (not_le.mp h648).le h681 (not_le.mp h683).le h685 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2194_pos (not_le.mp h648).le h681 (not_le.mp h685).le h682 hz
                            · -- right
                              by_cases h686 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h687 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2216_pos (not_le.mp h648).le h681 (not_le.mp h682).le h687 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2218_pos (not_le.mp h648).le h681 (not_le.mp h687).le h686 hz
                              · -- right
                                by_cases h688 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2224_pos (not_le.mp h648).le h681 (not_le.mp h686).le h688 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2226_pos (not_le.mp h648).le h681 (not_le.mp h688).le hz2 hz
                          · -- right
                            by_cases h689 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h690 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h691 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2185_pos (not_le.mp h681).le h680 hz1 h691 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2187_pos (not_le.mp h681).le h680 (not_le.mp h691).le h690 hz
                              · -- right
                                by_cases h692 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2193_pos (not_le.mp h681).le h680 (not_le.mp h690).le h692 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2195_pos (not_le.mp h681).le h680 (not_le.mp h692).le h689 hz
                            · -- right
                              by_cases h693 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h694 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2217_pos (not_le.mp h681).le h680 (not_le.mp h689).le h694 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2219_pos (not_le.mp h681).le h680 (not_le.mp h694).le h693 hz
                              · -- right
                                by_cases h695 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2225_pos (not_le.mp h681).le h680 (not_le.mp h693).le h695 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2227_pos (not_le.mp h681).le h680 (not_le.mp h695).le hz2 hz
                        · -- right
                          by_cases h696 : a ≤ ((1302663/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h697 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h698 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h699 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2188_pos (not_le.mp h680).le h696 hz1 h699 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2190_pos (not_le.mp h680).le h696 (not_le.mp h699).le h698 hz
                              · -- right
                                by_cases h700 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2196_pos (not_le.mp h680).le h696 (not_le.mp h698).le h700 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2198_pos (not_le.mp h680).le h696 (not_le.mp h700).le h697 hz
                            · -- right
                              by_cases h701 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h702 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2220_pos (not_le.mp h680).le h696 (not_le.mp h697).le h702 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2222_pos (not_le.mp h680).le h696 (not_le.mp h702).le h701 hz
                              · -- right
                                by_cases h703 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2228_pos (not_le.mp h680).le h696 (not_le.mp h701).le h703 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2230_pos (not_le.mp h680).le h696 (not_le.mp h703).le hz2 hz
                          · -- right
                            by_cases h704 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h705 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h706 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2189_pos (not_le.mp h696).le h647 hz1 h706 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2191_pos (not_le.mp h696).le h647 (not_le.mp h706).le h705 hz
                              · -- right
                                by_cases h707 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B036.e2197_pos (not_le.mp h696).le h647 (not_le.mp h705).le h707 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B036.e2199_pos (not_le.mp h696).le h647 (not_le.mp h707).le h704 hz
                            · -- right
                              by_cases h708 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h709 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2221_pos (not_le.mp h696).le h647 (not_le.mp h704).le h709 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2223_pos (not_le.mp h696).le h647 (not_le.mp h709).le h708 hz
                              · -- right
                                by_cases h710 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2229_pos (not_le.mp h696).le h647 (not_le.mp h708).le h710 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2231_pos (not_le.mp h696).le h647 (not_le.mp h710).le hz2 hz
                    · -- right
                      by_cases h711 : a ≤ ((326727/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h712 : a ≤ ((130521/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h713 : a ≤ ((1304361/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h714 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h715 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h716 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2232_pos (not_le.mp h647).le h713 hz1 h716 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2234_pos (not_le.mp h647).le h713 (not_le.mp h716).le h715 hz
                              · -- right
                                by_cases h717 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2240_pos (not_le.mp h647).le h713 (not_le.mp h715).le h717 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2242_pos (not_le.mp h647).le h713 (not_le.mp h717).le h714 hz
                            · -- right
                              by_cases h718 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h719 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2264_pos (not_le.mp h647).le h713 (not_le.mp h714).le h719 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2266_pos (not_le.mp h647).le h713 (not_le.mp h719).le h718 hz
                              · -- right
                                by_cases h720 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2272_pos (not_le.mp h647).le h713 (not_le.mp h718).le h720 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2274_pos (not_le.mp h647).le h713 (not_le.mp h720).le hz2 hz
                          · -- right
                            by_cases h721 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h722 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h723 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2233_pos (not_le.mp h713).le h712 hz1 h723 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2235_pos (not_le.mp h713).le h712 (not_le.mp h723).le h722 hz
                              · -- right
                                by_cases h724 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2241_pos (not_le.mp h713).le h712 (not_le.mp h722).le h724 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2243_pos (not_le.mp h713).le h712 (not_le.mp h724).le h721 hz
                            · -- right
                              by_cases h725 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h726 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2265_pos (not_le.mp h713).le h712 (not_le.mp h721).le h726 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2267_pos (not_le.mp h713).le h712 (not_le.mp h726).le h725 hz
                              · -- right
                                by_cases h727 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2273_pos (not_le.mp h713).le h712 (not_le.mp h725).le h727 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2275_pos (not_le.mp h713).le h712 (not_le.mp h727).le hz2 hz
                        · -- right
                          by_cases h728 : a ≤ ((1306059/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h729 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h730 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h731 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2236_pos (not_le.mp h712).le h728 hz1 h731 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2238_pos (not_le.mp h712).le h728 (not_le.mp h731).le h730 hz
                              · -- right
                                by_cases h732 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2244_pos (not_le.mp h712).le h728 (not_le.mp h730).le h732 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2246_pos (not_le.mp h712).le h728 (not_le.mp h732).le h729 hz
                            · -- right
                              by_cases h733 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h734 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2268_pos (not_le.mp h712).le h728 (not_le.mp h729).le h734 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2270_pos (not_le.mp h712).le h728 (not_le.mp h734).le h733 hz
                              · -- right
                                by_cases h735 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2276_pos (not_le.mp h712).le h728 (not_le.mp h733).le h735 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2278_pos (not_le.mp h712).le h728 (not_le.mp h735).le hz2 hz
                          · -- right
                            by_cases h736 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h737 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h738 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2237_pos (not_le.mp h728).le h711 hz1 h738 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2239_pos (not_le.mp h728).le h711 (not_le.mp h738).le h737 hz
                              · -- right
                                by_cases h739 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2245_pos (not_le.mp h728).le h711 (not_le.mp h737).le h739 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2247_pos (not_le.mp h728).le h711 (not_le.mp h739).le h736 hz
                            · -- right
                              by_cases h740 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h741 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2269_pos (not_le.mp h728).le h711 (not_le.mp h736).le h741 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2271_pos (not_le.mp h728).le h711 (not_le.mp h741).le h740 hz
                              · -- right
                                by_cases h742 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2277_pos (not_le.mp h728).le h711 (not_le.mp h740).le h742 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2279_pos (not_le.mp h728).le h711 (not_le.mp h742).le hz2 hz
                      · -- right
                        by_cases h743 : a ≤ ((654303/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h744 : a ≤ ((1307757/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h745 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h746 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h747 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2248_pos (not_le.mp h711).le h744 hz1 h747 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2250_pos (not_le.mp h711).le h744 (not_le.mp h747).le h746 hz
                              · -- right
                                by_cases h748 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2256_pos (not_le.mp h711).le h744 (not_le.mp h746).le h748 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2258_pos (not_le.mp h711).le h744 (not_le.mp h748).le h745 hz
                            · -- right
                              by_cases h749 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h750 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2280_pos (not_le.mp h711).le h744 (not_le.mp h745).le h750 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2282_pos (not_le.mp h711).le h744 (not_le.mp h750).le h749 hz
                              · -- right
                                by_cases h751 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2288_pos (not_le.mp h711).le h744 (not_le.mp h749).le h751 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2290_pos (not_le.mp h711).le h744 (not_le.mp h751).le hz2 hz
                          · -- right
                            by_cases h752 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h753 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h754 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2249_pos (not_le.mp h744).le h743 hz1 h754 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2251_pos (not_le.mp h744).le h743 (not_le.mp h754).le h753 hz
                              · -- right
                                by_cases h755 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2257_pos (not_le.mp h744).le h743 (not_le.mp h753).le h755 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2259_pos (not_le.mp h744).le h743 (not_le.mp h755).le h752 hz
                            · -- right
                              by_cases h756 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h757 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2281_pos (not_le.mp h744).le h743 (not_le.mp h752).le h757 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2283_pos (not_le.mp h744).le h743 (not_le.mp h757).le h756 hz
                              · -- right
                                by_cases h758 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2289_pos (not_le.mp h744).le h743 (not_le.mp h756).le h758 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2291_pos (not_le.mp h744).le h743 (not_le.mp h758).le hz2 hz
                        · -- right
                          by_cases h759 : a ≤ ((261891/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h760 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h761 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h762 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2252_pos (not_le.mp h743).le h759 hz1 h762 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2254_pos (not_le.mp h743).le h759 (not_le.mp h762).le h761 hz
                              · -- right
                                by_cases h763 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2260_pos (not_le.mp h743).le h759 (not_le.mp h761).le h763 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2262_pos (not_le.mp h743).le h759 (not_le.mp h763).le h760 hz
                            · -- right
                              by_cases h764 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h765 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2284_pos (not_le.mp h743).le h759 (not_le.mp h760).le h765 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2286_pos (not_le.mp h743).le h759 (not_le.mp h765).le h764 hz
                              · -- right
                                by_cases h766 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2292_pos (not_le.mp h743).le h759 (not_le.mp h764).le h766 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2294_pos (not_le.mp h743).le h759 (not_le.mp h766).le hz2 hz
                          · -- right
                            by_cases h767 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h768 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h769 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2253_pos (not_le.mp h759).le h518 hz1 h769 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2255_pos (not_le.mp h759).le h518 (not_le.mp h769).le h768 hz
                              · -- right
                                by_cases h770 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B037.e2261_pos (not_le.mp h759).le h518 (not_le.mp h768).le h770 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B037.e2263_pos (not_le.mp h759).le h518 (not_le.mp h770).le h767 hz
                            · -- right
                              by_cases h771 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h772 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2285_pos (not_le.mp h759).le h518 (not_le.mp h767).le h772 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2287_pos (not_le.mp h759).le h518 (not_le.mp h772).le h771 hz
                              · -- right
                                by_cases h773 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2293_pos (not_le.mp h759).le h518 (not_le.mp h771).le h773 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2295_pos (not_le.mp h759).le h518 (not_le.mp h773).le hz2 hz
                · -- right
                  by_cases h774 : a ≤ ((82743/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h775 : a ≤ ((164637/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h776 : a ≤ ((13137/81920 : ℚ) : ℝ)
                      · -- left
                        by_cases h777 : a ≤ ((656001/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h778 : a ≤ ((1311153/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h779 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h780 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h781 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2296_pos (not_le.mp h518).le h778 hz1 h781 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2298_pos (not_le.mp h518).le h778 (not_le.mp h781).le h780 hz
                              · -- right
                                by_cases h782 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2304_pos (not_le.mp h518).le h778 (not_le.mp h780).le h782 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2306_pos (not_le.mp h518).le h778 (not_le.mp h782).le h779 hz
                            · -- right
                              by_cases h783 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h784 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2328_pos (not_le.mp h518).le h778 (not_le.mp h779).le h784 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2330_pos (not_le.mp h518).le h778 (not_le.mp h784).le h783 hz
                              · -- right
                                by_cases h785 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2336_pos (not_le.mp h518).le h778 (not_le.mp h783).le h785 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2338_pos (not_le.mp h518).le h778 (not_le.mp h785).le hz2 hz
                          · -- right
                            by_cases h786 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h787 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h788 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2297_pos (not_le.mp h778).le h777 hz1 h788 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2299_pos (not_le.mp h778).le h777 (not_le.mp h788).le h787 hz
                              · -- right
                                by_cases h789 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2305_pos (not_le.mp h778).le h777 (not_le.mp h787).le h789 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2307_pos (not_le.mp h778).le h777 (not_le.mp h789).le h786 hz
                            · -- right
                              by_cases h790 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h791 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2329_pos (not_le.mp h778).le h777 (not_le.mp h786).le h791 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2331_pos (not_le.mp h778).le h777 (not_le.mp h791).le h790 hz
                              · -- right
                                by_cases h792 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2337_pos (not_le.mp h778).le h777 (not_le.mp h790).le h792 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2339_pos (not_le.mp h778).le h777 (not_le.mp h792).le hz2 hz
                        · -- right
                          by_cases h793 : a ≤ ((1312851/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h794 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h795 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h796 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2300_pos (not_le.mp h777).le h793 hz1 h796 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2302_pos (not_le.mp h777).le h793 (not_le.mp h796).le h795 hz
                              · -- right
                                by_cases h797 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2308_pos (not_le.mp h777).le h793 (not_le.mp h795).le h797 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2310_pos (not_le.mp h777).le h793 (not_le.mp h797).le h794 hz
                            · -- right
                              by_cases h798 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h799 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2332_pos (not_le.mp h777).le h793 (not_le.mp h794).le h799 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2334_pos (not_le.mp h777).le h793 (not_le.mp h799).le h798 hz
                              · -- right
                                by_cases h800 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2340_pos (not_le.mp h777).le h793 (not_le.mp h798).le h800 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2342_pos (not_le.mp h777).le h793 (not_le.mp h800).le hz2 hz
                          · -- right
                            by_cases h801 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h802 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h803 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2301_pos (not_le.mp h793).le h776 hz1 h803 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2303_pos (not_le.mp h793).le h776 (not_le.mp h803).le h802 hz
                              · -- right
                                by_cases h804 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2309_pos (not_le.mp h793).le h776 (not_le.mp h802).le h804 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2311_pos (not_le.mp h793).le h776 (not_le.mp h804).le h801 hz
                            · -- right
                              by_cases h805 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h806 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2333_pos (not_le.mp h793).le h776 (not_le.mp h801).le h806 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2335_pos (not_le.mp h793).le h776 (not_le.mp h806).le h805 hz
                              · -- right
                                by_cases h807 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2341_pos (not_le.mp h793).le h776 (not_le.mp h805).le h807 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2343_pos (not_le.mp h793).le h776 (not_le.mp h807).le hz2 hz
                      · -- right
                        by_cases h808 : a ≤ ((657699/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h809 : a ≤ ((1314549/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h810 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h811 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h812 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2312_pos (not_le.mp h776).le h809 hz1 h812 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2314_pos (not_le.mp h776).le h809 (not_le.mp h812).le h811 hz
                              · -- right
                                by_cases h813 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2320_pos (not_le.mp h776).le h809 (not_le.mp h811).le h813 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2322_pos (not_le.mp h776).le h809 (not_le.mp h813).le h810 hz
                            · -- right
                              by_cases h814 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h815 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2344_pos (not_le.mp h776).le h809 (not_le.mp h810).le h815 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2346_pos (not_le.mp h776).le h809 (not_le.mp h815).le h814 hz
                              · -- right
                                by_cases h816 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2352_pos (not_le.mp h776).le h809 (not_le.mp h814).le h816 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2354_pos (not_le.mp h776).le h809 (not_le.mp h816).le hz2 hz
                          · -- right
                            by_cases h817 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h818 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h819 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2313_pos (not_le.mp h809).le h808 hz1 h819 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2315_pos (not_le.mp h809).le h808 (not_le.mp h819).le h818 hz
                              · -- right
                                by_cases h820 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2321_pos (not_le.mp h809).le h808 (not_le.mp h818).le h820 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2323_pos (not_le.mp h809).le h808 (not_le.mp h820).le h817 hz
                            · -- right
                              by_cases h821 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h822 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2345_pos (not_le.mp h809).le h808 (not_le.mp h817).le h822 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2347_pos (not_le.mp h809).le h808 (not_le.mp h822).le h821 hz
                              · -- right
                                by_cases h823 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2353_pos (not_le.mp h809).le h808 (not_le.mp h821).le h823 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2355_pos (not_le.mp h809).le h808 (not_le.mp h823).le hz2 hz
                        · -- right
                          by_cases h824 : a ≤ ((1316247/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h825 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h826 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h827 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2316_pos (not_le.mp h808).le h824 hz1 h827 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2318_pos (not_le.mp h808).le h824 (not_le.mp h827).le h826 hz
                              · -- right
                                by_cases h828 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2324_pos (not_le.mp h808).le h824 (not_le.mp h826).le h828 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2326_pos (not_le.mp h808).le h824 (not_le.mp h828).le h825 hz
                            · -- right
                              by_cases h829 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h830 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2348_pos (not_le.mp h808).le h824 (not_le.mp h825).le h830 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2350_pos (not_le.mp h808).le h824 (not_le.mp h830).le h829 hz
                              · -- right
                                by_cases h831 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2356_pos (not_le.mp h808).le h824 (not_le.mp h829).le h831 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2358_pos (not_le.mp h808).le h824 (not_le.mp h831).le hz2 hz
                          · -- right
                            by_cases h832 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h833 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h834 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2317_pos (not_le.mp h824).le h775 hz1 h834 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2319_pos (not_le.mp h824).le h775 (not_le.mp h834).le h833 hz
                              · -- right
                                by_cases h835 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B038.e2325_pos (not_le.mp h824).le h775 (not_le.mp h833).le h835 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B038.e2327_pos (not_le.mp h824).le h775 (not_le.mp h835).le h832 hz
                            · -- right
                              by_cases h836 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h837 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2349_pos (not_le.mp h824).le h775 (not_le.mp h832).le h837 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2351_pos (not_le.mp h824).le h775 (not_le.mp h837).le h836 hz
                              · -- right
                                by_cases h838 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2357_pos (not_le.mp h824).le h775 (not_le.mp h836).le h838 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2359_pos (not_le.mp h824).le h775 (not_le.mp h838).le hz2 hz
                    · -- right
                      by_cases h839 : a ≤ ((330123/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h840 : a ≤ ((659397/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h841 : a ≤ ((263589/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h842 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h843 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h844 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2360_pos (not_le.mp h775).le h841 hz1 h844 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2362_pos (not_le.mp h775).le h841 (not_le.mp h844).le h843 hz
                              · -- right
                                by_cases h845 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2368_pos (not_le.mp h775).le h841 (not_le.mp h843).le h845 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2370_pos (not_le.mp h775).le h841 (not_le.mp h845).le h842 hz
                            · -- right
                              by_cases h846 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h847 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2392_pos (not_le.mp h775).le h841 (not_le.mp h842).le h847 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2394_pos (not_le.mp h775).le h841 (not_le.mp h847).le h846 hz
                              · -- right
                                by_cases h848 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2400_pos (not_le.mp h775).le h841 (not_le.mp h846).le h848 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2402_pos (not_le.mp h775).le h841 (not_le.mp h848).le hz2 hz
                          · -- right
                            by_cases h849 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h850 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h851 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2361_pos (not_le.mp h841).le h840 hz1 h851 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2363_pos (not_le.mp h841).le h840 (not_le.mp h851).le h850 hz
                              · -- right
                                by_cases h852 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2369_pos (not_le.mp h841).le h840 (not_le.mp h850).le h852 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2371_pos (not_le.mp h841).le h840 (not_le.mp h852).le h849 hz
                            · -- right
                              by_cases h853 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h854 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2393_pos (not_le.mp h841).le h840 (not_le.mp h849).le h854 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2395_pos (not_le.mp h841).le h840 (not_le.mp h854).le h853 hz
                              · -- right
                                by_cases h855 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2401_pos (not_le.mp h841).le h840 (not_le.mp h853).le h855 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2403_pos (not_le.mp h841).le h840 (not_le.mp h855).le hz2 hz
                        · -- right
                          by_cases h856 : a ≤ ((1319643/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h857 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h858 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h859 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2364_pos (not_le.mp h840).le h856 hz1 h859 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2366_pos (not_le.mp h840).le h856 (not_le.mp h859).le h858 hz
                              · -- right
                                by_cases h860 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2372_pos (not_le.mp h840).le h856 (not_le.mp h858).le h860 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2374_pos (not_le.mp h840).le h856 (not_le.mp h860).le h857 hz
                            · -- right
                              by_cases h861 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h862 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2396_pos (not_le.mp h840).le h856 (not_le.mp h857).le h862 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2398_pos (not_le.mp h840).le h856 (not_le.mp h862).le h861 hz
                              · -- right
                                by_cases h863 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2404_pos (not_le.mp h840).le h856 (not_le.mp h861).le h863 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2406_pos (not_le.mp h840).le h856 (not_le.mp h863).le hz2 hz
                          · -- right
                            by_cases h864 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h865 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h866 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2365_pos (not_le.mp h856).le h839 hz1 h866 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2367_pos (not_le.mp h856).le h839 (not_le.mp h866).le h865 hz
                              · -- right
                                by_cases h867 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2373_pos (not_le.mp h856).le h839 (not_le.mp h865).le h867 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2375_pos (not_le.mp h856).le h839 (not_le.mp h867).le h864 hz
                            · -- right
                              by_cases h868 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h869 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2397_pos (not_le.mp h856).le h839 (not_le.mp h864).le h869 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2399_pos (not_le.mp h856).le h839 (not_le.mp h869).le h868 hz
                              · -- right
                                by_cases h870 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2405_pos (not_le.mp h856).le h839 (not_le.mp h868).le h870 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2407_pos (not_le.mp h856).le h839 (not_le.mp h870).le hz2 hz
                      · -- right
                        by_cases h871 : a ≤ ((132219/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h872 : a ≤ ((1321341/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h873 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h874 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h875 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2376_pos (not_le.mp h839).le h872 hz1 h875 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2378_pos (not_le.mp h839).le h872 (not_le.mp h875).le h874 hz
                              · -- right
                                by_cases h876 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2384_pos (not_le.mp h839).le h872 (not_le.mp h874).le h876 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2386_pos (not_le.mp h839).le h872 (not_le.mp h876).le h873 hz
                            · -- right
                              by_cases h877 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h878 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2408_pos (not_le.mp h839).le h872 (not_le.mp h873).le h878 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2410_pos (not_le.mp h839).le h872 (not_le.mp h878).le h877 hz
                              · -- right
                                by_cases h879 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2416_pos (not_le.mp h839).le h872 (not_le.mp h877).le h879 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2418_pos (not_le.mp h839).le h872 (not_le.mp h879).le hz2 hz
                          · -- right
                            by_cases h880 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h881 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h882 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2377_pos (not_le.mp h872).le h871 hz1 h882 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2379_pos (not_le.mp h872).le h871 (not_le.mp h882).le h881 hz
                              · -- right
                                by_cases h883 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2385_pos (not_le.mp h872).le h871 (not_le.mp h881).le h883 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2387_pos (not_le.mp h872).le h871 (not_le.mp h883).le h880 hz
                            · -- right
                              by_cases h884 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h885 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2409_pos (not_le.mp h872).le h871 (not_le.mp h880).le h885 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2411_pos (not_le.mp h872).le h871 (not_le.mp h885).le h884 hz
                              · -- right
                                by_cases h886 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2417_pos (not_le.mp h872).le h871 (not_le.mp h884).le h886 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2419_pos (not_le.mp h872).le h871 (not_le.mp h886).le hz2 hz
                        · -- right
                          by_cases h887 : a ≤ ((1323039/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h888 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h889 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h890 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2380_pos (not_le.mp h871).le h887 hz1 h890 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2382_pos (not_le.mp h871).le h887 (not_le.mp h890).le h889 hz
                              · -- right
                                by_cases h891 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2388_pos (not_le.mp h871).le h887 (not_le.mp h889).le h891 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2390_pos (not_le.mp h871).le h887 (not_le.mp h891).le h888 hz
                            · -- right
                              by_cases h892 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h893 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2412_pos (not_le.mp h871).le h887 (not_le.mp h888).le h893 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2414_pos (not_le.mp h871).le h887 (not_le.mp h893).le h892 hz
                              · -- right
                                by_cases h894 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2420_pos (not_le.mp h871).le h887 (not_le.mp h892).le h894 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2422_pos (not_le.mp h871).le h887 (not_le.mp h894).le hz2 hz
                          · -- right
                            by_cases h895 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h896 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h897 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2381_pos (not_le.mp h887).le h774 hz1 h897 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2383_pos (not_le.mp h887).le h774 (not_le.mp h897).le h896 hz
                              · -- right
                                by_cases h898 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B039.e2389_pos (not_le.mp h887).le h774 (not_le.mp h896).le h898 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B039.e2391_pos (not_le.mp h887).le h774 (not_le.mp h898).le h895 hz
                            · -- right
                              by_cases h899 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h900 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2413_pos (not_le.mp h887).le h774 (not_le.mp h895).le h900 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2415_pos (not_le.mp h887).le h774 (not_le.mp h900).le h899 hz
                              · -- right
                                by_cases h901 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2421_pos (not_le.mp h887).le h774 (not_le.mp h899).le h901 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2423_pos (not_le.mp h887).le h774 (not_le.mp h901).le hz2 hz
                  · -- right
                    by_cases h902 : a ≤ ((33267/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h903 : a ≤ ((331821/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h904 : a ≤ ((662793/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h905 : a ≤ ((1324737/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h906 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h907 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h908 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2424_pos (not_le.mp h774).le h905 hz1 h908 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2426_pos (not_le.mp h774).le h905 (not_le.mp h908).le h907 hz
                              · -- right
                                by_cases h909 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2432_pos (not_le.mp h774).le h905 (not_le.mp h907).le h909 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2434_pos (not_le.mp h774).le h905 (not_le.mp h909).le h906 hz
                            · -- right
                              by_cases h910 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h911 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2456_pos (not_le.mp h774).le h905 (not_le.mp h906).le h911 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2458_pos (not_le.mp h774).le h905 (not_le.mp h911).le h910 hz
                              · -- right
                                by_cases h912 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2464_pos (not_le.mp h774).le h905 (not_le.mp h910).le h912 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2466_pos (not_le.mp h774).le h905 (not_le.mp h912).le hz2 hz
                          · -- right
                            by_cases h913 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h914 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h915 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2425_pos (not_le.mp h905).le h904 hz1 h915 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2427_pos (not_le.mp h905).le h904 (not_le.mp h915).le h914 hz
                              · -- right
                                by_cases h916 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2433_pos (not_le.mp h905).le h904 (not_le.mp h914).le h916 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2435_pos (not_le.mp h905).le h904 (not_le.mp h916).le h913 hz
                            · -- right
                              by_cases h917 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h918 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2457_pos (not_le.mp h905).le h904 (not_le.mp h913).le h918 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2459_pos (not_le.mp h905).le h904 (not_le.mp h918).le h917 hz
                              · -- right
                                by_cases h919 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2465_pos (not_le.mp h905).le h904 (not_le.mp h917).le h919 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2467_pos (not_le.mp h905).le h904 (not_le.mp h919).le hz2 hz
                        · -- right
                          by_cases h920 : a ≤ ((265287/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h921 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h922 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h923 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2428_pos (not_le.mp h904).le h920 hz1 h923 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2430_pos (not_le.mp h904).le h920 (not_le.mp h923).le h922 hz
                              · -- right
                                by_cases h924 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2436_pos (not_le.mp h904).le h920 (not_le.mp h922).le h924 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2438_pos (not_le.mp h904).le h920 (not_le.mp h924).le h921 hz
                            · -- right
                              by_cases h925 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h926 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2460_pos (not_le.mp h904).le h920 (not_le.mp h921).le h926 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2462_pos (not_le.mp h904).le h920 (not_le.mp h926).le h925 hz
                              · -- right
                                by_cases h927 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2468_pos (not_le.mp h904).le h920 (not_le.mp h925).le h927 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2470_pos (not_le.mp h904).le h920 (not_le.mp h927).le hz2 hz
                          · -- right
                            by_cases h928 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h929 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h930 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2429_pos (not_le.mp h920).le h903 hz1 h930 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2431_pos (not_le.mp h920).le h903 (not_le.mp h930).le h929 hz
                              · -- right
                                by_cases h931 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2437_pos (not_le.mp h920).le h903 (not_le.mp h929).le h931 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2439_pos (not_le.mp h920).le h903 (not_le.mp h931).le h928 hz
                            · -- right
                              by_cases h932 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h933 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2461_pos (not_le.mp h920).le h903 (not_le.mp h928).le h933 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2463_pos (not_le.mp h920).le h903 (not_le.mp h933).le h932 hz
                              · -- right
                                by_cases h934 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2469_pos (not_le.mp h920).le h903 (not_le.mp h932).le h934 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2471_pos (not_le.mp h920).le h903 (not_le.mp h934).le hz2 hz
                      · -- right
                        by_cases h935 : a ≤ ((664491/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h936 : a ≤ ((1328133/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h937 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h938 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h939 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2440_pos (not_le.mp h903).le h936 hz1 h939 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2442_pos (not_le.mp h903).le h936 (not_le.mp h939).le h938 hz
                              · -- right
                                by_cases h940 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2448_pos (not_le.mp h903).le h936 (not_le.mp h938).le h940 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2450_pos (not_le.mp h903).le h936 (not_le.mp h940).le h937 hz
                            · -- right
                              by_cases h941 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h942 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2472_pos (not_le.mp h903).le h936 (not_le.mp h937).le h942 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2474_pos (not_le.mp h903).le h936 (not_le.mp h942).le h941 hz
                              · -- right
                                by_cases h943 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2480_pos (not_le.mp h903).le h936 (not_le.mp h941).le h943 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2482_pos (not_le.mp h903).le h936 (not_le.mp h943).le hz2 hz
                          · -- right
                            by_cases h944 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h945 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h946 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2441_pos (not_le.mp h936).le h935 hz1 h946 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2443_pos (not_le.mp h936).le h935 (not_le.mp h946).le h945 hz
                              · -- right
                                by_cases h947 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2449_pos (not_le.mp h936).le h935 (not_le.mp h945).le h947 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2451_pos (not_le.mp h936).le h935 (not_le.mp h947).le h944 hz
                            · -- right
                              by_cases h948 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h949 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2473_pos (not_le.mp h936).le h935 (not_le.mp h944).le h949 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2475_pos (not_le.mp h936).le h935 (not_le.mp h949).le h948 hz
                              · -- right
                                by_cases h950 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2481_pos (not_le.mp h936).le h935 (not_le.mp h948).le h950 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2483_pos (not_le.mp h936).le h935 (not_le.mp h950).le hz2 hz
                        · -- right
                          by_cases h951 : a ≤ ((1329831/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h952 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h953 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h954 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2444_pos (not_le.mp h935).le h951 hz1 h954 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2446_pos (not_le.mp h935).le h951 (not_le.mp h954).le h953 hz
                              · -- right
                                by_cases h955 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2452_pos (not_le.mp h935).le h951 (not_le.mp h953).le h955 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2454_pos (not_le.mp h935).le h951 (not_le.mp h955).le h952 hz
                            · -- right
                              by_cases h956 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h957 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2476_pos (not_le.mp h935).le h951 (not_le.mp h952).le h957 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2478_pos (not_le.mp h935).le h951 (not_le.mp h957).le h956 hz
                              · -- right
                                by_cases h958 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2484_pos (not_le.mp h935).le h951 (not_le.mp h956).le h958 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2486_pos (not_le.mp h935).le h951 (not_le.mp h958).le hz2 hz
                          · -- right
                            by_cases h959 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h960 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h961 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2445_pos (not_le.mp h951).le h902 hz1 h961 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2447_pos (not_le.mp h951).le h902 (not_le.mp h961).le h960 hz
                              · -- right
                                by_cases h962 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B040.e2453_pos (not_le.mp h951).le h902 (not_le.mp h960).le h962 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B040.e2455_pos (not_le.mp h951).le h902 (not_le.mp h962).le h959 hz
                            · -- right
                              by_cases h963 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h964 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2477_pos (not_le.mp h951).le h902 (not_le.mp h959).le h964 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2479_pos (not_le.mp h951).le h902 (not_le.mp h964).le h963 hz
                              · -- right
                                by_cases h965 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2485_pos (not_le.mp h951).le h902 (not_le.mp h963).le h965 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2487_pos (not_le.mp h951).le h902 (not_le.mp h965).le hz2 hz
                    · -- right
                      by_cases h966 : a ≤ ((333519/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h967 : a ≤ ((666189/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h968 : a ≤ ((1331529/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h969 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h970 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h971 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2488_pos (not_le.mp h902).le h968 hz1 h971 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2490_pos (not_le.mp h902).le h968 (not_le.mp h971).le h970 hz
                              · -- right
                                by_cases h972 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2496_pos (not_le.mp h902).le h968 (not_le.mp h970).le h972 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2498_pos (not_le.mp h902).le h968 (not_le.mp h972).le h969 hz
                            · -- right
                              by_cases h973 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h974 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2520_pos (not_le.mp h902).le h968 (not_le.mp h969).le h974 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2522_pos (not_le.mp h902).le h968 (not_le.mp h974).le h973 hz
                              · -- right
                                by_cases h975 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2528_pos (not_le.mp h902).le h968 (not_le.mp h973).le h975 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2530_pos (not_le.mp h902).le h968 (not_le.mp h975).le hz2 hz
                          · -- right
                            by_cases h976 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h977 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h978 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2489_pos (not_le.mp h968).le h967 hz1 h978 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2491_pos (not_le.mp h968).le h967 (not_le.mp h978).le h977 hz
                              · -- right
                                by_cases h979 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2497_pos (not_le.mp h968).le h967 (not_le.mp h977).le h979 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2499_pos (not_le.mp h968).le h967 (not_le.mp h979).le h976 hz
                            · -- right
                              by_cases h980 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h981 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2521_pos (not_le.mp h968).le h967 (not_le.mp h976).le h981 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2523_pos (not_le.mp h968).le h967 (not_le.mp h981).le h980 hz
                              · -- right
                                by_cases h982 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2529_pos (not_le.mp h968).le h967 (not_le.mp h980).le h982 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2531_pos (not_le.mp h968).le h967 (not_le.mp h982).le hz2 hz
                        · -- right
                          by_cases h983 : a ≤ ((1333227/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h984 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h985 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h986 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2492_pos (not_le.mp h967).le h983 hz1 h986 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2494_pos (not_le.mp h967).le h983 (not_le.mp h986).le h985 hz
                              · -- right
                                by_cases h987 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2500_pos (not_le.mp h967).le h983 (not_le.mp h985).le h987 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2502_pos (not_le.mp h967).le h983 (not_le.mp h987).le h984 hz
                            · -- right
                              by_cases h988 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h989 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2524_pos (not_le.mp h967).le h983 (not_le.mp h984).le h989 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2526_pos (not_le.mp h967).le h983 (not_le.mp h989).le h988 hz
                              · -- right
                                by_cases h990 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2532_pos (not_le.mp h967).le h983 (not_le.mp h988).le h990 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2534_pos (not_le.mp h967).le h983 (not_le.mp h990).le hz2 hz
                          · -- right
                            by_cases h991 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h992 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h993 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2493_pos (not_le.mp h983).le h966 hz1 h993 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2495_pos (not_le.mp h983).le h966 (not_le.mp h993).le h992 hz
                              · -- right
                                by_cases h994 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2501_pos (not_le.mp h983).le h966 (not_le.mp h992).le h994 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2503_pos (not_le.mp h983).le h966 (not_le.mp h994).le h991 hz
                            · -- right
                              by_cases h995 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h996 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2525_pos (not_le.mp h983).le h966 (not_le.mp h991).le h996 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2527_pos (not_le.mp h983).le h966 (not_le.mp h996).le h995 hz
                              · -- right
                                by_cases h997 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2533_pos (not_le.mp h983).le h966 (not_le.mp h995).le h997 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2535_pos (not_le.mp h983).le h966 (not_le.mp h997).le hz2 hz
                      · -- right
                        by_cases h998 : a ≤ ((667887/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h999 : a ≤ ((53397/327680 : ℚ) : ℝ)
                          · -- left
                            by_cases h1000 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1001 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1002 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2504_pos (not_le.mp h966).le h999 hz1 h1002 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2506_pos (not_le.mp h966).le h999 (not_le.mp h1002).le h1001 hz
                              · -- right
                                by_cases h1003 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2512_pos (not_le.mp h966).le h999 (not_le.mp h1001).le h1003 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2514_pos (not_le.mp h966).le h999 (not_le.mp h1003).le h1000 hz
                            · -- right
                              by_cases h1004 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1005 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2536_pos (not_le.mp h966).le h999 (not_le.mp h1000).le h1005 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2538_pos (not_le.mp h966).le h999 (not_le.mp h1005).le h1004 hz
                              · -- right
                                by_cases h1006 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2544_pos (not_le.mp h966).le h999 (not_le.mp h1004).le h1006 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2546_pos (not_le.mp h966).le h999 (not_le.mp h1006).le hz2 hz
                          · -- right
                            by_cases h1007 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1008 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1009 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2505_pos (not_le.mp h999).le h998 hz1 h1009 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2507_pos (not_le.mp h999).le h998 (not_le.mp h1009).le h1008 hz
                              · -- right
                                by_cases h1010 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2513_pos (not_le.mp h999).le h998 (not_le.mp h1008).le h1010 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2515_pos (not_le.mp h999).le h998 (not_le.mp h1010).le h1007 hz
                            · -- right
                              by_cases h1011 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1012 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2537_pos (not_le.mp h999).le h998 (not_le.mp h1007).le h1012 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2539_pos (not_le.mp h999).le h998 (not_le.mp h1012).le h1011 hz
                              · -- right
                                by_cases h1013 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2545_pos (not_le.mp h999).le h998 (not_le.mp h1011).le h1013 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2547_pos (not_le.mp h999).le h998 (not_le.mp h1013).le hz2 hz
                        · -- right
                          by_cases h1014 : a ≤ ((1336623/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1015 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1016 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1017 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2508_pos (not_le.mp h998).le h1014 hz1 h1017 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2510_pos (not_le.mp h998).le h1014 (not_le.mp h1017).le h1016 hz
                              · -- right
                                by_cases h1018 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2516_pos (not_le.mp h998).le h1014 (not_le.mp h1016).le h1018 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2518_pos (not_le.mp h998).le h1014 (not_le.mp h1018).le h1015 hz
                            · -- right
                              by_cases h1019 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1020 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2540_pos (not_le.mp h998).le h1014 (not_le.mp h1015).le h1020 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2542_pos (not_le.mp h998).le h1014 (not_le.mp h1020).le h1019 hz
                              · -- right
                                by_cases h1021 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2548_pos (not_le.mp h998).le h1014 (not_le.mp h1019).le h1021 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2550_pos (not_le.mp h998).le h1014 (not_le.mp h1021).le hz2 hz
                          · -- right
                            by_cases h1022 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1023 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1024 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2509_pos (not_le.mp h1014).le h5 hz1 h1024 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2511_pos (not_le.mp h1014).le h5 (not_le.mp h1024).le h1023 hz
                              · -- right
                                by_cases h1025 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B041.e2517_pos (not_le.mp h1014).le h5 (not_le.mp h1023).le h1025 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B041.e2519_pos (not_le.mp h1014).le h5 (not_le.mp h1025).le h1022 hz
                            · -- right
                              by_cases h1026 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1027 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2541_pos (not_le.mp h1014).le h5 (not_le.mp h1022).le h1027 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2543_pos (not_le.mp h1014).le h5 (not_le.mp h1027).le h1026 hz
                              · -- right
                                by_cases h1028 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2549_pos (not_le.mp h1014).le h5 (not_le.mp h1026).le h1028 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2551_pos (not_le.mp h1014).le h5 (not_le.mp h1028).le hz2 hz
            · -- right
              by_cases h1029 : a ≤ ((21747/128000 : ℚ) : ℝ)
              · -- left
                by_cases h1030 : a ≤ ((8529/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h1031 : a ≤ ((84441/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1032 : a ≤ ((168033/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1033 : a ≤ ((335217/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1034 : a ≤ ((133917/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1035 : a ≤ ((1338321/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1036 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1037 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1038 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2552_pos (not_le.mp h5).le h1035 hz1 h1038 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2554_pos (not_le.mp h5).le h1035 (not_le.mp h1038).le h1037 hz
                              · -- right
                                by_cases h1039 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2560_pos (not_le.mp h5).le h1035 (not_le.mp h1037).le h1039 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2562_pos (not_le.mp h5).le h1035 (not_le.mp h1039).le h1036 hz
                            · -- right
                              by_cases h1040 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1041 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2584_pos (not_le.mp h5).le h1035 (not_le.mp h1036).le h1041 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2586_pos (not_le.mp h5).le h1035 (not_le.mp h1041).le h1040 hz
                              · -- right
                                by_cases h1042 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2592_pos (not_le.mp h5).le h1035 (not_le.mp h1040).le h1042 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2594_pos (not_le.mp h5).le h1035 (not_le.mp h1042).le hz2 hz
                          · -- right
                            by_cases h1043 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1044 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1045 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2553_pos (not_le.mp h1035).le h1034 hz1 h1045 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2555_pos (not_le.mp h1035).le h1034 (not_le.mp h1045).le h1044 hz
                              · -- right
                                by_cases h1046 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2561_pos (not_le.mp h1035).le h1034 (not_le.mp h1044).le h1046 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2563_pos (not_le.mp h1035).le h1034 (not_le.mp h1046).le h1043 hz
                            · -- right
                              by_cases h1047 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1048 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2585_pos (not_le.mp h1035).le h1034 (not_le.mp h1043).le h1048 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2587_pos (not_le.mp h1035).le h1034 (not_le.mp h1048).le h1047 hz
                              · -- right
                                by_cases h1049 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2593_pos (not_le.mp h1035).le h1034 (not_le.mp h1047).le h1049 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2595_pos (not_le.mp h1035).le h1034 (not_le.mp h1049).le hz2 hz
                        · -- right
                          by_cases h1050 : a ≤ ((1340019/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1051 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1052 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1053 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2556_pos (not_le.mp h1034).le h1050 hz1 h1053 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2558_pos (not_le.mp h1034).le h1050 (not_le.mp h1053).le h1052 hz
                              · -- right
                                by_cases h1054 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2564_pos (not_le.mp h1034).le h1050 (not_le.mp h1052).le h1054 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2566_pos (not_le.mp h1034).le h1050 (not_le.mp h1054).le h1051 hz
                            · -- right
                              by_cases h1055 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1056 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2588_pos (not_le.mp h1034).le h1050 (not_le.mp h1051).le h1056 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2590_pos (not_le.mp h1034).le h1050 (not_le.mp h1056).le h1055 hz
                              · -- right
                                by_cases h1057 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2596_pos (not_le.mp h1034).le h1050 (not_le.mp h1055).le h1057 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2598_pos (not_le.mp h1034).le h1050 (not_le.mp h1057).le hz2 hz
                          · -- right
                            by_cases h1058 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1059 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1060 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2557_pos (not_le.mp h1050).le h1033 hz1 h1060 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2559_pos (not_le.mp h1050).le h1033 (not_le.mp h1060).le h1059 hz
                              · -- right
                                by_cases h1061 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2565_pos (not_le.mp h1050).le h1033 (not_le.mp h1059).le h1061 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2567_pos (not_le.mp h1050).le h1033 (not_le.mp h1061).le h1058 hz
                            · -- right
                              by_cases h1062 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1063 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2589_pos (not_le.mp h1050).le h1033 (not_le.mp h1058).le h1063 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2591_pos (not_le.mp h1050).le h1033 (not_le.mp h1063).le h1062 hz
                              · -- right
                                by_cases h1064 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2597_pos (not_le.mp h1050).le h1033 (not_le.mp h1062).le h1064 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2599_pos (not_le.mp h1050).le h1033 (not_le.mp h1064).le hz2 hz
                      · -- right
                        by_cases h1065 : a ≤ ((671283/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1066 : a ≤ ((1341717/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1067 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1068 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1069 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2568_pos (not_le.mp h1033).le h1066 hz1 h1069 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2570_pos (not_le.mp h1033).le h1066 (not_le.mp h1069).le h1068 hz
                              · -- right
                                by_cases h1070 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2576_pos (not_le.mp h1033).le h1066 (not_le.mp h1068).le h1070 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2578_pos (not_le.mp h1033).le h1066 (not_le.mp h1070).le h1067 hz
                            · -- right
                              by_cases h1071 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1072 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2600_pos (not_le.mp h1033).le h1066 (not_le.mp h1067).le h1072 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2602_pos (not_le.mp h1033).le h1066 (not_le.mp h1072).le h1071 hz
                              · -- right
                                by_cases h1073 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2608_pos (not_le.mp h1033).le h1066 (not_le.mp h1071).le h1073 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2610_pos (not_le.mp h1033).le h1066 (not_le.mp h1073).le hz2 hz
                          · -- right
                            by_cases h1074 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1075 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1076 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2569_pos (not_le.mp h1066).le h1065 hz1 h1076 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2571_pos (not_le.mp h1066).le h1065 (not_le.mp h1076).le h1075 hz
                              · -- right
                                by_cases h1077 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2577_pos (not_le.mp h1066).le h1065 (not_le.mp h1075).le h1077 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2579_pos (not_le.mp h1066).le h1065 (not_le.mp h1077).le h1074 hz
                            · -- right
                              by_cases h1078 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1079 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2601_pos (not_le.mp h1066).le h1065 (not_le.mp h1074).le h1079 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2603_pos (not_le.mp h1066).le h1065 (not_le.mp h1079).le h1078 hz
                              · -- right
                                by_cases h1080 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2609_pos (not_le.mp h1066).le h1065 (not_le.mp h1078).le h1080 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2611_pos (not_le.mp h1066).le h1065 (not_le.mp h1080).le hz2 hz
                        · -- right
                          by_cases h1081 : a ≤ ((268683/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h1082 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1083 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1084 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2572_pos (not_le.mp h1065).le h1081 hz1 h1084 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2574_pos (not_le.mp h1065).le h1081 (not_le.mp h1084).le h1083 hz
                              · -- right
                                by_cases h1085 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2580_pos (not_le.mp h1065).le h1081 (not_le.mp h1083).le h1085 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2582_pos (not_le.mp h1065).le h1081 (not_le.mp h1085).le h1082 hz
                            · -- right
                              by_cases h1086 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1087 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2604_pos (not_le.mp h1065).le h1081 (not_le.mp h1082).le h1087 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2606_pos (not_le.mp h1065).le h1081 (not_le.mp h1087).le h1086 hz
                              · -- right
                                by_cases h1088 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2612_pos (not_le.mp h1065).le h1081 (not_le.mp h1086).le h1088 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2614_pos (not_le.mp h1065).le h1081 (not_le.mp h1088).le hz2 hz
                          · -- right
                            by_cases h1089 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1090 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1091 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B042.e2573_pos (not_le.mp h1081).le h1032 hz1 h1091 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B042.e2575_pos (not_le.mp h1081).le h1032 (not_le.mp h1091).le h1090 hz
                              · -- right
                                by_cases h1092 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2581_pos (not_le.mp h1081).le h1032 (not_le.mp h1090).le h1092 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2583_pos (not_le.mp h1081).le h1032 (not_le.mp h1092).le h1089 hz
                            · -- right
                              by_cases h1093 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1094 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2605_pos (not_le.mp h1081).le h1032 (not_le.mp h1089).le h1094 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2607_pos (not_le.mp h1081).le h1032 (not_le.mp h1094).le h1093 hz
                              · -- right
                                by_cases h1095 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2613_pos (not_le.mp h1081).le h1032 (not_le.mp h1093).le h1095 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2615_pos (not_le.mp h1081).le h1032 (not_le.mp h1095).le hz2 hz
                    · -- right
                      by_cases h1096 : a ≤ ((67383/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1097 : a ≤ ((672981/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1098 : a ≤ ((1345113/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1099 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1100 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1101 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2616_pos (not_le.mp h1032).le h1098 hz1 h1101 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2618_pos (not_le.mp h1032).le h1098 (not_le.mp h1101).le h1100 hz
                              · -- right
                                by_cases h1102 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2624_pos (not_le.mp h1032).le h1098 (not_le.mp h1100).le h1102 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2626_pos (not_le.mp h1032).le h1098 (not_le.mp h1102).le h1099 hz
                            · -- right
                              by_cases h1103 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1104 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2648_pos (not_le.mp h1032).le h1098 (not_le.mp h1099).le h1104 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2650_pos (not_le.mp h1032).le h1098 (not_le.mp h1104).le h1103 hz
                              · -- right
                                by_cases h1105 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2656_pos (not_le.mp h1032).le h1098 (not_le.mp h1103).le h1105 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2658_pos (not_le.mp h1032).le h1098 (not_le.mp h1105).le hz2 hz
                          · -- right
                            by_cases h1106 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1107 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1108 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2617_pos (not_le.mp h1098).le h1097 hz1 h1108 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2619_pos (not_le.mp h1098).le h1097 (not_le.mp h1108).le h1107 hz
                              · -- right
                                by_cases h1109 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2625_pos (not_le.mp h1098).le h1097 (not_le.mp h1107).le h1109 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2627_pos (not_le.mp h1098).le h1097 (not_le.mp h1109).le h1106 hz
                            · -- right
                              by_cases h1110 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1111 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2649_pos (not_le.mp h1098).le h1097 (not_le.mp h1106).le h1111 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2651_pos (not_le.mp h1098).le h1097 (not_le.mp h1111).le h1110 hz
                              · -- right
                                by_cases h1112 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2657_pos (not_le.mp h1098).le h1097 (not_le.mp h1110).le h1112 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2659_pos (not_le.mp h1098).le h1097 (not_le.mp h1112).le hz2 hz
                        · -- right
                          by_cases h1113 : a ≤ ((1346811/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1114 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1115 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1116 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2620_pos (not_le.mp h1097).le h1113 hz1 h1116 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2622_pos (not_le.mp h1097).le h1113 (not_le.mp h1116).le h1115 hz
                              · -- right
                                by_cases h1117 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2628_pos (not_le.mp h1097).le h1113 (not_le.mp h1115).le h1117 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2630_pos (not_le.mp h1097).le h1113 (not_le.mp h1117).le h1114 hz
                            · -- right
                              by_cases h1118 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1119 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2652_pos (not_le.mp h1097).le h1113 (not_le.mp h1114).le h1119 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2654_pos (not_le.mp h1097).le h1113 (not_le.mp h1119).le h1118 hz
                              · -- right
                                by_cases h1120 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2660_pos (not_le.mp h1097).le h1113 (not_le.mp h1118).le h1120 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2662_pos (not_le.mp h1097).le h1113 (not_le.mp h1120).le hz2 hz
                          · -- right
                            by_cases h1121 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1122 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1123 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2621_pos (not_le.mp h1113).le h1096 hz1 h1123 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2623_pos (not_le.mp h1113).le h1096 (not_le.mp h1123).le h1122 hz
                              · -- right
                                by_cases h1124 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2629_pos (not_le.mp h1113).le h1096 (not_le.mp h1122).le h1124 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2631_pos (not_le.mp h1113).le h1096 (not_le.mp h1124).le h1121 hz
                            · -- right
                              by_cases h1125 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1126 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2653_pos (not_le.mp h1113).le h1096 (not_le.mp h1121).le h1126 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2655_pos (not_le.mp h1113).le h1096 (not_le.mp h1126).le h1125 hz
                              · -- right
                                by_cases h1127 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2661_pos (not_le.mp h1113).le h1096 (not_le.mp h1125).le h1127 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2663_pos (not_le.mp h1113).le h1096 (not_le.mp h1127).le hz2 hz
                      · -- right
                        by_cases h1128 : a ≤ ((674679/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1129 : a ≤ ((1348509/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1130 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1131 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1132 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2632_pos (not_le.mp h1096).le h1129 hz1 h1132 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2634_pos (not_le.mp h1096).le h1129 (not_le.mp h1132).le h1131 hz
                              · -- right
                                by_cases h1133 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2640_pos (not_le.mp h1096).le h1129 (not_le.mp h1131).le h1133 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2642_pos (not_le.mp h1096).le h1129 (not_le.mp h1133).le h1130 hz
                            · -- right
                              by_cases h1134 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1135 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2664_pos (not_le.mp h1096).le h1129 (not_le.mp h1130).le h1135 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2666_pos (not_le.mp h1096).le h1129 (not_le.mp h1135).le h1134 hz
                              · -- right
                                by_cases h1136 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2672_pos (not_le.mp h1096).le h1129 (not_le.mp h1134).le h1136 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2674_pos (not_le.mp h1096).le h1129 (not_le.mp h1136).le hz2 hz
                          · -- right
                            by_cases h1137 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1138 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1139 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2633_pos (not_le.mp h1129).le h1128 hz1 h1139 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2635_pos (not_le.mp h1129).le h1128 (not_le.mp h1139).le h1138 hz
                              · -- right
                                by_cases h1140 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2641_pos (not_le.mp h1129).le h1128 (not_le.mp h1138).le h1140 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2643_pos (not_le.mp h1129).le h1128 (not_le.mp h1140).le h1137 hz
                            · -- right
                              by_cases h1141 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1142 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2665_pos (not_le.mp h1129).le h1128 (not_le.mp h1137).le h1142 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2667_pos (not_le.mp h1129).le h1128 (not_le.mp h1142).le h1141 hz
                              · -- right
                                by_cases h1143 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2673_pos (not_le.mp h1129).le h1128 (not_le.mp h1141).le h1143 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2675_pos (not_le.mp h1129).le h1128 (not_le.mp h1143).le hz2 hz
                        · -- right
                          by_cases h1144 : a ≤ ((1350207/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1145 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1146 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1147 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2636_pos (not_le.mp h1128).le h1144 hz1 h1147 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2638_pos (not_le.mp h1128).le h1144 (not_le.mp h1147).le h1146 hz
                              · -- right
                                by_cases h1148 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2644_pos (not_le.mp h1128).le h1144 (not_le.mp h1146).le h1148 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2646_pos (not_le.mp h1128).le h1144 (not_le.mp h1148).le h1145 hz
                            · -- right
                              by_cases h1149 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1150 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2668_pos (not_le.mp h1128).le h1144 (not_le.mp h1145).le h1150 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2670_pos (not_le.mp h1128).le h1144 (not_le.mp h1150).le h1149 hz
                              · -- right
                                by_cases h1151 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2676_pos (not_le.mp h1128).le h1144 (not_le.mp h1149).le h1151 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2678_pos (not_le.mp h1128).le h1144 (not_le.mp h1151).le hz2 hz
                          · -- right
                            by_cases h1152 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1153 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1154 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B043.e2637_pos (not_le.mp h1144).le h1031 hz1 h1154 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B043.e2639_pos (not_le.mp h1144).le h1031 (not_le.mp h1154).le h1153 hz
                              · -- right
                                by_cases h1155 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2645_pos (not_le.mp h1144).le h1031 (not_le.mp h1153).le h1155 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2647_pos (not_le.mp h1144).le h1031 (not_le.mp h1155).le h1152 hz
                            · -- right
                              by_cases h1156 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1157 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2669_pos (not_le.mp h1144).le h1031 (not_le.mp h1152).le h1157 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2671_pos (not_le.mp h1144).le h1031 (not_le.mp h1157).le h1156 hz
                              · -- right
                                by_cases h1158 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2677_pos (not_le.mp h1144).le h1031 (not_le.mp h1156).le h1158 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2679_pos (not_le.mp h1144).le h1031 (not_le.mp h1158).le hz2 hz
                  · -- right
                    by_cases h1159 : a ≤ ((169731/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1160 : a ≤ ((338613/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1161 : a ≤ ((676377/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1162 : a ≤ ((270381/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h1163 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1164 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1165 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2680_pos (not_le.mp h1031).le h1162 hz1 h1165 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2682_pos (not_le.mp h1031).le h1162 (not_le.mp h1165).le h1164 hz
                              · -- right
                                by_cases h1166 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2688_pos (not_le.mp h1031).le h1162 (not_le.mp h1164).le h1166 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2690_pos (not_le.mp h1031).le h1162 (not_le.mp h1166).le h1163 hz
                            · -- right
                              by_cases h1167 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1168 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2712_pos (not_le.mp h1031).le h1162 (not_le.mp h1163).le h1168 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2714_pos (not_le.mp h1031).le h1162 (not_le.mp h1168).le h1167 hz
                              · -- right
                                by_cases h1169 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2720_pos (not_le.mp h1031).le h1162 (not_le.mp h1167).le h1169 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2722_pos (not_le.mp h1031).le h1162 (not_le.mp h1169).le hz2 hz
                          · -- right
                            by_cases h1170 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1171 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1172 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2681_pos (not_le.mp h1162).le h1161 hz1 h1172 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2683_pos (not_le.mp h1162).le h1161 (not_le.mp h1172).le h1171 hz
                              · -- right
                                by_cases h1173 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2689_pos (not_le.mp h1162).le h1161 (not_le.mp h1171).le h1173 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2691_pos (not_le.mp h1162).le h1161 (not_le.mp h1173).le h1170 hz
                            · -- right
                              by_cases h1174 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1175 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2713_pos (not_le.mp h1162).le h1161 (not_le.mp h1170).le h1175 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2715_pos (not_le.mp h1162).le h1161 (not_le.mp h1175).le h1174 hz
                              · -- right
                                by_cases h1176 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2721_pos (not_le.mp h1162).le h1161 (not_le.mp h1174).le h1176 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2723_pos (not_le.mp h1162).le h1161 (not_le.mp h1176).le hz2 hz
                        · -- right
                          by_cases h1177 : a ≤ ((1353603/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1178 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1179 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1180 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2684_pos (not_le.mp h1161).le h1177 hz1 h1180 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2686_pos (not_le.mp h1161).le h1177 (not_le.mp h1180).le h1179 hz
                              · -- right
                                by_cases h1181 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2692_pos (not_le.mp h1161).le h1177 (not_le.mp h1179).le h1181 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2694_pos (not_le.mp h1161).le h1177 (not_le.mp h1181).le h1178 hz
                            · -- right
                              by_cases h1182 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1183 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2716_pos (not_le.mp h1161).le h1177 (not_le.mp h1178).le h1183 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2718_pos (not_le.mp h1161).le h1177 (not_le.mp h1183).le h1182 hz
                              · -- right
                                by_cases h1184 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2724_pos (not_le.mp h1161).le h1177 (not_le.mp h1182).le h1184 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2726_pos (not_le.mp h1161).le h1177 (not_le.mp h1184).le hz2 hz
                          · -- right
                            by_cases h1185 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1186 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1187 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2685_pos (not_le.mp h1177).le h1160 hz1 h1187 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2687_pos (not_le.mp h1177).le h1160 (not_le.mp h1187).le h1186 hz
                              · -- right
                                by_cases h1188 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2693_pos (not_le.mp h1177).le h1160 (not_le.mp h1186).le h1188 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2695_pos (not_le.mp h1177).le h1160 (not_le.mp h1188).le h1185 hz
                            · -- right
                              by_cases h1189 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1190 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2717_pos (not_le.mp h1177).le h1160 (not_le.mp h1185).le h1190 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2719_pos (not_le.mp h1177).le h1160 (not_le.mp h1190).le h1189 hz
                              · -- right
                                by_cases h1191 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2725_pos (not_le.mp h1177).le h1160 (not_le.mp h1189).le h1191 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2727_pos (not_le.mp h1177).le h1160 (not_le.mp h1191).le hz2 hz
                      · -- right
                        by_cases h1192 : a ≤ ((27123/163840 : ℚ) : ℝ)
                        · -- left
                          by_cases h1193 : a ≤ ((1355301/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1194 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1195 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1196 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2696_pos (not_le.mp h1160).le h1193 hz1 h1196 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2698_pos (not_le.mp h1160).le h1193 (not_le.mp h1196).le h1195 hz
                              · -- right
                                by_cases h1197 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2704_pos (not_le.mp h1160).le h1193 (not_le.mp h1195).le h1197 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2706_pos (not_le.mp h1160).le h1193 (not_le.mp h1197).le h1194 hz
                            · -- right
                              by_cases h1198 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1199 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2728_pos (not_le.mp h1160).le h1193 (not_le.mp h1194).le h1199 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2730_pos (not_le.mp h1160).le h1193 (not_le.mp h1199).le h1198 hz
                              · -- right
                                by_cases h1200 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2736_pos (not_le.mp h1160).le h1193 (not_le.mp h1198).le h1200 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2738_pos (not_le.mp h1160).le h1193 (not_le.mp h1200).le hz2 hz
                          · -- right
                            by_cases h1201 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1202 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1203 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B044.e2697_pos (not_le.mp h1193).le h1192 hz1 h1203 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B044.e2699_pos (not_le.mp h1193).le h1192 (not_le.mp h1203).le h1202 hz
                              · -- right
                                by_cases h1204 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2705_pos (not_le.mp h1193).le h1192 (not_le.mp h1202).le h1204 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2707_pos (not_le.mp h1193).le h1192 (not_le.mp h1204).le h1201 hz
                            · -- right
                              by_cases h1205 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1206 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2729_pos (not_le.mp h1193).le h1192 (not_le.mp h1201).le h1206 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2731_pos (not_le.mp h1193).le h1192 (not_le.mp h1206).le h1205 hz
                              · -- right
                                by_cases h1207 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2737_pos (not_le.mp h1193).le h1192 (not_le.mp h1205).le h1207 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2739_pos (not_le.mp h1193).le h1192 (not_le.mp h1207).le hz2 hz
                        · -- right
                          by_cases h1208 : a ≤ ((1356999/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1209 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1210 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1211 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2700_pos (not_le.mp h1192).le h1208 hz1 h1211 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2702_pos (not_le.mp h1192).le h1208 (not_le.mp h1211).le h1210 hz
                              · -- right
                                by_cases h1212 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2708_pos (not_le.mp h1192).le h1208 (not_le.mp h1210).le h1212 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2710_pos (not_le.mp h1192).le h1208 (not_le.mp h1212).le h1209 hz
                            · -- right
                              by_cases h1213 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1214 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2732_pos (not_le.mp h1192).le h1208 (not_le.mp h1209).le h1214 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2734_pos (not_le.mp h1192).le h1208 (not_le.mp h1214).le h1213 hz
                              · -- right
                                by_cases h1215 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2740_pos (not_le.mp h1192).le h1208 (not_le.mp h1213).le h1215 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2742_pos (not_le.mp h1192).le h1208 (not_le.mp h1215).le hz2 hz
                          · -- right
                            by_cases h1216 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1217 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1218 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2701_pos (not_le.mp h1208).le h1159 hz1 h1218 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2703_pos (not_le.mp h1208).le h1159 (not_le.mp h1218).le h1217 hz
                              · -- right
                                by_cases h1219 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2709_pos (not_le.mp h1208).le h1159 (not_le.mp h1217).le h1219 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2711_pos (not_le.mp h1208).le h1159 (not_le.mp h1219).le h1216 hz
                            · -- right
                              by_cases h1220 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1221 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2733_pos (not_le.mp h1208).le h1159 (not_le.mp h1216).le h1221 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2735_pos (not_le.mp h1208).le h1159 (not_le.mp h1221).le h1220 hz
                              · -- right
                                by_cases h1222 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2741_pos (not_le.mp h1208).le h1159 (not_le.mp h1220).le h1222 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2743_pos (not_le.mp h1208).le h1159 (not_le.mp h1222).le hz2 hz
                    · -- right
                      by_cases h1223 : a ≤ ((340311/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1224 : a ≤ ((679773/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1225 : a ≤ ((1358697/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1226 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1227 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1228 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2744_pos (not_le.mp h1159).le h1225 hz1 h1228 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2746_pos (not_le.mp h1159).le h1225 (not_le.mp h1228).le h1227 hz
                              · -- right
                                by_cases h1229 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2752_pos (not_le.mp h1159).le h1225 (not_le.mp h1227).le h1229 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2754_pos (not_le.mp h1159).le h1225 (not_le.mp h1229).le h1226 hz
                            · -- right
                              by_cases h1230 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1231 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2776_pos (not_le.mp h1159).le h1225 (not_le.mp h1226).le h1231 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2778_pos (not_le.mp h1159).le h1225 (not_le.mp h1231).le h1230 hz
                              · -- right
                                by_cases h1232 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2784_pos (not_le.mp h1159).le h1225 (not_le.mp h1230).le h1232 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2786_pos (not_le.mp h1159).le h1225 (not_le.mp h1232).le hz2 hz
                          · -- right
                            by_cases h1233 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1234 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1235 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2745_pos (not_le.mp h1225).le h1224 hz1 h1235 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2747_pos (not_le.mp h1225).le h1224 (not_le.mp h1235).le h1234 hz
                              · -- right
                                by_cases h1236 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2753_pos (not_le.mp h1225).le h1224 (not_le.mp h1234).le h1236 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2755_pos (not_le.mp h1225).le h1224 (not_le.mp h1236).le h1233 hz
                            · -- right
                              by_cases h1237 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1238 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2777_pos (not_le.mp h1225).le h1224 (not_le.mp h1233).le h1238 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2779_pos (not_le.mp h1225).le h1224 (not_le.mp h1238).le h1237 hz
                              · -- right
                                by_cases h1239 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2785_pos (not_le.mp h1225).le h1224 (not_le.mp h1237).le h1239 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2787_pos (not_le.mp h1225).le h1224 (not_le.mp h1239).le hz2 hz
                        · -- right
                          by_cases h1240 : a ≤ ((272079/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h1241 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1242 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1243 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2748_pos (not_le.mp h1224).le h1240 hz1 h1243 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2750_pos (not_le.mp h1224).le h1240 (not_le.mp h1243).le h1242 hz
                              · -- right
                                by_cases h1244 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2756_pos (not_le.mp h1224).le h1240 (not_le.mp h1242).le h1244 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2758_pos (not_le.mp h1224).le h1240 (not_le.mp h1244).le h1241 hz
                            · -- right
                              by_cases h1245 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1246 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2780_pos (not_le.mp h1224).le h1240 (not_le.mp h1241).le h1246 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2782_pos (not_le.mp h1224).le h1240 (not_le.mp h1246).le h1245 hz
                              · -- right
                                by_cases h1247 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2788_pos (not_le.mp h1224).le h1240 (not_le.mp h1245).le h1247 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2790_pos (not_le.mp h1224).le h1240 (not_le.mp h1247).le hz2 hz
                          · -- right
                            by_cases h1248 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1249 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1250 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2749_pos (not_le.mp h1240).le h1223 hz1 h1250 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2751_pos (not_le.mp h1240).le h1223 (not_le.mp h1250).le h1249 hz
                              · -- right
                                by_cases h1251 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B045.e2757_pos (not_le.mp h1240).le h1223 (not_le.mp h1249).le h1251 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B045.e2759_pos (not_le.mp h1240).le h1223 (not_le.mp h1251).le h1248 hz
                            · -- right
                              by_cases h1252 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1253 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2781_pos (not_le.mp h1240).le h1223 (not_le.mp h1248).le h1253 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2783_pos (not_le.mp h1240).le h1223 (not_le.mp h1253).le h1252 hz
                              · -- right
                                by_cases h1254 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2789_pos (not_le.mp h1240).le h1223 (not_le.mp h1252).le h1254 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2791_pos (not_le.mp h1240).le h1223 (not_le.mp h1254).le hz2 hz
                      · -- right
                        by_cases h1255 : a ≤ ((681471/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1256 : a ≤ ((1362093/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1257 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1258 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1259 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2760_pos (not_le.mp h1223).le h1256 hz1 h1259 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2762_pos (not_le.mp h1223).le h1256 (not_le.mp h1259).le h1258 hz
                              · -- right
                                by_cases h1260 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2768_pos (not_le.mp h1223).le h1256 (not_le.mp h1258).le h1260 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2770_pos (not_le.mp h1223).le h1256 (not_le.mp h1260).le h1257 hz
                            · -- right
                              by_cases h1261 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1262 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2792_pos (not_le.mp h1223).le h1256 (not_le.mp h1257).le h1262 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2794_pos (not_le.mp h1223).le h1256 (not_le.mp h1262).le h1261 hz
                              · -- right
                                by_cases h1263 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2800_pos (not_le.mp h1223).le h1256 (not_le.mp h1261).le h1263 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2802_pos (not_le.mp h1223).le h1256 (not_le.mp h1263).le hz2 hz
                          · -- right
                            by_cases h1264 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1265 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1266 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2761_pos (not_le.mp h1256).le h1255 hz1 h1266 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2763_pos (not_le.mp h1256).le h1255 (not_le.mp h1266).le h1265 hz
                              · -- right
                                by_cases h1267 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2769_pos (not_le.mp h1256).le h1255 (not_le.mp h1265).le h1267 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2771_pos (not_le.mp h1256).le h1255 (not_le.mp h1267).le h1264 hz
                            · -- right
                              by_cases h1268 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1269 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2793_pos (not_le.mp h1256).le h1255 (not_le.mp h1264).le h1269 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2795_pos (not_le.mp h1256).le h1255 (not_le.mp h1269).le h1268 hz
                              · -- right
                                by_cases h1270 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2801_pos (not_le.mp h1256).le h1255 (not_le.mp h1268).le h1270 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2803_pos (not_le.mp h1256).le h1255 (not_le.mp h1270).le hz2 hz
                        · -- right
                          by_cases h1271 : a ≤ ((1363791/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1272 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1273 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1274 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2764_pos (not_le.mp h1255).le h1271 hz1 h1274 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2766_pos (not_le.mp h1255).le h1271 (not_le.mp h1274).le h1273 hz
                              · -- right
                                by_cases h1275 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2772_pos (not_le.mp h1255).le h1271 (not_le.mp h1273).le h1275 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2774_pos (not_le.mp h1255).le h1271 (not_le.mp h1275).le h1272 hz
                            · -- right
                              by_cases h1276 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1277 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2796_pos (not_le.mp h1255).le h1271 (not_le.mp h1272).le h1277 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2798_pos (not_le.mp h1255).le h1271 (not_le.mp h1277).le h1276 hz
                              · -- right
                                by_cases h1278 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2804_pos (not_le.mp h1255).le h1271 (not_le.mp h1276).le h1278 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2806_pos (not_le.mp h1255).le h1271 (not_le.mp h1278).le hz2 hz
                          · -- right
                            by_cases h1279 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1280 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1281 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2765_pos (not_le.mp h1271).le h1030 hz1 h1281 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2767_pos (not_le.mp h1271).le h1030 (not_le.mp h1281).le h1280 hz
                              · -- right
                                by_cases h1282 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2773_pos (not_le.mp h1271).le h1030 (not_le.mp h1280).le h1282 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2775_pos (not_le.mp h1271).le h1030 (not_le.mp h1282).le h1279 hz
                            · -- right
                              by_cases h1283 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1284 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2797_pos (not_le.mp h1271).le h1030 (not_le.mp h1279).le h1284 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2799_pos (not_le.mp h1271).le h1030 (not_le.mp h1284).le h1283 hz
                              · -- right
                                by_cases h1285 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2805_pos (not_le.mp h1271).le h1030 (not_le.mp h1283).le h1285 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2807_pos (not_le.mp h1271).le h1030 (not_le.mp h1285).le hz2 hz
                · -- right
                  by_cases h1286 : a ≤ ((86139/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1287 : a ≤ ((171429/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1288 : a ≤ ((342009/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1289 : a ≤ ((683169/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1290 : a ≤ ((1365489/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1291 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1292 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1293 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2808_pos (not_le.mp h1030).le h1290 hz1 h1293 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2810_pos (not_le.mp h1030).le h1290 (not_le.mp h1293).le h1292 hz
                              · -- right
                                by_cases h1294 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2816_pos (not_le.mp h1030).le h1290 (not_le.mp h1292).le h1294 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2818_pos (not_le.mp h1030).le h1290 (not_le.mp h1294).le h1291 hz
                            · -- right
                              by_cases h1295 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1296 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2840_pos (not_le.mp h1030).le h1290 (not_le.mp h1291).le h1296 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2842_pos (not_le.mp h1030).le h1290 (not_le.mp h1296).le h1295 hz
                              · -- right
                                by_cases h1297 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2848_pos (not_le.mp h1030).le h1290 (not_le.mp h1295).le h1297 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2850_pos (not_le.mp h1030).le h1290 (not_le.mp h1297).le hz2 hz
                          · -- right
                            by_cases h1298 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1299 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1300 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2809_pos (not_le.mp h1290).le h1289 hz1 h1300 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2811_pos (not_le.mp h1290).le h1289 (not_le.mp h1300).le h1299 hz
                              · -- right
                                by_cases h1301 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2817_pos (not_le.mp h1290).le h1289 (not_le.mp h1299).le h1301 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2819_pos (not_le.mp h1290).le h1289 (not_le.mp h1301).le h1298 hz
                            · -- right
                              by_cases h1302 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1303 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2841_pos (not_le.mp h1290).le h1289 (not_le.mp h1298).le h1303 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2843_pos (not_le.mp h1290).le h1289 (not_le.mp h1303).le h1302 hz
                              · -- right
                                by_cases h1304 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2849_pos (not_le.mp h1290).le h1289 (not_le.mp h1302).le h1304 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2851_pos (not_le.mp h1290).le h1289 (not_le.mp h1304).le hz2 hz
                        · -- right
                          by_cases h1305 : a ≤ ((1367187/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1306 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1307 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1308 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2812_pos (not_le.mp h1289).le h1305 hz1 h1308 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2814_pos (not_le.mp h1289).le h1305 (not_le.mp h1308).le h1307 hz
                              · -- right
                                by_cases h1309 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2820_pos (not_le.mp h1289).le h1305 (not_le.mp h1307).le h1309 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2822_pos (not_le.mp h1289).le h1305 (not_le.mp h1309).le h1306 hz
                            · -- right
                              by_cases h1310 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1311 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2844_pos (not_le.mp h1289).le h1305 (not_le.mp h1306).le h1311 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2846_pos (not_le.mp h1289).le h1305 (not_le.mp h1311).le h1310 hz
                              · -- right
                                by_cases h1312 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2852_pos (not_le.mp h1289).le h1305 (not_le.mp h1310).le h1312 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2854_pos (not_le.mp h1289).le h1305 (not_le.mp h1312).le hz2 hz
                          · -- right
                            by_cases h1313 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1314 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1315 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B046.e2813_pos (not_le.mp h1305).le h1288 hz1 h1315 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B046.e2815_pos (not_le.mp h1305).le h1288 (not_le.mp h1315).le h1314 hz
                              · -- right
                                by_cases h1316 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2821_pos (not_le.mp h1305).le h1288 (not_le.mp h1314).le h1316 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2823_pos (not_le.mp h1305).le h1288 (not_le.mp h1316).le h1313 hz
                            · -- right
                              by_cases h1317 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1318 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2845_pos (not_le.mp h1305).le h1288 (not_le.mp h1313).le h1318 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2847_pos (not_le.mp h1305).le h1288 (not_le.mp h1318).le h1317 hz
                              · -- right
                                by_cases h1319 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2853_pos (not_le.mp h1305).le h1288 (not_le.mp h1317).le h1319 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2855_pos (not_le.mp h1305).le h1288 (not_le.mp h1319).le hz2 hz
                      · -- right
                        by_cases h1320 : a ≤ ((684867/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1321 : a ≤ ((273777/1638400 : ℚ) : ℝ)
                          · -- left
                            by_cases h1322 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1323 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1324 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2824_pos (not_le.mp h1288).le h1321 hz1 h1324 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2826_pos (not_le.mp h1288).le h1321 (not_le.mp h1324).le h1323 hz
                              · -- right
                                by_cases h1325 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2832_pos (not_le.mp h1288).le h1321 (not_le.mp h1323).le h1325 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2834_pos (not_le.mp h1288).le h1321 (not_le.mp h1325).le h1322 hz
                            · -- right
                              by_cases h1326 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1327 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2856_pos (not_le.mp h1288).le h1321 (not_le.mp h1322).le h1327 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2858_pos (not_le.mp h1288).le h1321 (not_le.mp h1327).le h1326 hz
                              · -- right
                                by_cases h1328 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2864_pos (not_le.mp h1288).le h1321 (not_le.mp h1326).le h1328 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2866_pos (not_le.mp h1288).le h1321 (not_le.mp h1328).le hz2 hz
                          · -- right
                            by_cases h1329 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1330 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1331 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2825_pos (not_le.mp h1321).le h1320 hz1 h1331 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2827_pos (not_le.mp h1321).le h1320 (not_le.mp h1331).le h1330 hz
                              · -- right
                                by_cases h1332 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2833_pos (not_le.mp h1321).le h1320 (not_le.mp h1330).le h1332 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2835_pos (not_le.mp h1321).le h1320 (not_le.mp h1332).le h1329 hz
                            · -- right
                              by_cases h1333 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1334 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2857_pos (not_le.mp h1321).le h1320 (not_le.mp h1329).le h1334 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2859_pos (not_le.mp h1321).le h1320 (not_le.mp h1334).le h1333 hz
                              · -- right
                                by_cases h1335 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2865_pos (not_le.mp h1321).le h1320 (not_le.mp h1333).le h1335 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2867_pos (not_le.mp h1321).le h1320 (not_le.mp h1335).le hz2 hz
                        · -- right
                          by_cases h1336 : a ≤ ((1370583/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1337 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1338 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1339 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2828_pos (not_le.mp h1320).le h1336 hz1 h1339 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2830_pos (not_le.mp h1320).le h1336 (not_le.mp h1339).le h1338 hz
                              · -- right
                                by_cases h1340 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2836_pos (not_le.mp h1320).le h1336 (not_le.mp h1338).le h1340 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2838_pos (not_le.mp h1320).le h1336 (not_le.mp h1340).le h1337 hz
                            · -- right
                              by_cases h1341 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1342 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2860_pos (not_le.mp h1320).le h1336 (not_le.mp h1337).le h1342 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2862_pos (not_le.mp h1320).le h1336 (not_le.mp h1342).le h1341 hz
                              · -- right
                                by_cases h1343 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2868_pos (not_le.mp h1320).le h1336 (not_le.mp h1341).le h1343 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2870_pos (not_le.mp h1320).le h1336 (not_le.mp h1343).le hz2 hz
                          · -- right
                            by_cases h1344 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1345 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1346 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2829_pos (not_le.mp h1336).le h1287 hz1 h1346 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2831_pos (not_le.mp h1336).le h1287 (not_le.mp h1346).le h1345 hz
                              · -- right
                                by_cases h1347 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2837_pos (not_le.mp h1336).le h1287 (not_le.mp h1345).le h1347 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2839_pos (not_le.mp h1336).le h1287 (not_le.mp h1347).le h1344 hz
                            · -- right
                              by_cases h1348 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1349 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2861_pos (not_le.mp h1336).le h1287 (not_le.mp h1344).le h1349 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2863_pos (not_le.mp h1336).le h1287 (not_le.mp h1349).le h1348 hz
                              · -- right
                                by_cases h1350 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2869_pos (not_le.mp h1336).le h1287 (not_le.mp h1348).le h1350 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2871_pos (not_le.mp h1336).le h1287 (not_le.mp h1350).le hz2 hz
                    · -- right
                      by_cases h1351 : a ≤ ((343707/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1352 : a ≤ ((137313/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1353 : a ≤ ((1372281/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1354 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1355 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1356 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2872_pos (not_le.mp h1287).le h1353 hz1 h1356 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2874_pos (not_le.mp h1287).le h1353 (not_le.mp h1356).le h1355 hz
                              · -- right
                                by_cases h1357 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2880_pos (not_le.mp h1287).le h1353 (not_le.mp h1355).le h1357 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2882_pos (not_le.mp h1287).le h1353 (not_le.mp h1357).le h1354 hz
                            · -- right
                              by_cases h1358 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1359 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2896_pos (not_le.mp h1287).le h1353 (not_le.mp h1354).le h1359 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2898_pos (not_le.mp h1287).le h1353 (not_le.mp h1359).le h1358 hz
                              · -- right
                                by_cases h1360 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2904_pos (not_le.mp h1287).le h1353 (not_le.mp h1358).le h1360 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2906_pos (not_le.mp h1287).le h1353 (not_le.mp h1360).le hz2 hz
                          · -- right
                            by_cases h1361 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1362 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1363 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2873_pos (not_le.mp h1353).le h1352 hz1 h1363 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2875_pos (not_le.mp h1353).le h1352 (not_le.mp h1363).le h1362 hz
                              · -- right
                                by_cases h1364 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2881_pos (not_le.mp h1353).le h1352 (not_le.mp h1362).le h1364 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2883_pos (not_le.mp h1353).le h1352 (not_le.mp h1364).le h1361 hz
                            · -- right
                              by_cases h1365 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1366 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2897_pos (not_le.mp h1353).le h1352 (not_le.mp h1361).le h1366 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2899_pos (not_le.mp h1353).le h1352 (not_le.mp h1366).le h1365 hz
                              · -- right
                                by_cases h1367 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2905_pos (not_le.mp h1353).le h1352 (not_le.mp h1365).le h1367 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2907_pos (not_le.mp h1353).le h1352 (not_le.mp h1367).le hz2 hz
                        · -- right
                          by_cases h1368 : a ≤ ((1373979/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1369 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1370 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1371 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2876_pos (not_le.mp h1352).le h1368 hz1 h1371 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2878_pos (not_le.mp h1352).le h1368 (not_le.mp h1371).le h1370 hz
                              · -- right
                                by_cases h1372 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2884_pos (not_le.mp h1352).le h1368 (not_le.mp h1370).le h1372 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2886_pos (not_le.mp h1352).le h1368 (not_le.mp h1372).le h1369 hz
                            · -- right
                              by_cases h1373 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1374 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2900_pos (not_le.mp h1352).le h1368 (not_le.mp h1369).le h1374 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2902_pos (not_le.mp h1352).le h1368 (not_le.mp h1374).le h1373 hz
                              · -- right
                                by_cases h1375 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2908_pos (not_le.mp h1352).le h1368 (not_le.mp h1373).le h1375 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2910_pos (not_le.mp h1352).le h1368 (not_le.mp h1375).le hz2 hz
                          · -- right
                            by_cases h1376 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1377 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1378 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B047.e2877_pos (not_le.mp h1368).le h1351 hz1 h1378 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B047.e2879_pos (not_le.mp h1368).le h1351 (not_le.mp h1378).le h1377 hz
                              · -- right
                                by_cases h1379 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2885_pos (not_le.mp h1368).le h1351 (not_le.mp h1377).le h1379 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2887_pos (not_le.mp h1368).le h1351 (not_le.mp h1379).le h1376 hz
                            · -- right
                              by_cases h1380 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1381 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2901_pos (not_le.mp h1368).le h1351 (not_le.mp h1376).le h1381 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2903_pos (not_le.mp h1368).le h1351 (not_le.mp h1381).le h1380 hz
                              · -- right
                                by_cases h1382 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2909_pos (not_le.mp h1368).le h1351 (not_le.mp h1380).le h1382 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2911_pos (not_le.mp h1368).le h1351 (not_le.mp h1382).le hz2 hz
                      · -- right
                        by_cases h1383 : a ≤ ((688263/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1384 : a ≤ ((1375677/8192000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1385 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1386 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1387 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2888_pos (not_le.mp h1351).le h1384 hz1 h1387 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2890_pos (not_le.mp h1351).le h1384 (not_le.mp h1387).le h1386 hz
                              · -- right
                                by_cases h1388 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2892_pos (not_le.mp h1351).le h1384 (not_le.mp h1386).le h1388 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2894_pos (not_le.mp h1351).le h1384 (not_le.mp h1388).le h1385 hz
                            · -- right
                              by_cases h1389 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1390 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2912_pos (not_le.mp h1351).le h1384 (not_le.mp h1385).le h1390 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2914_pos (not_le.mp h1351).le h1384 (not_le.mp h1390).le h1389 hz
                              · -- right
                                by_cases h1391 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2916_pos (not_le.mp h1351).le h1384 (not_le.mp h1389).le h1391 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2918_pos (not_le.mp h1351).le h1384 (not_le.mp h1391).le hz2 hz
                          · -- right
                            by_cases h1392 : z ≤ ((1999/2000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1393 : z ≤ ((3997/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1394 : z ≤ ((7993/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2889_pos (not_le.mp h1384).le h1383 hz1 h1394 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2891_pos (not_le.mp h1384).le h1383 (not_le.mp h1394).le h1393 hz
                              · -- right
                                by_cases h1395 : z ≤ ((1599/1600 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2893_pos (not_le.mp h1384).le h1383 (not_le.mp h1393).le h1395 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2895_pos (not_le.mp h1384).le h1383 (not_le.mp h1395).le h1392 hz
                            · -- right
                              by_cases h1396 : z ≤ ((3999/4000 : ℚ) : ℝ)
                              · -- left
                                by_cases h1397 : z ≤ ((7997/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2913_pos (not_le.mp h1384).le h1383 (not_le.mp h1392).le h1397 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2915_pos (not_le.mp h1384).le h1383 (not_le.mp h1397).le h1396 hz
                              · -- right
                                by_cases h1398 : z ≤ ((7999/8000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2917_pos (not_le.mp h1384).le h1383 (not_le.mp h1396).le h1398 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2919_pos (not_le.mp h1384).le h1383 (not_le.mp h1398).le hz2 hz
                        · -- right
                          by_cases h1399 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1400 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1401 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1419_pos (not_le.mp h1383).le h1286 hz1 h1401 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1420_pos (not_le.mp h1383).le h1286 (not_le.mp h1401).le h1400 hz
                            · -- right
                              by_cases h1402 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1421_pos (not_le.mp h1383).le h1286 (not_le.mp h1400).le h1402 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1422_pos (not_le.mp h1383).le h1286 (not_le.mp h1402).le h1399 hz
                          · -- right
                            by_cases h1403 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1404 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1423_pos (not_le.mp h1383).le h1286 (not_le.mp h1399).le h1404 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1424_pos (not_le.mp h1383).le h1286 (not_le.mp h1404).le h1403 hz
                            · -- right
                              by_cases h1405 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1425_pos (not_le.mp h1383).le h1286 (not_le.mp h1403).le h1405 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1426_pos (not_le.mp h1383).le h1286 (not_le.mp h1405).le hz2 hz
                  · -- right
                    by_cases h1406 : a ≤ ((173127/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1407 : a ≤ ((69081/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1408 : a ≤ ((689961/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1409 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1410 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1411 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1427_pos (not_le.mp h1286).le h1408 hz1 h1411 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1428_pos (not_le.mp h1286).le h1408 (not_le.mp h1411).le h1410 hz
                            · -- right
                              by_cases h1412 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1431_pos (not_le.mp h1286).le h1408 (not_le.mp h1410).le h1412 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1432_pos (not_le.mp h1286).le h1408 (not_le.mp h1412).le h1409 hz
                          · -- right
                            by_cases h1413 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1414 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1443_pos (not_le.mp h1286).le h1408 (not_le.mp h1409).le h1414 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1444_pos (not_le.mp h1286).le h1408 (not_le.mp h1414).le h1413 hz
                            · -- right
                              by_cases h1415 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1447_pos (not_le.mp h1286).le h1408 (not_le.mp h1413).le h1415 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1448_pos (not_le.mp h1286).le h1408 (not_le.mp h1415).le hz2 hz
                        · -- right
                          by_cases h1416 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1417 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1418 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1429_pos (not_le.mp h1408).le h1407 hz1 h1418 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1430_pos (not_le.mp h1408).le h1407 (not_le.mp h1418).le h1417 hz
                            · -- right
                              by_cases h1419 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1433_pos (not_le.mp h1408).le h1407 (not_le.mp h1417).le h1419 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1434_pos (not_le.mp h1408).le h1407 (not_le.mp h1419).le h1416 hz
                          · -- right
                            by_cases h1420 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1421 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1445_pos (not_le.mp h1408).le h1407 (not_le.mp h1416).le h1421 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1446_pos (not_le.mp h1408).le h1407 (not_le.mp h1421).le h1420 hz
                            · -- right
                              by_cases h1422 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1449_pos (not_le.mp h1408).le h1407 (not_le.mp h1420).le h1422 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1450_pos (not_le.mp h1408).le h1407 (not_le.mp h1422).le hz2 hz
                      · -- right
                        by_cases h1423 : a ≤ ((691659/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1424 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1425 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1426 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1435_pos (not_le.mp h1407).le h1423 hz1 h1426 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1436_pos (not_le.mp h1407).le h1423 (not_le.mp h1426).le h1425 hz
                            · -- right
                              by_cases h1427 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1439_pos (not_le.mp h1407).le h1423 (not_le.mp h1425).le h1427 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1440_pos (not_le.mp h1407).le h1423 (not_le.mp h1427).le h1424 hz
                          · -- right
                            by_cases h1428 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1429 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1451_pos (not_le.mp h1407).le h1423 (not_le.mp h1424).le h1429 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1452_pos (not_le.mp h1407).le h1423 (not_le.mp h1429).le h1428 hz
                            · -- right
                              by_cases h1430 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1455_pos (not_le.mp h1407).le h1423 (not_le.mp h1428).le h1430 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1456_pos (not_le.mp h1407).le h1423 (not_le.mp h1430).le hz2 hz
                        · -- right
                          by_cases h1431 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1432 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1433 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B023.e1437_pos (not_le.mp h1423).le h1406 hz1 h1433 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B023.e1438_pos (not_le.mp h1423).le h1406 (not_le.mp h1433).le h1432 hz
                            · -- right
                              by_cases h1434 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1441_pos (not_le.mp h1423).le h1406 (not_le.mp h1432).le h1434 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1442_pos (not_le.mp h1423).le h1406 (not_le.mp h1434).le h1431 hz
                          · -- right
                            by_cases h1435 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1436 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1453_pos (not_le.mp h1423).le h1406 (not_le.mp h1431).le h1436 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1454_pos (not_le.mp h1423).le h1406 (not_le.mp h1436).le h1435 hz
                            · -- right
                              by_cases h1437 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1457_pos (not_le.mp h1423).le h1406 (not_le.mp h1435).le h1437 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1458_pos (not_le.mp h1423).le h1406 (not_le.mp h1437).le hz2 hz
                    · -- right
                      by_cases h1438 : a ≤ ((347103/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1439 : a ≤ ((693357/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1440 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1441 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1442 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1459_pos (not_le.mp h1406).le h1439 hz1 h1442 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1460_pos (not_le.mp h1406).le h1439 (not_le.mp h1442).le h1441 hz
                            · -- right
                              by_cases h1443 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1463_pos (not_le.mp h1406).le h1439 (not_le.mp h1441).le h1443 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1464_pos (not_le.mp h1406).le h1439 (not_le.mp h1443).le h1440 hz
                          · -- right
                            by_cases h1444 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1445 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1475_pos (not_le.mp h1406).le h1439 (not_le.mp h1440).le h1445 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1476_pos (not_le.mp h1406).le h1439 (not_le.mp h1445).le h1444 hz
                            · -- right
                              by_cases h1446 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1479_pos (not_le.mp h1406).le h1439 (not_le.mp h1444).le h1446 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1480_pos (not_le.mp h1406).le h1439 (not_le.mp h1446).le hz2 hz
                        · -- right
                          by_cases h1447 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1448 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1449 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1461_pos (not_le.mp h1439).le h1438 hz1 h1449 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1462_pos (not_le.mp h1439).le h1438 (not_le.mp h1449).le h1448 hz
                            · -- right
                              by_cases h1450 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1465_pos (not_le.mp h1439).le h1438 (not_le.mp h1448).le h1450 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1466_pos (not_le.mp h1439).le h1438 (not_le.mp h1450).le h1447 hz
                          · -- right
                            by_cases h1451 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1452 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1477_pos (not_le.mp h1439).le h1438 (not_le.mp h1447).le h1452 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1478_pos (not_le.mp h1439).le h1438 (not_le.mp h1452).le h1451 hz
                            · -- right
                              by_cases h1453 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1481_pos (not_le.mp h1439).le h1438 (not_le.mp h1451).le h1453 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1482_pos (not_le.mp h1439).le h1438 (not_le.mp h1453).le hz2 hz
                      · -- right
                        by_cases h1454 : a ≤ ((139011/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1455 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1456 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1457 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1467_pos (not_le.mp h1438).le h1454 hz1 h1457 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1468_pos (not_le.mp h1438).le h1454 (not_le.mp h1457).le h1456 hz
                            · -- right
                              by_cases h1458 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1471_pos (not_le.mp h1438).le h1454 (not_le.mp h1456).le h1458 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1472_pos (not_le.mp h1438).le h1454 (not_le.mp h1458).le h1455 hz
                          · -- right
                            by_cases h1459 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1460 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1483_pos (not_le.mp h1438).le h1454 (not_le.mp h1455).le h1460 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1484_pos (not_le.mp h1438).le h1454 (not_le.mp h1460).le h1459 hz
                            · -- right
                              by_cases h1461 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1487_pos (not_le.mp h1438).le h1454 (not_le.mp h1459).le h1461 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1488_pos (not_le.mp h1438).le h1454 (not_le.mp h1461).le hz2 hz
                        · -- right
                          by_cases h1462 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1463 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1464 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1469_pos (not_le.mp h1454).le h1029 hz1 h1464 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1470_pos (not_le.mp h1454).le h1029 (not_le.mp h1464).le h1463 hz
                            · -- right
                              by_cases h1465 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1473_pos (not_le.mp h1454).le h1029 (not_le.mp h1463).le h1465 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1474_pos (not_le.mp h1454).le h1029 (not_le.mp h1465).le h1462 hz
                          · -- right
                            by_cases h1466 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1467 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1485_pos (not_le.mp h1454).le h1029 (not_le.mp h1462).le h1467 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1486_pos (not_le.mp h1454).le h1029 (not_le.mp h1467).le h1466 hz
                            · -- right
                              by_cases h1468 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1489_pos (not_le.mp h1454).le h1029 (not_le.mp h1466).le h1468 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1490_pos (not_le.mp h1454).le h1029 (not_le.mp h1468).le hz2 hz
              · -- right
                by_cases h1469 : a ≤ ((44343/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h1470 : a ≤ ((87837/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1471 : a ≤ ((6993/40960 : ℚ) : ℝ)
                    · -- left
                      by_cases h1472 : a ≤ ((348801/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1473 : a ≤ ((696753/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1474 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1475 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1476 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1491_pos (not_le.mp h1029).le h1473 hz1 h1476 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1492_pos (not_le.mp h1029).le h1473 (not_le.mp h1476).le h1475 hz
                            · -- right
                              by_cases h1477 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1495_pos (not_le.mp h1029).le h1473 (not_le.mp h1475).le h1477 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1496_pos (not_le.mp h1029).le h1473 (not_le.mp h1477).le h1474 hz
                          · -- right
                            by_cases h1478 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1479 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1507_pos (not_le.mp h1029).le h1473 (not_le.mp h1474).le h1479 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1508_pos (not_le.mp h1029).le h1473 (not_le.mp h1479).le h1478 hz
                            · -- right
                              by_cases h1480 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1511_pos (not_le.mp h1029).le h1473 (not_le.mp h1478).le h1480 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1512_pos (not_le.mp h1029).le h1473 (not_le.mp h1480).le hz2 hz
                        · -- right
                          by_cases h1481 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1482 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1483 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1493_pos (not_le.mp h1473).le h1472 hz1 h1483 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1494_pos (not_le.mp h1473).le h1472 (not_le.mp h1483).le h1482 hz
                            · -- right
                              by_cases h1484 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1497_pos (not_le.mp h1473).le h1472 (not_le.mp h1482).le h1484 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B024.e1498_pos (not_le.mp h1473).le h1472 (not_le.mp h1484).le h1481 hz
                          · -- right
                            by_cases h1485 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1486 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1509_pos (not_le.mp h1473).le h1472 (not_le.mp h1481).le h1486 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1510_pos (not_le.mp h1473).le h1472 (not_le.mp h1486).le h1485 hz
                            · -- right
                              by_cases h1487 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1513_pos (not_le.mp h1473).le h1472 (not_le.mp h1485).le h1487 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1514_pos (not_le.mp h1473).le h1472 (not_le.mp h1487).le hz2 hz
                      · -- right
                        by_cases h1488 : a ≤ ((698451/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1489 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1490 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1491 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B024.e1499_pos (not_le.mp h1472).le h1488 hz1 h1491 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1500_pos (not_le.mp h1472).le h1488 (not_le.mp h1491).le h1490 hz
                            · -- right
                              by_cases h1492 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1503_pos (not_le.mp h1472).le h1488 (not_le.mp h1490).le h1492 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1504_pos (not_le.mp h1472).le h1488 (not_le.mp h1492).le h1489 hz
                          · -- right
                            by_cases h1493 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1494 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1515_pos (not_le.mp h1472).le h1488 (not_le.mp h1489).le h1494 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1516_pos (not_le.mp h1472).le h1488 (not_le.mp h1494).le h1493 hz
                            · -- right
                              by_cases h1495 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1519_pos (not_le.mp h1472).le h1488 (not_le.mp h1493).le h1495 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1520_pos (not_le.mp h1472).le h1488 (not_le.mp h1495).le hz2 hz
                        · -- right
                          by_cases h1496 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1497 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1498 : z ≤ ((7993/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1501_pos (not_le.mp h1488).le h1471 hz1 h1498 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1502_pos (not_le.mp h1488).le h1471 (not_le.mp h1498).le h1497 hz
                            · -- right
                              by_cases h1499 : z ≤ ((1599/1600 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1505_pos (not_le.mp h1488).le h1471 (not_le.mp h1497).le h1499 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1506_pos (not_le.mp h1488).le h1471 (not_le.mp h1499).le h1496 hz
                          · -- right
                            by_cases h1500 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              by_cases h1501 : z ≤ ((7997/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1517_pos (not_le.mp h1488).le h1471 (not_le.mp h1496).le h1501 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1518_pos (not_le.mp h1488).le h1471 (not_le.mp h1501).le h1500 hz
                            · -- right
                              by_cases h1502 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1521_pos (not_le.mp h1488).le h1471 (not_le.mp h1500).le h1502 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1522_pos (not_le.mp h1488).le h1471 (not_le.mp h1502).le hz2 hz
                    · -- right
                      by_cases h1503 : a ≤ ((350499/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1504 : a ≤ ((700149/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1505 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1506 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e590_pos (not_le.mp h1471).le h1504 hz1 h1506 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B009.e592_pos (not_le.mp h1471).le h1504 (not_le.mp h1506).le h1505 hz
                          · -- right
                            by_cases h1507 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e598_pos (not_le.mp h1471).le h1504 (not_le.mp h1505).le h1507 hz
                            · -- right
                              by_cases h1508 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1523_pos (not_le.mp h1471).le h1504 (not_le.mp h1507).le h1508 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1524_pos (not_le.mp h1471).le h1504 (not_le.mp h1508).le hz2 hz
                        · -- right
                          by_cases h1509 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1510 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e591_pos (not_le.mp h1504).le h1503 hz1 h1510 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B009.e593_pos (not_le.mp h1504).le h1503 (not_le.mp h1510).le h1509 hz
                          · -- right
                            by_cases h1511 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e599_pos (not_le.mp h1504).le h1503 (not_le.mp h1509).le h1511 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e600_pos (not_le.mp h1504).le h1503 (not_le.mp h1511).le hz2 hz
                      · -- right
                        by_cases h1512 : a ≤ ((701847/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1513 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1514 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e594_pos (not_le.mp h1503).le h1512 hz1 h1514 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B009.e596_pos (not_le.mp h1503).le h1512 (not_le.mp h1514).le h1513 hz
                          · -- right
                            by_cases h1515 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e601_pos (not_le.mp h1503).le h1512 (not_le.mp h1513).le h1515 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e603_pos (not_le.mp h1503).le h1512 (not_le.mp h1515).le hz2 hz
                        · -- right
                          by_cases h1516 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1517 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B009.e595_pos (not_le.mp h1512).le h1470 hz1 h1517 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B009.e597_pos (not_le.mp h1512).le h1470 (not_le.mp h1517).le h1516 hz
                          · -- right
                            by_cases h1518 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e602_pos (not_le.mp h1512).le h1470 (not_le.mp h1516).le h1518 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e604_pos (not_le.mp h1512).le h1470 (not_le.mp h1518).le hz2 hz
                  · -- right
                    by_cases h1519 : a ≤ ((176523/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1520 : a ≤ ((352197/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1521 : a ≤ ((140709/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1522 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1523 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e605_pos (not_le.mp h1470).le h1521 hz1 h1523 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e607_pos (not_le.mp h1470).le h1521 (not_le.mp h1523).le h1522 hz
                          · -- right
                            by_cases h1524 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e613_pos (not_le.mp h1470).le h1521 (not_le.mp h1522).le h1524 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e615_pos (not_le.mp h1470).le h1521 (not_le.mp h1524).le hz2 hz
                        · -- right
                          by_cases h1525 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1526 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e606_pos (not_le.mp h1521).le h1520 hz1 h1526 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e608_pos (not_le.mp h1521).le h1520 (not_le.mp h1526).le h1525 hz
                          · -- right
                            by_cases h1527 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e614_pos (not_le.mp h1521).le h1520 (not_le.mp h1525).le h1527 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e616_pos (not_le.mp h1521).le h1520 (not_le.mp h1527).le hz2 hz
                      · -- right
                        by_cases h1528 : a ≤ ((705243/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1529 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1530 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e609_pos (not_le.mp h1520).le h1528 hz1 h1530 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e611_pos (not_le.mp h1520).le h1528 (not_le.mp h1530).le h1529 hz
                          · -- right
                            by_cases h1531 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e617_pos (not_le.mp h1520).le h1528 (not_le.mp h1529).le h1531 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e619_pos (not_le.mp h1520).le h1528 (not_le.mp h1531).le hz2 hz
                        · -- right
                          by_cases h1532 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1533 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e610_pos (not_le.mp h1528).le h1519 hz1 h1533 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e612_pos (not_le.mp h1528).le h1519 (not_le.mp h1533).le h1532 hz
                          · -- right
                            by_cases h1534 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e618_pos (not_le.mp h1528).le h1519 (not_le.mp h1532).le h1534 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e620_pos (not_le.mp h1528).le h1519 (not_le.mp h1534).le hz2 hz
                    · -- right
                      by_cases h1535 : a ≤ ((70779/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1536 : a ≤ ((706941/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1537 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1538 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e621_pos (not_le.mp h1519).le h1536 hz1 h1538 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e623_pos (not_le.mp h1519).le h1536 (not_le.mp h1538).le h1537 hz
                          · -- right
                            by_cases h1539 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e629_pos (not_le.mp h1519).le h1536 (not_le.mp h1537).le h1539 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e631_pos (not_le.mp h1519).le h1536 (not_le.mp h1539).le hz2 hz
                        · -- right
                          by_cases h1540 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1541 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e622_pos (not_le.mp h1536).le h1535 hz1 h1541 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e624_pos (not_le.mp h1536).le h1535 (not_le.mp h1541).le h1540 hz
                          · -- right
                            by_cases h1542 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e630_pos (not_le.mp h1536).le h1535 (not_le.mp h1540).le h1542 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e632_pos (not_le.mp h1536).le h1535 (not_le.mp h1542).le hz2 hz
                      · -- right
                        by_cases h1543 : a ≤ ((708639/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1544 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1545 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e625_pos (not_le.mp h1535).le h1543 hz1 h1545 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e627_pos (not_le.mp h1535).le h1543 (not_le.mp h1545).le h1544 hz
                          · -- right
                            by_cases h1546 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e633_pos (not_le.mp h1535).le h1543 (not_le.mp h1544).le h1546 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e635_pos (not_le.mp h1535).le h1543 (not_le.mp h1546).le hz2 hz
                        · -- right
                          by_cases h1547 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1548 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e626_pos (not_le.mp h1543).le h1469 hz1 h1548 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e628_pos (not_le.mp h1543).le h1469 (not_le.mp h1548).le h1547 hz
                          · -- right
                            by_cases h1549 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e634_pos (not_le.mp h1543).le h1469 (not_le.mp h1547).le h1549 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e636_pos (not_le.mp h1543).le h1469 (not_le.mp h1549).le hz2 hz
                · -- right
                  by_cases h1550 : a ≤ ((17907/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h1551 : a ≤ ((178221/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1552 : a ≤ ((355593/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1553 : a ≤ ((710337/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1554 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1555 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e637_pos (not_le.mp h1469).le h1553 hz1 h1555 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e639_pos (not_le.mp h1469).le h1553 (not_le.mp h1555).le h1554 hz
                          · -- right
                            by_cases h1556 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e645_pos (not_le.mp h1469).le h1553 (not_le.mp h1554).le h1556 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e647_pos (not_le.mp h1469).le h1553 (not_le.mp h1556).le hz2 hz
                        · -- right
                          by_cases h1557 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1558 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e638_pos (not_le.mp h1553).le h1552 hz1 h1558 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e640_pos (not_le.mp h1553).le h1552 (not_le.mp h1558).le h1557 hz
                          · -- right
                            by_cases h1559 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e646_pos (not_le.mp h1553).le h1552 (not_le.mp h1557).le h1559 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e648_pos (not_le.mp h1553).le h1552 (not_le.mp h1559).le hz2 hz
                      · -- right
                        by_cases h1560 : a ≤ ((142407/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1561 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1562 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e641_pos (not_le.mp h1552).le h1560 hz1 h1562 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e643_pos (not_le.mp h1552).le h1560 (not_le.mp h1562).le h1561 hz
                          · -- right
                            by_cases h1563 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e649_pos (not_le.mp h1552).le h1560 (not_le.mp h1561).le h1563 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e651_pos (not_le.mp h1552).le h1560 (not_le.mp h1563).le hz2 hz
                        · -- right
                          by_cases h1564 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1565 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e642_pos (not_le.mp h1560).le h1551 hz1 h1565 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e644_pos (not_le.mp h1560).le h1551 (not_le.mp h1565).le h1564 hz
                          · -- right
                            by_cases h1566 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e650_pos (not_le.mp h1560).le h1551 (not_le.mp h1564).le h1566 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e652_pos (not_le.mp h1560).le h1551 (not_le.mp h1566).le hz2 hz
                    · -- right
                      by_cases h1567 : a ≤ ((357291/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1568 : a ≤ ((713733/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1569 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1570 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e653_pos (not_le.mp h1551).le h1568 hz1 h1570 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e655_pos (not_le.mp h1551).le h1568 (not_le.mp h1570).le h1569 hz
                          · -- right
                            by_cases h1571 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e661_pos (not_le.mp h1551).le h1568 (not_le.mp h1569).le h1571 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e663_pos (not_le.mp h1551).le h1568 (not_le.mp h1571).le hz2 hz
                        · -- right
                          by_cases h1572 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1573 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e654_pos (not_le.mp h1568).le h1567 hz1 h1573 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e656_pos (not_le.mp h1568).le h1567 (not_le.mp h1573).le h1572 hz
                          · -- right
                            by_cases h1574 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e662_pos (not_le.mp h1568).le h1567 (not_le.mp h1572).le h1574 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e664_pos (not_le.mp h1568).le h1567 (not_le.mp h1574).le hz2 hz
                      · -- right
                        by_cases h1575 : a ≤ ((715431/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1576 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1577 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e657_pos (not_le.mp h1567).le h1575 hz1 h1577 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B010.e659_pos (not_le.mp h1567).le h1575 (not_le.mp h1577).le h1576 hz
                          · -- right
                            by_cases h1578 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e665_pos (not_le.mp h1567).le h1575 (not_le.mp h1576).le h1578 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e667_pos (not_le.mp h1567).le h1575 (not_le.mp h1578).le hz2 hz
                        · -- right
                          by_cases h1579 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1580 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B010.e658_pos (not_le.mp h1575).le h1550 hz1 h1580 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e660_pos (not_le.mp h1575).le h1550 (not_le.mp h1580).le h1579 hz
                          · -- right
                            by_cases h1581 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e666_pos (not_le.mp h1575).le h1550 (not_le.mp h1579).le h1581 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e668_pos (not_le.mp h1575).le h1550 (not_le.mp h1581).le hz2 hz
                  · -- right
                    by_cases h1582 : a ≤ ((179919/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1583 : a ≤ ((358989/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1584 : a ≤ ((717129/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1585 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1586 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e669_pos (not_le.mp h1550).le h1584 hz1 h1586 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e671_pos (not_le.mp h1550).le h1584 (not_le.mp h1586).le h1585 hz
                          · -- right
                            by_cases h1587 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e677_pos (not_le.mp h1550).le h1584 (not_le.mp h1585).le h1587 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e679_pos (not_le.mp h1550).le h1584 (not_le.mp h1587).le hz2 hz
                        · -- right
                          by_cases h1588 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1589 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e670_pos (not_le.mp h1584).le h1583 hz1 h1589 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e672_pos (not_le.mp h1584).le h1583 (not_le.mp h1589).le h1588 hz
                          · -- right
                            by_cases h1590 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e678_pos (not_le.mp h1584).le h1583 (not_le.mp h1588).le h1590 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e680_pos (not_le.mp h1584).le h1583 (not_le.mp h1590).le hz2 hz
                      · -- right
                        by_cases h1591 : a ≤ ((718827/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1592 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1593 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e673_pos (not_le.mp h1583).le h1591 hz1 h1593 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e675_pos (not_le.mp h1583).le h1591 (not_le.mp h1593).le h1592 hz
                          · -- right
                            by_cases h1594 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e681_pos (not_le.mp h1583).le h1591 (not_le.mp h1592).le h1594 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e683_pos (not_le.mp h1583).le h1591 (not_le.mp h1594).le hz2 hz
                        · -- right
                          by_cases h1595 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1596 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e674_pos (not_le.mp h1591).le h1582 hz1 h1596 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e676_pos (not_le.mp h1591).le h1582 (not_le.mp h1596).le h1595 hz
                          · -- right
                            by_cases h1597 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e682_pos (not_le.mp h1591).le h1582 (not_le.mp h1595).le h1597 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e684_pos (not_le.mp h1591).le h1582 (not_le.mp h1597).le hz2 hz
                    · -- right
                      by_cases h1598 : a ≤ ((360687/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1599 : a ≤ ((28821/163840 : ℚ) : ℝ)
                        · -- left
                          by_cases h1600 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1601 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e685_pos (not_le.mp h1582).le h1599 hz1 h1601 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e687_pos (not_le.mp h1582).le h1599 (not_le.mp h1601).le h1600 hz
                          · -- right
                            by_cases h1602 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e693_pos (not_le.mp h1582).le h1599 (not_le.mp h1600).le h1602 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e695_pos (not_le.mp h1582).le h1599 (not_le.mp h1602).le hz2 hz
                        · -- right
                          by_cases h1603 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1604 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e686_pos (not_le.mp h1599).le h1598 hz1 h1604 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e688_pos (not_le.mp h1599).le h1598 (not_le.mp h1604).le h1603 hz
                          · -- right
                            by_cases h1605 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e694_pos (not_le.mp h1599).le h1598 (not_le.mp h1603).le h1605 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e696_pos (not_le.mp h1599).le h1598 (not_le.mp h1605).le hz2 hz
                      · -- right
                        by_cases h1606 : a ≤ ((722223/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1607 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1608 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e689_pos (not_le.mp h1598).le h1606 hz1 h1608 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e691_pos (not_le.mp h1598).le h1606 (not_le.mp h1608).le h1607 hz
                          · -- right
                            by_cases h1609 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e697_pos (not_le.mp h1598).le h1606 (not_le.mp h1607).le h1609 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e699_pos (not_le.mp h1598).le h1606 (not_le.mp h1609).le hz2 hz
                        · -- right
                          by_cases h1610 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1611 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e690_pos (not_le.mp h1606).le h4 hz1 h1611 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e692_pos (not_le.mp h1606).le h4 (not_le.mp h1611).le h1610 hz
                          · -- right
                            by_cases h1612 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e698_pos (not_le.mp h1606).le h4 (not_le.mp h1610).le h1612 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e700_pos (not_le.mp h1606).le h4 (not_le.mp h1612).le hz2 hz
          · -- right
            by_cases h1613 : a ≤ ((12147/64000 : ℚ) : ℝ)
            · -- left
              by_cases h1614 : a ≤ ((4689/25600 : ℚ) : ℝ)
              · -- left
                by_cases h1615 : a ≤ ((46041/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h1616 : a ≤ ((91233/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1617 : a ≤ ((181617/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1618 : a ≤ ((72477/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1619 : a ≤ ((723921/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1620 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1621 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e701_pos (not_le.mp h4).le h1619 hz1 h1621 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e703_pos (not_le.mp h4).le h1619 (not_le.mp h1621).le h1620 hz
                          · -- right
                            by_cases h1622 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e709_pos (not_le.mp h4).le h1619 (not_le.mp h1620).le h1622 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e711_pos (not_le.mp h4).le h1619 (not_le.mp h1622).le hz2 hz
                        · -- right
                          by_cases h1623 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1624 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e702_pos (not_le.mp h1619).le h1618 hz1 h1624 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e704_pos (not_le.mp h1619).le h1618 (not_le.mp h1624).le h1623 hz
                          · -- right
                            by_cases h1625 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e710_pos (not_le.mp h1619).le h1618 (not_le.mp h1623).le h1625 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e712_pos (not_le.mp h1619).le h1618 (not_le.mp h1625).le hz2 hz
                      · -- right
                        by_cases h1626 : a ≤ ((725619/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1627 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1628 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e705_pos (not_le.mp h1618).le h1626 hz1 h1628 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e707_pos (not_le.mp h1618).le h1626 (not_le.mp h1628).le h1627 hz
                          · -- right
                            by_cases h1629 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e713_pos (not_le.mp h1618).le h1626 (not_le.mp h1627).le h1629 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e715_pos (not_le.mp h1618).le h1626 (not_le.mp h1629).le hz2 hz
                        · -- right
                          by_cases h1630 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1631 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e706_pos (not_le.mp h1626).le h1617 hz1 h1631 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e708_pos (not_le.mp h1626).le h1617 (not_le.mp h1631).le h1630 hz
                          · -- right
                            by_cases h1632 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e714_pos (not_le.mp h1626).le h1617 (not_le.mp h1630).le h1632 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e716_pos (not_le.mp h1626).le h1617 (not_le.mp h1632).le hz2 hz
                    · -- right
                      by_cases h1633 : a ≤ ((364083/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1634 : a ≤ ((727317/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1635 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1636 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e717_pos (not_le.mp h1617).le h1634 hz1 h1636 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B011.e719_pos (not_le.mp h1617).le h1634 (not_le.mp h1636).le h1635 hz
                          · -- right
                            by_cases h1637 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e725_pos (not_le.mp h1617).le h1634 (not_le.mp h1635).le h1637 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e727_pos (not_le.mp h1617).le h1634 (not_le.mp h1637).le hz2 hz
                        · -- right
                          by_cases h1638 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1639 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B011.e718_pos (not_le.mp h1634).le h1633 hz1 h1639 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e720_pos (not_le.mp h1634).le h1633 (not_le.mp h1639).le h1638 hz
                          · -- right
                            by_cases h1640 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e726_pos (not_le.mp h1634).le h1633 (not_le.mp h1638).le h1640 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e728_pos (not_le.mp h1634).le h1633 (not_le.mp h1640).le hz2 hz
                      · -- right
                        by_cases h1641 : a ≤ ((145803/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1642 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1643 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e721_pos (not_le.mp h1633).le h1641 hz1 h1643 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e723_pos (not_le.mp h1633).le h1641 (not_le.mp h1643).le h1642 hz
                          · -- right
                            by_cases h1644 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e729_pos (not_le.mp h1633).le h1641 (not_le.mp h1642).le h1644 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e731_pos (not_le.mp h1633).le h1641 (not_le.mp h1644).le hz2 hz
                        · -- right
                          by_cases h1645 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1646 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e722_pos (not_le.mp h1641).le h1616 hz1 h1646 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e724_pos (not_le.mp h1641).le h1616 (not_le.mp h1646).le h1645 hz
                          · -- right
                            by_cases h1647 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e730_pos (not_le.mp h1641).le h1616 (not_le.mp h1645).le h1647 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e732_pos (not_le.mp h1641).le h1616 (not_le.mp h1647).le hz2 hz
                  · -- right
                    by_cases h1648 : a ≤ ((36663/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1649 : a ≤ ((365781/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1650 : a ≤ ((730713/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1651 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1652 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e733_pos (not_le.mp h1616).le h1650 hz1 h1652 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e735_pos (not_le.mp h1616).le h1650 (not_le.mp h1652).le h1651 hz
                          · -- right
                            by_cases h1653 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e741_pos (not_le.mp h1616).le h1650 (not_le.mp h1651).le h1653 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e743_pos (not_le.mp h1616).le h1650 (not_le.mp h1653).le hz2 hz
                        · -- right
                          by_cases h1654 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1655 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e734_pos (not_le.mp h1650).le h1649 hz1 h1655 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e736_pos (not_le.mp h1650).le h1649 (not_le.mp h1655).le h1654 hz
                          · -- right
                            by_cases h1656 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e742_pos (not_le.mp h1650).le h1649 (not_le.mp h1654).le h1656 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e744_pos (not_le.mp h1650).le h1649 (not_le.mp h1656).le hz2 hz
                      · -- right
                        by_cases h1657 : a ≤ ((732411/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1658 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1659 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e737_pos (not_le.mp h1649).le h1657 hz1 h1659 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e739_pos (not_le.mp h1649).le h1657 (not_le.mp h1659).le h1658 hz
                          · -- right
                            by_cases h1660 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e745_pos (not_le.mp h1649).le h1657 (not_le.mp h1658).le h1660 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e747_pos (not_le.mp h1649).le h1657 (not_le.mp h1660).le hz2 hz
                        · -- right
                          by_cases h1661 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1662 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e738_pos (not_le.mp h1657).le h1648 hz1 h1662 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e740_pos (not_le.mp h1657).le h1648 (not_le.mp h1662).le h1661 hz
                          · -- right
                            by_cases h1663 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e746_pos (not_le.mp h1657).le h1648 (not_le.mp h1661).le h1663 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e748_pos (not_le.mp h1657).le h1648 (not_le.mp h1663).le hz2 hz
                    · -- right
                      by_cases h1664 : a ≤ ((367479/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1665 : a ≤ ((734109/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1666 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1667 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e749_pos (not_le.mp h1648).le h1665 hz1 h1667 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e751_pos (not_le.mp h1648).le h1665 (not_le.mp h1667).le h1666 hz
                          · -- right
                            by_cases h1668 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e757_pos (not_le.mp h1648).le h1665 (not_le.mp h1666).le h1668 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e759_pos (not_le.mp h1648).le h1665 (not_le.mp h1668).le hz2 hz
                        · -- right
                          by_cases h1669 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1670 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e750_pos (not_le.mp h1665).le h1664 hz1 h1670 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e752_pos (not_le.mp h1665).le h1664 (not_le.mp h1670).le h1669 hz
                          · -- right
                            by_cases h1671 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e758_pos (not_le.mp h1665).le h1664 (not_le.mp h1669).le h1671 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e760_pos (not_le.mp h1665).le h1664 (not_le.mp h1671).le hz2 hz
                      · -- right
                        by_cases h1672 : a ≤ ((735807/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1673 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1674 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e753_pos (not_le.mp h1664).le h1672 hz1 h1674 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e755_pos (not_le.mp h1664).le h1672 (not_le.mp h1674).le h1673 hz
                          · -- right
                            by_cases h1675 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e761_pos (not_le.mp h1664).le h1672 (not_le.mp h1673).le h1675 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e763_pos (not_le.mp h1664).le h1672 (not_le.mp h1675).le hz2 hz
                        · -- right
                          by_cases h1676 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1677 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e754_pos (not_le.mp h1672).le h1615 hz1 h1677 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e756_pos (not_le.mp h1672).le h1615 (not_le.mp h1677).le h1676 hz
                          · -- right
                            by_cases h1678 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e762_pos (not_le.mp h1672).le h1615 (not_le.mp h1676).le h1678 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e764_pos (not_le.mp h1672).le h1615 (not_le.mp h1678).le hz2 hz
                · -- right
                  by_cases h1679 : a ≤ ((92931/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1680 : a ≤ ((185013/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1681 : a ≤ ((369177/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1682 : a ≤ ((147501/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1683 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1684 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e765_pos (not_le.mp h1615).le h1682 hz1 h1684 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e767_pos (not_le.mp h1615).le h1682 (not_le.mp h1684).le h1683 hz
                          · -- right
                            by_cases h1685 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e773_pos (not_le.mp h1615).le h1682 (not_le.mp h1683).le h1685 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e775_pos (not_le.mp h1615).le h1682 (not_le.mp h1685).le hz2 hz
                        · -- right
                          by_cases h1686 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1687 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e766_pos (not_le.mp h1682).le h1681 hz1 h1687 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e768_pos (not_le.mp h1682).le h1681 (not_le.mp h1687).le h1686 hz
                          · -- right
                            by_cases h1688 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e774_pos (not_le.mp h1682).le h1681 (not_le.mp h1686).le h1688 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e776_pos (not_le.mp h1682).le h1681 (not_le.mp h1688).le hz2 hz
                      · -- right
                        by_cases h1689 : a ≤ ((739203/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1690 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1691 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e769_pos (not_le.mp h1681).le h1689 hz1 h1691 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e771_pos (not_le.mp h1681).le h1689 (not_le.mp h1691).le h1690 hz
                          · -- right
                            by_cases h1692 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e777_pos (not_le.mp h1681).le h1689 (not_le.mp h1690).le h1692 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e779_pos (not_le.mp h1681).le h1689 (not_le.mp h1692).le hz2 hz
                        · -- right
                          by_cases h1693 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1694 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e770_pos (not_le.mp h1689).le h1680 hz1 h1694 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B012.e772_pos (not_le.mp h1689).le h1680 (not_le.mp h1694).le h1693 hz
                          · -- right
                            by_cases h1695 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B012.e778_pos (not_le.mp h1689).le h1680 (not_le.mp h1693).le h1695 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e780_pos (not_le.mp h1689).le h1680 (not_le.mp h1695).le hz2 hz
                    · -- right
                      by_cases h1696 : a ≤ ((2967/16384 : ℚ) : ℝ)
                      · -- left
                        by_cases h1697 : a ≤ ((740901/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1698 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1699 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e781_pos (not_le.mp h1680).le h1697 hz1 h1699 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e783_pos (not_le.mp h1680).le h1697 (not_le.mp h1699).le h1698 hz
                          · -- right
                            by_cases h1700 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e789_pos (not_le.mp h1680).le h1697 (not_le.mp h1698).le h1700 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e791_pos (not_le.mp h1680).le h1697 (not_le.mp h1700).le hz2 hz
                        · -- right
                          by_cases h1701 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1702 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e782_pos (not_le.mp h1697).le h1696 hz1 h1702 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e784_pos (not_le.mp h1697).le h1696 (not_le.mp h1702).le h1701 hz
                          · -- right
                            by_cases h1703 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e790_pos (not_le.mp h1697).le h1696 (not_le.mp h1701).le h1703 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e792_pos (not_le.mp h1697).le h1696 (not_le.mp h1703).le hz2 hz
                      · -- right
                        by_cases h1704 : a ≤ ((742599/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1705 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1706 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e785_pos (not_le.mp h1696).le h1704 hz1 h1706 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e787_pos (not_le.mp h1696).le h1704 (not_le.mp h1706).le h1705 hz
                          · -- right
                            by_cases h1707 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e793_pos (not_le.mp h1696).le h1704 (not_le.mp h1705).le h1707 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e795_pos (not_le.mp h1696).le h1704 (not_le.mp h1707).le hz2 hz
                        · -- right
                          by_cases h1708 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1709 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e786_pos (not_le.mp h1704).le h1679 hz1 h1709 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e788_pos (not_le.mp h1704).le h1679 (not_le.mp h1709).le h1708 hz
                          · -- right
                            by_cases h1710 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e794_pos (not_le.mp h1704).le h1679 (not_le.mp h1708).le h1710 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e796_pos (not_le.mp h1704).le h1679 (not_le.mp h1710).le hz2 hz
                  · -- right
                    by_cases h1711 : a ≤ ((186711/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1712 : a ≤ ((372573/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1713 : a ≤ ((744297/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1714 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1715 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e797_pos (not_le.mp h1679).le h1713 hz1 h1715 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e799_pos (not_le.mp h1679).le h1713 (not_le.mp h1715).le h1714 hz
                          · -- right
                            by_cases h1716 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e805_pos (not_le.mp h1679).le h1713 (not_le.mp h1714).le h1716 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e807_pos (not_le.mp h1679).le h1713 (not_le.mp h1716).le hz2 hz
                        · -- right
                          by_cases h1717 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1718 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e798_pos (not_le.mp h1713).le h1712 hz1 h1718 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e800_pos (not_le.mp h1713).le h1712 (not_le.mp h1718).le h1717 hz
                          · -- right
                            by_cases h1719 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e806_pos (not_le.mp h1713).le h1712 (not_le.mp h1717).le h1719 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e808_pos (not_le.mp h1713).le h1712 (not_le.mp h1719).le hz2 hz
                      · -- right
                        by_cases h1720 : a ≤ ((149199/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1721 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1722 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e801_pos (not_le.mp h1712).le h1720 hz1 h1722 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e803_pos (not_le.mp h1712).le h1720 (not_le.mp h1722).le h1721 hz
                          · -- right
                            by_cases h1723 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e809_pos (not_le.mp h1712).le h1720 (not_le.mp h1721).le h1723 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e811_pos (not_le.mp h1712).le h1720 (not_le.mp h1723).le hz2 hz
                        · -- right
                          by_cases h1724 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1725 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e802_pos (not_le.mp h1720).le h1711 hz1 h1725 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e804_pos (not_le.mp h1720).le h1711 (not_le.mp h1725).le h1724 hz
                          · -- right
                            by_cases h1726 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e810_pos (not_le.mp h1720).le h1711 (not_le.mp h1724).le h1726 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e812_pos (not_le.mp h1720).le h1711 (not_le.mp h1726).le hz2 hz
                    · -- right
                      by_cases h1727 : a ≤ ((374271/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1728 : a ≤ ((747693/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1729 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1730 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e813_pos (not_le.mp h1711).le h1728 hz1 h1730 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e815_pos (not_le.mp h1711).le h1728 (not_le.mp h1730).le h1729 hz
                          · -- right
                            by_cases h1731 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e821_pos (not_le.mp h1711).le h1728 (not_le.mp h1729).le h1731 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e823_pos (not_le.mp h1711).le h1728 (not_le.mp h1731).le hz2 hz
                        · -- right
                          by_cases h1732 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1733 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e814_pos (not_le.mp h1728).le h1727 hz1 h1733 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e816_pos (not_le.mp h1728).le h1727 (not_le.mp h1733).le h1732 hz
                          · -- right
                            by_cases h1734 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e822_pos (not_le.mp h1728).le h1727 (not_le.mp h1732).le h1734 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e824_pos (not_le.mp h1728).le h1727 (not_le.mp h1734).le hz2 hz
                      · -- right
                        by_cases h1735 : a ≤ ((749391/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1736 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1737 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e817_pos (not_le.mp h1727).le h1735 hz1 h1737 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e819_pos (not_le.mp h1727).le h1735 (not_le.mp h1737).le h1736 hz
                          · -- right
                            by_cases h1738 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e825_pos (not_le.mp h1727).le h1735 (not_le.mp h1736).le h1738 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e827_pos (not_le.mp h1727).le h1735 (not_le.mp h1738).le hz2 hz
                        · -- right
                          by_cases h1739 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1740 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e818_pos (not_le.mp h1735).le h1614 hz1 h1740 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e820_pos (not_le.mp h1735).le h1614 (not_le.mp h1740).le h1739 hz
                          · -- right
                            by_cases h1741 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e826_pos (not_le.mp h1735).le h1614 (not_le.mp h1739).le h1741 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e828_pos (not_le.mp h1735).le h1614 (not_le.mp h1741).le hz2 hz
              · -- right
                by_cases h1742 : a ≤ ((47739/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h1743 : a ≤ ((94629/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1744 : a ≤ ((188409/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1745 : a ≤ ((375969/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1746 : a ≤ ((751089/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1747 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1748 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e829_pos (not_le.mp h1614).le h1746 hz1 h1748 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e831_pos (not_le.mp h1614).le h1746 (not_le.mp h1748).le h1747 hz
                          · -- right
                            by_cases h1749 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e837_pos (not_le.mp h1614).le h1746 (not_le.mp h1747).le h1749 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e839_pos (not_le.mp h1614).le h1746 (not_le.mp h1749).le hz2 hz
                        · -- right
                          by_cases h1750 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1751 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e830_pos (not_le.mp h1746).le h1745 hz1 h1751 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e832_pos (not_le.mp h1746).le h1745 (not_le.mp h1751).le h1750 hz
                          · -- right
                            by_cases h1752 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e838_pos (not_le.mp h1746).le h1745 (not_le.mp h1750).le h1752 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e840_pos (not_le.mp h1746).le h1745 (not_le.mp h1752).le hz2 hz
                      · -- right
                        by_cases h1753 : a ≤ ((752787/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1754 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1755 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e833_pos (not_le.mp h1745).le h1753 hz1 h1755 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e835_pos (not_le.mp h1745).le h1753 (not_le.mp h1755).le h1754 hz
                          · -- right
                            by_cases h1756 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e841_pos (not_le.mp h1745).le h1753 (not_le.mp h1754).le h1756 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e843_pos (not_le.mp h1745).le h1753 (not_le.mp h1756).le hz2 hz
                        · -- right
                          by_cases h1757 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1758 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B013.e834_pos (not_le.mp h1753).le h1744 hz1 h1758 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B013.e836_pos (not_le.mp h1753).le h1744 (not_le.mp h1758).le h1757 hz
                          · -- right
                            by_cases h1759 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e842_pos (not_le.mp h1753).le h1744 (not_le.mp h1757).le h1759 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e844_pos (not_le.mp h1753).le h1744 (not_le.mp h1759).le hz2 hz
                    · -- right
                      by_cases h1760 : a ≤ ((377667/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1761 : a ≤ ((150897/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1762 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1763 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e845_pos (not_le.mp h1744).le h1761 hz1 h1763 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e847_pos (not_le.mp h1744).le h1761 (not_le.mp h1763).le h1762 hz
                          · -- right
                            by_cases h1764 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e853_pos (not_le.mp h1744).le h1761 (not_le.mp h1762).le h1764 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e855_pos (not_le.mp h1744).le h1761 (not_le.mp h1764).le hz2 hz
                        · -- right
                          by_cases h1765 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1766 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e846_pos (not_le.mp h1761).le h1760 hz1 h1766 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e848_pos (not_le.mp h1761).le h1760 (not_le.mp h1766).le h1765 hz
                          · -- right
                            by_cases h1767 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e854_pos (not_le.mp h1761).le h1760 (not_le.mp h1765).le h1767 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e856_pos (not_le.mp h1761).le h1760 (not_le.mp h1767).le hz2 hz
                      · -- right
                        by_cases h1768 : a ≤ ((756183/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1769 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1770 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e849_pos (not_le.mp h1760).le h1768 hz1 h1770 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e851_pos (not_le.mp h1760).le h1768 (not_le.mp h1770).le h1769 hz
                          · -- right
                            by_cases h1771 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e857_pos (not_le.mp h1760).le h1768 (not_le.mp h1769).le h1771 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e859_pos (not_le.mp h1760).le h1768 (not_le.mp h1771).le hz2 hz
                        · -- right
                          by_cases h1772 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1773 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e850_pos (not_le.mp h1768).le h1743 hz1 h1773 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e852_pos (not_le.mp h1768).le h1743 (not_le.mp h1773).le h1772 hz
                          · -- right
                            by_cases h1774 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e858_pos (not_le.mp h1768).le h1743 (not_le.mp h1772).le h1774 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e860_pos (not_le.mp h1768).le h1743 (not_le.mp h1774).le hz2 hz
                  · -- right
                    by_cases h1775 : a ≤ ((190107/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1776 : a ≤ ((75873/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1777 : a ≤ ((757881/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1778 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1779 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e861_pos (not_le.mp h1743).le h1777 hz1 h1779 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e863_pos (not_le.mp h1743).le h1777 (not_le.mp h1779).le h1778 hz
                          · -- right
                            by_cases h1780 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e869_pos (not_le.mp h1743).le h1777 (not_le.mp h1778).le h1780 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e871_pos (not_le.mp h1743).le h1777 (not_le.mp h1780).le hz2 hz
                        · -- right
                          by_cases h1781 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1782 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e862_pos (not_le.mp h1777).le h1776 hz1 h1782 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e864_pos (not_le.mp h1777).le h1776 (not_le.mp h1782).le h1781 hz
                          · -- right
                            by_cases h1783 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e870_pos (not_le.mp h1777).le h1776 (not_le.mp h1781).le h1783 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e872_pos (not_le.mp h1777).le h1776 (not_le.mp h1783).le hz2 hz
                      · -- right
                        by_cases h1784 : a ≤ ((759579/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1785 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1786 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e865_pos (not_le.mp h1776).le h1784 hz1 h1786 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e867_pos (not_le.mp h1776).le h1784 (not_le.mp h1786).le h1785 hz
                          · -- right
                            by_cases h1787 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e873_pos (not_le.mp h1776).le h1784 (not_le.mp h1785).le h1787 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e875_pos (not_le.mp h1776).le h1784 (not_le.mp h1787).le hz2 hz
                        · -- right
                          by_cases h1788 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1789 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e866_pos (not_le.mp h1784).le h1775 hz1 h1789 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e868_pos (not_le.mp h1784).le h1775 (not_le.mp h1789).le h1788 hz
                          · -- right
                            by_cases h1790 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e874_pos (not_le.mp h1784).le h1775 (not_le.mp h1788).le h1790 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e876_pos (not_le.mp h1784).le h1775 (not_le.mp h1790).le hz2 hz
                    · -- right
                      by_cases h1791 : a ≤ ((381063/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1792 : a ≤ ((761277/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1793 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1794 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e877_pos (not_le.mp h1775).le h1792 hz1 h1794 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e879_pos (not_le.mp h1775).le h1792 (not_le.mp h1794).le h1793 hz
                          · -- right
                            by_cases h1795 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e885_pos (not_le.mp h1775).le h1792 (not_le.mp h1793).le h1795 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e887_pos (not_le.mp h1775).le h1792 (not_le.mp h1795).le hz2 hz
                        · -- right
                          by_cases h1796 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1797 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e878_pos (not_le.mp h1792).le h1791 hz1 h1797 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e880_pos (not_le.mp h1792).le h1791 (not_le.mp h1797).le h1796 hz
                          · -- right
                            by_cases h1798 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e886_pos (not_le.mp h1792).le h1791 (not_le.mp h1796).le h1798 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e888_pos (not_le.mp h1792).le h1791 (not_le.mp h1798).le hz2 hz
                      · -- right
                        by_cases h1799 : a ≤ ((30519/163840 : ℚ) : ℝ)
                        · -- left
                          by_cases h1800 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1801 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e881_pos (not_le.mp h1791).le h1799 hz1 h1801 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e883_pos (not_le.mp h1791).le h1799 (not_le.mp h1801).le h1800 hz
                          · -- right
                            by_cases h1802 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e889_pos (not_le.mp h1791).le h1799 (not_le.mp h1800).le h1802 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e891_pos (not_le.mp h1791).le h1799 (not_le.mp h1802).le hz2 hz
                        · -- right
                          by_cases h1803 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1804 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e882_pos (not_le.mp h1799).le h1742 hz1 h1804 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e884_pos (not_le.mp h1799).le h1742 (not_le.mp h1804).le h1803 hz
                          · -- right
                            by_cases h1805 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e890_pos (not_le.mp h1799).le h1742 (not_le.mp h1803).le h1805 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e892_pos (not_le.mp h1799).le h1742 (not_le.mp h1805).le hz2 hz
                · -- right
                  by_cases h1806 : a ≤ ((96327/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1807 : a ≤ ((38361/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1808 : a ≤ ((382761/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1809 : a ≤ ((764673/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1810 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1811 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e893_pos (not_le.mp h1742).le h1809 hz1 h1811 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e895_pos (not_le.mp h1742).le h1809 (not_le.mp h1811).le h1810 hz
                          · -- right
                            by_cases h1812 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e901_pos (not_le.mp h1742).le h1809 (not_le.mp h1810).le h1812 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e903_pos (not_le.mp h1742).le h1809 (not_le.mp h1812).le hz2 hz
                        · -- right
                          by_cases h1813 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1814 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e894_pos (not_le.mp h1809).le h1808 hz1 h1814 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e896_pos (not_le.mp h1809).le h1808 (not_le.mp h1814).le h1813 hz
                          · -- right
                            by_cases h1815 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e902_pos (not_le.mp h1809).le h1808 (not_le.mp h1813).le h1815 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e904_pos (not_le.mp h1809).le h1808 (not_le.mp h1815).le hz2 hz
                      · -- right
                        by_cases h1816 : a ≤ ((766371/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1817 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1818 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e897_pos (not_le.mp h1808).le h1816 hz1 h1818 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B014.e899_pos (not_le.mp h1808).le h1816 (not_le.mp h1818).le h1817 hz
                          · -- right
                            by_cases h1819 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e905_pos (not_le.mp h1808).le h1816 (not_le.mp h1817).le h1819 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e907_pos (not_le.mp h1808).le h1816 (not_le.mp h1819).le hz2 hz
                        · -- right
                          by_cases h1820 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1821 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B014.e898_pos (not_le.mp h1816).le h1807 hz1 h1821 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e900_pos (not_le.mp h1816).le h1807 (not_le.mp h1821).le h1820 hz
                          · -- right
                            by_cases h1822 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e906_pos (not_le.mp h1816).le h1807 (not_le.mp h1820).le h1822 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e908_pos (not_le.mp h1816).le h1807 (not_le.mp h1822).le hz2 hz
                    · -- right
                      by_cases h1823 : a ≤ ((384459/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1824 : a ≤ ((768069/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1825 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1826 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e909_pos (not_le.mp h1807).le h1824 hz1 h1826 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e911_pos (not_le.mp h1807).le h1824 (not_le.mp h1826).le h1825 hz
                          · -- right
                            by_cases h1827 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e917_pos (not_le.mp h1807).le h1824 (not_le.mp h1825).le h1827 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e919_pos (not_le.mp h1807).le h1824 (not_le.mp h1827).le hz2 hz
                        · -- right
                          by_cases h1828 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1829 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e910_pos (not_le.mp h1824).le h1823 hz1 h1829 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e912_pos (not_le.mp h1824).le h1823 (not_le.mp h1829).le h1828 hz
                          · -- right
                            by_cases h1830 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e918_pos (not_le.mp h1824).le h1823 (not_le.mp h1828).le h1830 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e920_pos (not_le.mp h1824).le h1823 (not_le.mp h1830).le hz2 hz
                      · -- right
                        by_cases h1831 : a ≤ ((769767/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1832 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1833 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e913_pos (not_le.mp h1823).le h1831 hz1 h1833 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e915_pos (not_le.mp h1823).le h1831 (not_le.mp h1833).le h1832 hz
                          · -- right
                            by_cases h1834 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e921_pos (not_le.mp h1823).le h1831 (not_le.mp h1832).le h1834 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e923_pos (not_le.mp h1823).le h1831 (not_le.mp h1834).le hz2 hz
                        · -- right
                          by_cases h1835 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1836 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e914_pos (not_le.mp h1831).le h1806 hz1 h1836 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e916_pos (not_le.mp h1831).le h1806 (not_le.mp h1836).le h1835 hz
                          · -- right
                            by_cases h1837 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e922_pos (not_le.mp h1831).le h1806 (not_le.mp h1835).le h1837 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e924_pos (not_le.mp h1831).le h1806 (not_le.mp h1837).le hz2 hz
                  · -- right
                    by_cases h1838 : a ≤ ((193503/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1839 : a ≤ ((386157/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1840 : a ≤ ((154293/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1841 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1842 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e925_pos (not_le.mp h1806).le h1840 hz1 h1842 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e927_pos (not_le.mp h1806).le h1840 (not_le.mp h1842).le h1841 hz
                          · -- right
                            by_cases h1843 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e933_pos (not_le.mp h1806).le h1840 (not_le.mp h1841).le h1843 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e935_pos (not_le.mp h1806).le h1840 (not_le.mp h1843).le hz2 hz
                        · -- right
                          by_cases h1844 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1845 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e926_pos (not_le.mp h1840).le h1839 hz1 h1845 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e928_pos (not_le.mp h1840).le h1839 (not_le.mp h1845).le h1844 hz
                          · -- right
                            by_cases h1846 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e934_pos (not_le.mp h1840).le h1839 (not_le.mp h1844).le h1846 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e936_pos (not_le.mp h1840).le h1839 (not_le.mp h1846).le hz2 hz
                      · -- right
                        by_cases h1847 : a ≤ ((773163/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1848 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1849 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e929_pos (not_le.mp h1839).le h1847 hz1 h1849 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e931_pos (not_le.mp h1839).le h1847 (not_le.mp h1849).le h1848 hz
                          · -- right
                            by_cases h1850 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e937_pos (not_le.mp h1839).le h1847 (not_le.mp h1848).le h1850 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e939_pos (not_le.mp h1839).le h1847 (not_le.mp h1850).le hz2 hz
                        · -- right
                          by_cases h1851 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1852 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e930_pos (not_le.mp h1847).le h1838 hz1 h1852 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e932_pos (not_le.mp h1847).le h1838 (not_le.mp h1852).le h1851 hz
                          · -- right
                            by_cases h1853 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e938_pos (not_le.mp h1847).le h1838 (not_le.mp h1851).le h1853 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e940_pos (not_le.mp h1847).le h1838 (not_le.mp h1853).le hz2 hz
                    · -- right
                      by_cases h1854 : a ≤ ((77571/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1855 : a ≤ ((774861/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1856 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1857 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e941_pos (not_le.mp h1838).le h1855 hz1 h1857 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e943_pos (not_le.mp h1838).le h1855 (not_le.mp h1857).le h1856 hz
                          · -- right
                            by_cases h1858 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e949_pos (not_le.mp h1838).le h1855 (not_le.mp h1856).le h1858 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e951_pos (not_le.mp h1838).le h1855 (not_le.mp h1858).le hz2 hz
                        · -- right
                          by_cases h1859 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1860 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e942_pos (not_le.mp h1855).le h1854 hz1 h1860 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e944_pos (not_le.mp h1855).le h1854 (not_le.mp h1860).le h1859 hz
                          · -- right
                            by_cases h1861 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e950_pos (not_le.mp h1855).le h1854 (not_le.mp h1859).le h1861 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e952_pos (not_le.mp h1855).le h1854 (not_le.mp h1861).le hz2 hz
                      · -- right
                        by_cases h1862 : a ≤ ((776559/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1863 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1864 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e945_pos (not_le.mp h1854).le h1862 hz1 h1864 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e947_pos (not_le.mp h1854).le h1862 (not_le.mp h1864).le h1863 hz
                          · -- right
                            by_cases h1865 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e953_pos (not_le.mp h1854).le h1862 (not_le.mp h1863).le h1865 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e955_pos (not_le.mp h1854).le h1862 (not_le.mp h1865).le hz2 hz
                        · -- right
                          by_cases h1866 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1867 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e946_pos (not_le.mp h1862).le h1613 hz1 h1867 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e948_pos (not_le.mp h1862).le h1613 (not_le.mp h1867).le h1866 hz
                          · -- right
                            by_cases h1868 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e954_pos (not_le.mp h1862).le h1613 (not_le.mp h1866).le h1868 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e956_pos (not_le.mp h1862).le h1613 (not_le.mp h1868).le hz2 hz
            · -- right
              by_cases h1869 : a ≤ ((25143/128000 : ℚ) : ℝ)
              · -- left
                by_cases h1870 : a ≤ ((49437/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h1871 : a ≤ ((3921/20480 : ℚ) : ℝ)
                  · -- left
                    by_cases h1872 : a ≤ ((195201/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1873 : a ≤ ((389553/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1874 : a ≤ ((778257/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1875 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1876 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e957_pos (not_le.mp h1613).le h1874 hz1 h1876 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B015.e959_pos (not_le.mp h1613).le h1874 (not_le.mp h1876).le h1875 hz
                          · -- right
                            by_cases h1877 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e965_pos (not_le.mp h1613).le h1874 (not_le.mp h1875).le h1877 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e967_pos (not_le.mp h1613).le h1874 (not_le.mp h1877).le hz2 hz
                        · -- right
                          by_cases h1878 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1879 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B015.e958_pos (not_le.mp h1874).le h1873 hz1 h1879 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e960_pos (not_le.mp h1874).le h1873 (not_le.mp h1879).le h1878 hz
                          · -- right
                            by_cases h1880 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e966_pos (not_le.mp h1874).le h1873 (not_le.mp h1878).le h1880 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e968_pos (not_le.mp h1874).le h1873 (not_le.mp h1880).le hz2 hz
                      · -- right
                        by_cases h1881 : a ≤ ((155991/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1882 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1883 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e961_pos (not_le.mp h1873).le h1881 hz1 h1883 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e963_pos (not_le.mp h1873).le h1881 (not_le.mp h1883).le h1882 hz
                          · -- right
                            by_cases h1884 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e969_pos (not_le.mp h1873).le h1881 (not_le.mp h1882).le h1884 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e971_pos (not_le.mp h1873).le h1881 (not_le.mp h1884).le hz2 hz
                        · -- right
                          by_cases h1885 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1886 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e962_pos (not_le.mp h1881).le h1872 hz1 h1886 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e964_pos (not_le.mp h1881).le h1872 (not_le.mp h1886).le h1885 hz
                          · -- right
                            by_cases h1887 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e970_pos (not_le.mp h1881).le h1872 (not_le.mp h1885).le h1887 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e972_pos (not_le.mp h1881).le h1872 (not_le.mp h1887).le hz2 hz
                    · -- right
                      by_cases h1888 : a ≤ ((391251/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1889 : a ≤ ((781653/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1890 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1891 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e973_pos (not_le.mp h1872).le h1889 hz1 h1891 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e975_pos (not_le.mp h1872).le h1889 (not_le.mp h1891).le h1890 hz
                          · -- right
                            by_cases h1892 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e981_pos (not_le.mp h1872).le h1889 (not_le.mp h1890).le h1892 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e983_pos (not_le.mp h1872).le h1889 (not_le.mp h1892).le hz2 hz
                        · -- right
                          by_cases h1893 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1894 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e974_pos (not_le.mp h1889).le h1888 hz1 h1894 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e976_pos (not_le.mp h1889).le h1888 (not_le.mp h1894).le h1893 hz
                          · -- right
                            by_cases h1895 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e982_pos (not_le.mp h1889).le h1888 (not_le.mp h1893).le h1895 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e984_pos (not_le.mp h1889).le h1888 (not_le.mp h1895).le hz2 hz
                      · -- right
                        by_cases h1896 : a ≤ ((783351/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1897 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1898 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e977_pos (not_le.mp h1888).le h1896 hz1 h1898 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e979_pos (not_le.mp h1888).le h1896 (not_le.mp h1898).le h1897 hz
                          · -- right
                            by_cases h1899 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e985_pos (not_le.mp h1888).le h1896 (not_le.mp h1897).le h1899 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e987_pos (not_le.mp h1888).le h1896 (not_le.mp h1899).le hz2 hz
                        · -- right
                          by_cases h1900 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1901 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e978_pos (not_le.mp h1896).le h1871 hz1 h1901 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e980_pos (not_le.mp h1896).le h1871 (not_le.mp h1901).le h1900 hz
                          · -- right
                            by_cases h1902 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e986_pos (not_le.mp h1896).le h1871 (not_le.mp h1900).le h1902 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e988_pos (not_le.mp h1896).le h1871 (not_le.mp h1902).le hz2 hz
                  · -- right
                    by_cases h1903 : a ≤ ((196899/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1904 : a ≤ ((392949/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1905 : a ≤ ((785049/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1906 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1907 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e989_pos (not_le.mp h1871).le h1905 hz1 h1907 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e991_pos (not_le.mp h1871).le h1905 (not_le.mp h1907).le h1906 hz
                          · -- right
                            by_cases h1908 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e997_pos (not_le.mp h1871).le h1905 (not_le.mp h1906).le h1908 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e999_pos (not_le.mp h1871).le h1905 (not_le.mp h1908).le hz2 hz
                        · -- right
                          by_cases h1909 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1910 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e990_pos (not_le.mp h1905).le h1904 hz1 h1910 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e992_pos (not_le.mp h1905).le h1904 (not_le.mp h1910).le h1909 hz
                          · -- right
                            by_cases h1911 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e998_pos (not_le.mp h1905).le h1904 (not_le.mp h1909).le h1911 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1000_pos (not_le.mp h1905).le h1904 (not_le.mp h1911).le hz2 hz
                      · -- right
                        by_cases h1912 : a ≤ ((786747/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1913 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1914 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e993_pos (not_le.mp h1904).le h1912 hz1 h1914 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e995_pos (not_le.mp h1904).le h1912 (not_le.mp h1914).le h1913 hz
                          · -- right
                            by_cases h1915 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1001_pos (not_le.mp h1904).le h1912 (not_le.mp h1913).le h1915 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1003_pos (not_le.mp h1904).le h1912 (not_le.mp h1915).le hz2 hz
                        · -- right
                          by_cases h1916 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1917 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e994_pos (not_le.mp h1912).le h1903 hz1 h1917 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e996_pos (not_le.mp h1912).le h1903 (not_le.mp h1917).le h1916 hz
                          · -- right
                            by_cases h1918 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1002_pos (not_le.mp h1912).le h1903 (not_le.mp h1916).le h1918 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1004_pos (not_le.mp h1912).le h1903 (not_le.mp h1918).le hz2 hz
                    · -- right
                      by_cases h1919 : a ≤ ((394647/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1920 : a ≤ ((157689/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1921 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1922 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1005_pos (not_le.mp h1903).le h1920 hz1 h1922 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1007_pos (not_le.mp h1903).le h1920 (not_le.mp h1922).le h1921 hz
                          · -- right
                            by_cases h1923 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1013_pos (not_le.mp h1903).le h1920 (not_le.mp h1921).le h1923 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1015_pos (not_le.mp h1903).le h1920 (not_le.mp h1923).le hz2 hz
                        · -- right
                          by_cases h1924 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1925 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1006_pos (not_le.mp h1920).le h1919 hz1 h1925 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1008_pos (not_le.mp h1920).le h1919 (not_le.mp h1925).le h1924 hz
                          · -- right
                            by_cases h1926 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1014_pos (not_le.mp h1920).le h1919 (not_le.mp h1924).le h1926 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1016_pos (not_le.mp h1920).le h1919 (not_le.mp h1926).le hz2 hz
                      · -- right
                        by_cases h1927 : a ≤ ((790143/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1928 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1929 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1009_pos (not_le.mp h1919).le h1927 hz1 h1929 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1011_pos (not_le.mp h1919).le h1927 (not_le.mp h1929).le h1928 hz
                          · -- right
                            by_cases h1930 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1017_pos (not_le.mp h1919).le h1927 (not_le.mp h1928).le h1930 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1019_pos (not_le.mp h1919).le h1927 (not_le.mp h1930).le hz2 hz
                        · -- right
                          by_cases h1931 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1932 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1010_pos (not_le.mp h1927).le h1870 hz1 h1932 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B016.e1012_pos (not_le.mp h1927).le h1870 (not_le.mp h1932).le h1931 hz
                          · -- right
                            by_cases h1933 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B016.e1018_pos (not_le.mp h1927).le h1870 (not_le.mp h1931).le h1933 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1020_pos (not_le.mp h1927).le h1870 (not_le.mp h1933).le hz2 hz
                · -- right
                  by_cases h1934 : a ≤ ((99723/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1935 : a ≤ ((198597/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h1936 : a ≤ ((79269/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h1937 : a ≤ ((791841/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1938 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1939 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1021_pos (not_le.mp h1870).le h1937 hz1 h1939 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1023_pos (not_le.mp h1870).le h1937 (not_le.mp h1939).le h1938 hz
                          · -- right
                            by_cases h1940 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1029_pos (not_le.mp h1870).le h1937 (not_le.mp h1938).le h1940 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1031_pos (not_le.mp h1870).le h1937 (not_le.mp h1940).le hz2 hz
                        · -- right
                          by_cases h1941 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1942 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1022_pos (not_le.mp h1937).le h1936 hz1 h1942 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1024_pos (not_le.mp h1937).le h1936 (not_le.mp h1942).le h1941 hz
                          · -- right
                            by_cases h1943 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1030_pos (not_le.mp h1937).le h1936 (not_le.mp h1941).le h1943 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1032_pos (not_le.mp h1937).le h1936 (not_le.mp h1943).le hz2 hz
                      · -- right
                        by_cases h1944 : a ≤ ((793539/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1945 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1946 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1025_pos (not_le.mp h1936).le h1944 hz1 h1946 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1027_pos (not_le.mp h1936).le h1944 (not_le.mp h1946).le h1945 hz
                          · -- right
                            by_cases h1947 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1033_pos (not_le.mp h1936).le h1944 (not_le.mp h1945).le h1947 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1035_pos (not_le.mp h1936).le h1944 (not_le.mp h1947).le hz2 hz
                        · -- right
                          by_cases h1948 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1949 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1026_pos (not_le.mp h1944).le h1935 hz1 h1949 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1028_pos (not_le.mp h1944).le h1935 (not_le.mp h1949).le h1948 hz
                          · -- right
                            by_cases h1950 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1034_pos (not_le.mp h1944).le h1935 (not_le.mp h1948).le h1950 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1036_pos (not_le.mp h1944).le h1935 (not_le.mp h1950).le hz2 hz
                    · -- right
                      by_cases h1951 : a ≤ ((398043/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1952 : a ≤ ((795237/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1953 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1954 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1037_pos (not_le.mp h1935).le h1952 hz1 h1954 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1039_pos (not_le.mp h1935).le h1952 (not_le.mp h1954).le h1953 hz
                          · -- right
                            by_cases h1955 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1045_pos (not_le.mp h1935).le h1952 (not_le.mp h1953).le h1955 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1047_pos (not_le.mp h1935).le h1952 (not_le.mp h1955).le hz2 hz
                        · -- right
                          by_cases h1956 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1957 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1038_pos (not_le.mp h1952).le h1951 hz1 h1957 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1040_pos (not_le.mp h1952).le h1951 (not_le.mp h1957).le h1956 hz
                          · -- right
                            by_cases h1958 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1046_pos (not_le.mp h1952).le h1951 (not_le.mp h1956).le h1958 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1048_pos (not_le.mp h1952).le h1951 (not_le.mp h1958).le hz2 hz
                      · -- right
                        by_cases h1959 : a ≤ ((159387/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h1960 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1961 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1041_pos (not_le.mp h1951).le h1959 hz1 h1961 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1043_pos (not_le.mp h1951).le h1959 (not_le.mp h1961).le h1960 hz
                          · -- right
                            by_cases h1962 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1049_pos (not_le.mp h1951).le h1959 (not_le.mp h1960).le h1962 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1051_pos (not_le.mp h1951).le h1959 (not_le.mp h1962).le hz2 hz
                        · -- right
                          by_cases h1963 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1964 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1042_pos (not_le.mp h1959).le h1934 hz1 h1964 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1044_pos (not_le.mp h1959).le h1934 (not_le.mp h1964).le h1963 hz
                          · -- right
                            by_cases h1965 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1050_pos (not_le.mp h1959).le h1934 (not_le.mp h1963).le h1965 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1052_pos (not_le.mp h1959).le h1934 (not_le.mp h1965).le hz2 hz
                  · -- right
                    by_cases h1966 : a ≤ ((40059/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h1967 : a ≤ ((399741/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1968 : a ≤ ((798633/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1969 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1970 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1053_pos (not_le.mp h1934).le h1968 hz1 h1970 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1055_pos (not_le.mp h1934).le h1968 (not_le.mp h1970).le h1969 hz
                          · -- right
                            by_cases h1971 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1061_pos (not_le.mp h1934).le h1968 (not_le.mp h1969).le h1971 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1063_pos (not_le.mp h1934).le h1968 (not_le.mp h1971).le hz2 hz
                        · -- right
                          by_cases h1972 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1973 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1054_pos (not_le.mp h1968).le h1967 hz1 h1973 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1056_pos (not_le.mp h1968).le h1967 (not_le.mp h1973).le h1972 hz
                          · -- right
                            by_cases h1974 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1062_pos (not_le.mp h1968).le h1967 (not_le.mp h1972).le h1974 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1064_pos (not_le.mp h1968).le h1967 (not_le.mp h1974).le hz2 hz
                      · -- right
                        by_cases h1975 : a ≤ ((800331/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1976 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1977 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1057_pos (not_le.mp h1967).le h1975 hz1 h1977 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1059_pos (not_le.mp h1967).le h1975 (not_le.mp h1977).le h1976 hz
                          · -- right
                            by_cases h1978 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1065_pos (not_le.mp h1967).le h1975 (not_le.mp h1976).le h1978 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1067_pos (not_le.mp h1967).le h1975 (not_le.mp h1978).le hz2 hz
                        · -- right
                          by_cases h1979 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1980 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1058_pos (not_le.mp h1975).le h1966 hz1 h1980 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1060_pos (not_le.mp h1975).le h1966 (not_le.mp h1980).le h1979 hz
                          · -- right
                            by_cases h1981 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1066_pos (not_le.mp h1975).le h1966 (not_le.mp h1979).le h1981 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1068_pos (not_le.mp h1975).le h1966 (not_le.mp h1981).le hz2 hz
                    · -- right
                      by_cases h1982 : a ≤ ((401439/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h1983 : a ≤ ((802029/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1984 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1985 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1069_pos (not_le.mp h1966).le h1983 hz1 h1985 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1071_pos (not_le.mp h1966).le h1983 (not_le.mp h1985).le h1984 hz
                          · -- right
                            by_cases h1986 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1077_pos (not_le.mp h1966).le h1983 (not_le.mp h1984).le h1986 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1079_pos (not_le.mp h1966).le h1983 (not_le.mp h1986).le hz2 hz
                        · -- right
                          by_cases h1987 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1988 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1070_pos (not_le.mp h1983).le h1982 hz1 h1988 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1072_pos (not_le.mp h1983).le h1982 (not_le.mp h1988).le h1987 hz
                          · -- right
                            by_cases h1989 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1078_pos (not_le.mp h1983).le h1982 (not_le.mp h1987).le h1989 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1080_pos (not_le.mp h1983).le h1982 (not_le.mp h1989).le hz2 hz
                      · -- right
                        by_cases h1990 : a ≤ ((803727/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h1991 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1992 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1073_pos (not_le.mp h1982).le h1990 hz1 h1992 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1075_pos (not_le.mp h1982).le h1990 (not_le.mp h1992).le h1991 hz
                          · -- right
                            by_cases h1993 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1081_pos (not_le.mp h1982).le h1990 (not_le.mp h1991).le h1993 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1083_pos (not_le.mp h1982).le h1990 (not_le.mp h1993).le hz2 hz
                        · -- right
                          by_cases h1994 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h1995 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B017.e1074_pos (not_le.mp h1990).le h1869 hz1 h1995 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B017.e1076_pos (not_le.mp h1990).le h1869 (not_le.mp h1995).le h1994 hz
                          · -- right
                            by_cases h1996 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1082_pos (not_le.mp h1990).le h1869 (not_le.mp h1994).le h1996 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1084_pos (not_le.mp h1990).le h1869 (not_le.mp h1996).le hz2 hz
              · -- right
                by_cases h1997 : a ≤ ((10227/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h1998 : a ≤ ((101421/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h1999 : a ≤ ((201993/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2000 : a ≤ ((403137/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2001 : a ≤ ((32217/163840 : ℚ) : ℝ)
                        · -- left
                          by_cases h2002 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2003 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1085_pos (not_le.mp h1869).le h2001 hz1 h2003 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1087_pos (not_le.mp h1869).le h2001 (not_le.mp h2003).le h2002 hz
                          · -- right
                            by_cases h2004 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1093_pos (not_le.mp h1869).le h2001 (not_le.mp h2002).le h2004 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1095_pos (not_le.mp h1869).le h2001 (not_le.mp h2004).le hz2 hz
                        · -- right
                          by_cases h2005 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2006 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1086_pos (not_le.mp h2001).le h2000 hz1 h2006 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1088_pos (not_le.mp h2001).le h2000 (not_le.mp h2006).le h2005 hz
                          · -- right
                            by_cases h2007 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1094_pos (not_le.mp h2001).le h2000 (not_le.mp h2005).le h2007 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1096_pos (not_le.mp h2001).le h2000 (not_le.mp h2007).le hz2 hz
                      · -- right
                        by_cases h2008 : a ≤ ((807123/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2009 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2010 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1089_pos (not_le.mp h2000).le h2008 hz1 h2010 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1091_pos (not_le.mp h2000).le h2008 (not_le.mp h2010).le h2009 hz
                          · -- right
                            by_cases h2011 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1097_pos (not_le.mp h2000).le h2008 (not_le.mp h2009).le h2011 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1099_pos (not_le.mp h2000).le h2008 (not_le.mp h2011).le hz2 hz
                        · -- right
                          by_cases h2012 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2013 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1090_pos (not_le.mp h2008).le h1999 hz1 h2013 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1092_pos (not_le.mp h2008).le h1999 (not_le.mp h2013).le h2012 hz
                          · -- right
                            by_cases h2014 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1098_pos (not_le.mp h2008).le h1999 (not_le.mp h2012).le h2014 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1100_pos (not_le.mp h2008).le h1999 (not_le.mp h2014).le hz2 hz
                    · -- right
                      by_cases h2015 : a ≤ ((80967/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2016 : a ≤ ((808821/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2017 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2018 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1101_pos (not_le.mp h1999).le h2016 hz1 h2018 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1103_pos (not_le.mp h1999).le h2016 (not_le.mp h2018).le h2017 hz
                          · -- right
                            by_cases h2019 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1109_pos (not_le.mp h1999).le h2016 (not_le.mp h2017).le h2019 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1111_pos (not_le.mp h1999).le h2016 (not_le.mp h2019).le hz2 hz
                        · -- right
                          by_cases h2020 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2021 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1102_pos (not_le.mp h2016).le h2015 hz1 h2021 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1104_pos (not_le.mp h2016).le h2015 (not_le.mp h2021).le h2020 hz
                          · -- right
                            by_cases h2022 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1110_pos (not_le.mp h2016).le h2015 (not_le.mp h2020).le h2022 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1112_pos (not_le.mp h2016).le h2015 (not_le.mp h2022).le hz2 hz
                      · -- right
                        by_cases h2023 : a ≤ ((810519/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2024 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2025 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1105_pos (not_le.mp h2015).le h2023 hz1 h2025 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1107_pos (not_le.mp h2015).le h2023 (not_le.mp h2025).le h2024 hz
                          · -- right
                            by_cases h2026 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1113_pos (not_le.mp h2015).le h2023 (not_le.mp h2024).le h2026 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1115_pos (not_le.mp h2015).le h2023 (not_le.mp h2026).le hz2 hz
                        · -- right
                          by_cases h2027 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2028 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1106_pos (not_le.mp h2023).le h1998 hz1 h2028 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1108_pos (not_le.mp h2023).le h1998 (not_le.mp h2028).le h2027 hz
                          · -- right
                            by_cases h2029 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1114_pos (not_le.mp h2023).le h1998 (not_le.mp h2027).le h2029 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1116_pos (not_le.mp h2023).le h1998 (not_le.mp h2029).le hz2 hz
                  · -- right
                    by_cases h2030 : a ≤ ((203691/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2031 : a ≤ ((406533/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2032 : a ≤ ((812217/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2033 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2034 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1117_pos (not_le.mp h1998).le h2032 hz1 h2034 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1119_pos (not_le.mp h1998).le h2032 (not_le.mp h2034).le h2033 hz
                          · -- right
                            by_cases h2035 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1125_pos (not_le.mp h1998).le h2032 (not_le.mp h2033).le h2035 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1127_pos (not_le.mp h1998).le h2032 (not_le.mp h2035).le hz2 hz
                        · -- right
                          by_cases h2036 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2037 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1118_pos (not_le.mp h2032).le h2031 hz1 h2037 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1120_pos (not_le.mp h2032).le h2031 (not_le.mp h2037).le h2036 hz
                          · -- right
                            by_cases h2038 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1126_pos (not_le.mp h2032).le h2031 (not_le.mp h2036).le h2038 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1128_pos (not_le.mp h2032).le h2031 (not_le.mp h2038).le hz2 hz
                      · -- right
                        by_cases h2039 : a ≤ ((162783/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2040 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2041 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1121_pos (not_le.mp h2031).le h2039 hz1 h2041 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1123_pos (not_le.mp h2031).le h2039 (not_le.mp h2041).le h2040 hz
                          · -- right
                            by_cases h2042 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1129_pos (not_le.mp h2031).le h2039 (not_le.mp h2040).le h2042 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1131_pos (not_le.mp h2031).le h2039 (not_le.mp h2042).le hz2 hz
                        · -- right
                          by_cases h2043 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2044 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1122_pos (not_le.mp h2039).le h2030 hz1 h2044 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1124_pos (not_le.mp h2039).le h2030 (not_le.mp h2044).le h2043 hz
                          · -- right
                            by_cases h2045 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1130_pos (not_le.mp h2039).le h2030 (not_le.mp h2043).le h2045 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1132_pos (not_le.mp h2039).le h2030 (not_le.mp h2045).le hz2 hz
                    · -- right
                      by_cases h2046 : a ≤ ((408231/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2047 : a ≤ ((815613/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2048 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2049 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1133_pos (not_le.mp h2030).le h2047 hz1 h2049 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1135_pos (not_le.mp h2030).le h2047 (not_le.mp h2049).le h2048 hz
                          · -- right
                            by_cases h2050 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1141_pos (not_le.mp h2030).le h2047 (not_le.mp h2048).le h2050 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1143_pos (not_le.mp h2030).le h2047 (not_le.mp h2050).le hz2 hz
                        · -- right
                          by_cases h2051 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2052 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1134_pos (not_le.mp h2047).le h2046 hz1 h2052 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1136_pos (not_le.mp h2047).le h2046 (not_le.mp h2052).le h2051 hz
                          · -- right
                            by_cases h2053 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1142_pos (not_le.mp h2047).le h2046 (not_le.mp h2051).le h2053 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1144_pos (not_le.mp h2047).le h2046 (not_le.mp h2053).le hz2 hz
                      · -- right
                        by_cases h2054 : a ≤ ((817311/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2055 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2056 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1137_pos (not_le.mp h2046).le h2054 hz1 h2056 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B018.e1139_pos (not_le.mp h2046).le h2054 (not_le.mp h2056).le h2055 hz
                          · -- right
                            by_cases h2057 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1145_pos (not_le.mp h2046).le h2054 (not_le.mp h2055).le h2057 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1147_pos (not_le.mp h2046).le h2054 (not_le.mp h2057).le hz2 hz
                        · -- right
                          by_cases h2058 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2059 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B018.e1138_pos (not_le.mp h2054).le h1997 hz1 h2059 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1140_pos (not_le.mp h2054).le h1997 (not_le.mp h2059).le h2058 hz
                          · -- right
                            by_cases h2060 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1146_pos (not_le.mp h2054).le h1997 (not_le.mp h2058).le h2060 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1148_pos (not_le.mp h2054).le h1997 (not_le.mp h2060).le hz2 hz
                · -- right
                  by_cases h2061 : a ≤ ((103119/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2062 : a ≤ ((205389/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2063 : a ≤ ((409929/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2064 : a ≤ ((819009/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2065 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2066 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1149_pos (not_le.mp h1997).le h2064 hz1 h2066 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1151_pos (not_le.mp h1997).le h2064 (not_le.mp h2066).le h2065 hz
                          · -- right
                            by_cases h2067 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1157_pos (not_le.mp h1997).le h2064 (not_le.mp h2065).le h2067 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1159_pos (not_le.mp h1997).le h2064 (not_le.mp h2067).le hz2 hz
                        · -- right
                          by_cases h2068 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2069 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1150_pos (not_le.mp h2064).le h2063 hz1 h2069 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1152_pos (not_le.mp h2064).le h2063 (not_le.mp h2069).le h2068 hz
                          · -- right
                            by_cases h2070 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1158_pos (not_le.mp h2064).le h2063 (not_le.mp h2068).le h2070 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1160_pos (not_le.mp h2064).le h2063 (not_le.mp h2070).le hz2 hz
                      · -- right
                        by_cases h2071 : a ≤ ((820707/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2072 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2073 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1153_pos (not_le.mp h2063).le h2071 hz1 h2073 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1155_pos (not_le.mp h2063).le h2071 (not_le.mp h2073).le h2072 hz
                          · -- right
                            by_cases h2074 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1161_pos (not_le.mp h2063).le h2071 (not_le.mp h2072).le h2074 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1163_pos (not_le.mp h2063).le h2071 (not_le.mp h2074).le hz2 hz
                        · -- right
                          by_cases h2075 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2076 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1154_pos (not_le.mp h2071).le h2062 hz1 h2076 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1156_pos (not_le.mp h2071).le h2062 (not_le.mp h2076).le h2075 hz
                          · -- right
                            by_cases h2077 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1162_pos (not_le.mp h2071).le h2062 (not_le.mp h2075).le h2077 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1164_pos (not_le.mp h2071).le h2062 (not_le.mp h2077).le hz2 hz
                    · -- right
                      by_cases h2078 : a ≤ ((411627/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2079 : a ≤ ((164481/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2080 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2081 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1165_pos (not_le.mp h2062).le h2079 hz1 h2081 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1167_pos (not_le.mp h2062).le h2079 (not_le.mp h2081).le h2080 hz
                          · -- right
                            by_cases h2082 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1173_pos (not_le.mp h2062).le h2079 (not_le.mp h2080).le h2082 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1175_pos (not_le.mp h2062).le h2079 (not_le.mp h2082).le hz2 hz
                        · -- right
                          by_cases h2083 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2084 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1166_pos (not_le.mp h2079).le h2078 hz1 h2084 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1168_pos (not_le.mp h2079).le h2078 (not_le.mp h2084).le h2083 hz
                          · -- right
                            by_cases h2085 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1174_pos (not_le.mp h2079).le h2078 (not_le.mp h2083).le h2085 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1176_pos (not_le.mp h2079).le h2078 (not_le.mp h2085).le hz2 hz
                      · -- right
                        by_cases h2086 : a ≤ ((824103/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2087 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2088 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1169_pos (not_le.mp h2078).le h2086 hz1 h2088 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1171_pos (not_le.mp h2078).le h2086 (not_le.mp h2088).le h2087 hz
                          · -- right
                            by_cases h2089 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1177_pos (not_le.mp h2078).le h2086 (not_le.mp h2087).le h2089 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1179_pos (not_le.mp h2078).le h2086 (not_le.mp h2089).le hz2 hz
                        · -- right
                          by_cases h2090 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2091 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1170_pos (not_le.mp h2086).le h2061 hz1 h2091 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1172_pos (not_le.mp h2086).le h2061 (not_le.mp h2091).le h2090 hz
                          · -- right
                            by_cases h2092 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1178_pos (not_le.mp h2086).le h2061 (not_le.mp h2090).le h2092 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1180_pos (not_le.mp h2086).le h2061 (not_le.mp h2092).le hz2 hz
                  · -- right
                    by_cases h2093 : a ≤ ((207087/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2094 : a ≤ ((16533/81920 : ℚ) : ℝ)
                      · -- left
                        by_cases h2095 : a ≤ ((825801/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2096 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2097 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1181_pos (not_le.mp h2061).le h2095 hz1 h2097 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1183_pos (not_le.mp h2061).le h2095 (not_le.mp h2097).le h2096 hz
                          · -- right
                            by_cases h2098 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1189_pos (not_le.mp h2061).le h2095 (not_le.mp h2096).le h2098 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1191_pos (not_le.mp h2061).le h2095 (not_le.mp h2098).le hz2 hz
                        · -- right
                          by_cases h2099 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2100 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1182_pos (not_le.mp h2095).le h2094 hz1 h2100 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1184_pos (not_le.mp h2095).le h2094 (not_le.mp h2100).le h2099 hz
                          · -- right
                            by_cases h2101 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1190_pos (not_le.mp h2095).le h2094 (not_le.mp h2099).le h2101 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1192_pos (not_le.mp h2095).le h2094 (not_le.mp h2101).le hz2 hz
                      · -- right
                        by_cases h2102 : a ≤ ((827499/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2103 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2104 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1185_pos (not_le.mp h2094).le h2102 hz1 h2104 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1187_pos (not_le.mp h2094).le h2102 (not_le.mp h2104).le h2103 hz
                          · -- right
                            by_cases h2105 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1193_pos (not_le.mp h2094).le h2102 (not_le.mp h2103).le h2105 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1195_pos (not_le.mp h2094).le h2102 (not_le.mp h2105).le hz2 hz
                        · -- right
                          by_cases h2106 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2107 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1186_pos (not_le.mp h2102).le h2093 hz1 h2107 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1188_pos (not_le.mp h2102).le h2093 (not_le.mp h2107).le h2106 hz
                          · -- right
                            by_cases h2108 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1194_pos (not_le.mp h2102).le h2093 (not_le.mp h2106).le h2108 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1196_pos (not_le.mp h2102).le h2093 (not_le.mp h2108).le hz2 hz
                    · -- right
                      by_cases h2109 : a ≤ ((415023/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2110 : a ≤ ((829197/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2111 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2112 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1197_pos (not_le.mp h2093).le h2110 hz1 h2112 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B019.e1199_pos (not_le.mp h2093).le h2110 (not_le.mp h2112).le h2111 hz
                          · -- right
                            by_cases h2113 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1205_pos (not_le.mp h2093).le h2110 (not_le.mp h2111).le h2113 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1207_pos (not_le.mp h2093).le h2110 (not_le.mp h2113).le hz2 hz
                        · -- right
                          by_cases h2114 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2115 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B019.e1198_pos (not_le.mp h2110).le h2109 hz1 h2115 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1200_pos (not_le.mp h2110).le h2109 (not_le.mp h2115).le h2114 hz
                          · -- right
                            by_cases h2116 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1206_pos (not_le.mp h2110).le h2109 (not_le.mp h2114).le h2116 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1208_pos (not_le.mp h2110).le h2109 (not_le.mp h2116).le hz2 hz
                      · -- right
                        by_cases h2117 : a ≤ ((166179/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2118 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2119 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1201_pos (not_le.mp h2109).le h2117 hz1 h2119 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1203_pos (not_le.mp h2109).le h2117 (not_le.mp h2119).le h2118 hz
                          · -- right
                            by_cases h2120 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1209_pos (not_le.mp h2109).le h2117 (not_le.mp h2118).le h2120 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1211_pos (not_le.mp h2109).le h2117 (not_le.mp h2120).le hz2 hz
                        · -- right
                          by_cases h2121 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2122 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1202_pos (not_le.mp h2117).le h3 hz1 h2122 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1204_pos (not_le.mp h2117).le h3 (not_le.mp h2122).le h2121 hz
                          · -- right
                            by_cases h2123 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1210_pos (not_le.mp h2117).le h3 (not_le.mp h2121).le h2123 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1212_pos (not_le.mp h2117).le h3 (not_le.mp h2123).le hz2 hz
        · -- right
          by_cases h2124 : a ≤ ((7347/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2125 : a ≤ ((2769/12800 : ℚ) : ℝ)
            · -- left
              by_cases h2126 : a ≤ ((26841/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2127 : a ≤ ((52833/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2128 : a ≤ ((104817/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2129 : a ≤ ((41757/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2130 : a ≤ ((416721/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2131 : a ≤ ((832593/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2132 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2133 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1213_pos (not_le.mp h3).le h2131 hz1 h2133 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1215_pos (not_le.mp h3).le h2131 (not_le.mp h2133).le h2132 hz
                          · -- right
                            by_cases h2134 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1221_pos (not_le.mp h3).le h2131 (not_le.mp h2132).le h2134 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1223_pos (not_le.mp h3).le h2131 (not_le.mp h2134).le hz2 hz
                        · -- right
                          by_cases h2135 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2136 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1214_pos (not_le.mp h2131).le h2130 hz1 h2136 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1216_pos (not_le.mp h2131).le h2130 (not_le.mp h2136).le h2135 hz
                          · -- right
                            by_cases h2137 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1222_pos (not_le.mp h2131).le h2130 (not_le.mp h2135).le h2137 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1224_pos (not_le.mp h2131).le h2130 (not_le.mp h2137).le hz2 hz
                      · -- right
                        by_cases h2138 : a ≤ ((834291/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2139 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2140 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1217_pos (not_le.mp h2130).le h2138 hz1 h2140 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1219_pos (not_le.mp h2130).le h2138 (not_le.mp h2140).le h2139 hz
                          · -- right
                            by_cases h2141 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1225_pos (not_le.mp h2130).le h2138 (not_le.mp h2139).le h2141 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1227_pos (not_le.mp h2130).le h2138 (not_le.mp h2141).le hz2 hz
                        · -- right
                          by_cases h2142 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2143 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1218_pos (not_le.mp h2138).le h2129 hz1 h2143 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1220_pos (not_le.mp h2138).le h2129 (not_le.mp h2143).le h2142 hz
                          · -- right
                            by_cases h2144 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1226_pos (not_le.mp h2138).le h2129 (not_le.mp h2142).le h2144 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1228_pos (not_le.mp h2138).le h2129 (not_le.mp h2144).le hz2 hz
                    · -- right
                      by_cases h2145 : a ≤ ((418419/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2146 : a ≤ ((835989/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2147 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2148 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1229_pos (not_le.mp h2129).le h2146 hz1 h2148 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1231_pos (not_le.mp h2129).le h2146 (not_le.mp h2148).le h2147 hz
                          · -- right
                            by_cases h2149 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1237_pos (not_le.mp h2129).le h2146 (not_le.mp h2147).le h2149 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1239_pos (not_le.mp h2129).le h2146 (not_le.mp h2149).le hz2 hz
                        · -- right
                          by_cases h2150 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2151 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1230_pos (not_le.mp h2146).le h2145 hz1 h2151 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1232_pos (not_le.mp h2146).le h2145 (not_le.mp h2151).le h2150 hz
                          · -- right
                            by_cases h2152 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1238_pos (not_le.mp h2146).le h2145 (not_le.mp h2150).le h2152 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1240_pos (not_le.mp h2146).le h2145 (not_le.mp h2152).le hz2 hz
                      · -- right
                        by_cases h2153 : a ≤ ((837687/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2154 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2155 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1233_pos (not_le.mp h2145).le h2153 hz1 h2155 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1235_pos (not_le.mp h2145).le h2153 (not_le.mp h2155).le h2154 hz
                          · -- right
                            by_cases h2156 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1241_pos (not_le.mp h2145).le h2153 (not_le.mp h2154).le h2156 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1243_pos (not_le.mp h2145).le h2153 (not_le.mp h2156).le hz2 hz
                        · -- right
                          by_cases h2157 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2158 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1234_pos (not_le.mp h2153).le h2128 hz1 h2158 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1236_pos (not_le.mp h2153).le h2128 (not_le.mp h2158).le h2157 hz
                          · -- right
                            by_cases h2159 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1242_pos (not_le.mp h2153).le h2128 (not_le.mp h2157).le h2159 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1244_pos (not_le.mp h2153).le h2128 (not_le.mp h2159).le hz2 hz
                  · -- right
                    by_cases h2160 : a ≤ ((210483/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2161 : a ≤ ((420117/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2162 : a ≤ ((167877/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2163 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2164 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1245_pos (not_le.mp h2128).le h2162 hz1 h2164 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1247_pos (not_le.mp h2128).le h2162 (not_le.mp h2164).le h2163 hz
                          · -- right
                            by_cases h2165 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1253_pos (not_le.mp h2128).le h2162 (not_le.mp h2163).le h2165 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1255_pos (not_le.mp h2128).le h2162 (not_le.mp h2165).le hz2 hz
                        · -- right
                          by_cases h2166 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2167 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1246_pos (not_le.mp h2162).le h2161 hz1 h2167 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1248_pos (not_le.mp h2162).le h2161 (not_le.mp h2167).le h2166 hz
                          · -- right
                            by_cases h2168 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1254_pos (not_le.mp h2162).le h2161 (not_le.mp h2166).le h2168 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1256_pos (not_le.mp h2162).le h2161 (not_le.mp h2168).le hz2 hz
                      · -- right
                        by_cases h2169 : a ≤ ((841083/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2170 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2171 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1249_pos (not_le.mp h2161).le h2169 hz1 h2171 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1251_pos (not_le.mp h2161).le h2169 (not_le.mp h2171).le h2170 hz
                          · -- right
                            by_cases h2172 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1257_pos (not_le.mp h2161).le h2169 (not_le.mp h2170).le h2172 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1259_pos (not_le.mp h2161).le h2169 (not_le.mp h2172).le hz2 hz
                        · -- right
                          by_cases h2173 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2174 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1250_pos (not_le.mp h2169).le h2160 hz1 h2174 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B020.e1252_pos (not_le.mp h2169).le h2160 (not_le.mp h2174).le h2173 hz
                          · -- right
                            by_cases h2175 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B020.e1258_pos (not_le.mp h2169).le h2160 (not_le.mp h2173).le h2175 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1260_pos (not_le.mp h2169).le h2160 (not_le.mp h2175).le hz2 hz
                    · -- right
                      by_cases h2176 : a ≤ ((84363/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2177 : a ≤ ((842781/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2178 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2179 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1261_pos (not_le.mp h2160).le h2177 hz1 h2179 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1263_pos (not_le.mp h2160).le h2177 (not_le.mp h2179).le h2178 hz
                          · -- right
                            by_cases h2180 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1269_pos (not_le.mp h2160).le h2177 (not_le.mp h2178).le h2180 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1271_pos (not_le.mp h2160).le h2177 (not_le.mp h2180).le hz2 hz
                        · -- right
                          by_cases h2181 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2182 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1262_pos (not_le.mp h2177).le h2176 hz1 h2182 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1264_pos (not_le.mp h2177).le h2176 (not_le.mp h2182).le h2181 hz
                          · -- right
                            by_cases h2183 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1270_pos (not_le.mp h2177).le h2176 (not_le.mp h2181).le h2183 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1272_pos (not_le.mp h2177).le h2176 (not_le.mp h2183).le hz2 hz
                      · -- right
                        by_cases h2184 : a ≤ ((844479/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2185 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2186 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1265_pos (not_le.mp h2176).le h2184 hz1 h2186 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1267_pos (not_le.mp h2176).le h2184 (not_le.mp h2186).le h2185 hz
                          · -- right
                            by_cases h2187 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1273_pos (not_le.mp h2176).le h2184 (not_le.mp h2185).le h2187 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1275_pos (not_le.mp h2176).le h2184 (not_le.mp h2187).le hz2 hz
                        · -- right
                          by_cases h2188 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2189 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1266_pos (not_le.mp h2184).le h2127 hz1 h2189 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1268_pos (not_le.mp h2184).le h2127 (not_le.mp h2189).le h2188 hz
                          · -- right
                            by_cases h2190 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1274_pos (not_le.mp h2184).le h2127 (not_le.mp h2188).le h2190 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1276_pos (not_le.mp h2184).le h2127 (not_le.mp h2190).le hz2 hz
                · -- right
                  by_cases h2191 : a ≤ ((21303/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2192 : a ≤ ((212181/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2193 : a ≤ ((423513/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2194 : a ≤ ((846177/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2195 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2196 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1277_pos (not_le.mp h2127).le h2194 hz1 h2196 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1279_pos (not_le.mp h2127).le h2194 (not_le.mp h2196).le h2195 hz
                          · -- right
                            by_cases h2197 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1285_pos (not_le.mp h2127).le h2194 (not_le.mp h2195).le h2197 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1287_pos (not_le.mp h2127).le h2194 (not_le.mp h2197).le hz2 hz
                        · -- right
                          by_cases h2198 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2199 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1278_pos (not_le.mp h2194).le h2193 hz1 h2199 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1280_pos (not_le.mp h2194).le h2193 (not_le.mp h2199).le h2198 hz
                          · -- right
                            by_cases h2200 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1286_pos (not_le.mp h2194).le h2193 (not_le.mp h2198).le h2200 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1288_pos (not_le.mp h2194).le h2193 (not_le.mp h2200).le hz2 hz
                      · -- right
                        by_cases h2201 : a ≤ ((6783/32768 : ℚ) : ℝ)
                        · -- left
                          by_cases h2202 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2203 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1281_pos (not_le.mp h2193).le h2201 hz1 h2203 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1283_pos (not_le.mp h2193).le h2201 (not_le.mp h2203).le h2202 hz
                          · -- right
                            by_cases h2204 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1289_pos (not_le.mp h2193).le h2201 (not_le.mp h2202).le h2204 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1291_pos (not_le.mp h2193).le h2201 (not_le.mp h2204).le hz2 hz
                        · -- right
                          by_cases h2205 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2206 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1282_pos (not_le.mp h2201).le h2192 hz1 h2206 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1284_pos (not_le.mp h2201).le h2192 (not_le.mp h2206).le h2205 hz
                          · -- right
                            by_cases h2207 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1290_pos (not_le.mp h2201).le h2192 (not_le.mp h2205).le h2207 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1292_pos (not_le.mp h2201).le h2192 (not_le.mp h2207).le hz2 hz
                    · -- right
                      by_cases h2208 : a ≤ ((425211/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2209 : a ≤ ((849573/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2210 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2211 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1293_pos (not_le.mp h2192).le h2209 hz1 h2211 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1295_pos (not_le.mp h2192).le h2209 (not_le.mp h2211).le h2210 hz
                          · -- right
                            by_cases h2212 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1301_pos (not_le.mp h2192).le h2209 (not_le.mp h2210).le h2212 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1303_pos (not_le.mp h2192).le h2209 (not_le.mp h2212).le hz2 hz
                        · -- right
                          by_cases h2213 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2214 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1294_pos (not_le.mp h2209).le h2208 hz1 h2214 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1296_pos (not_le.mp h2209).le h2208 (not_le.mp h2214).le h2213 hz
                          · -- right
                            by_cases h2215 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1302_pos (not_le.mp h2209).le h2208 (not_le.mp h2213).le h2215 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1304_pos (not_le.mp h2209).le h2208 (not_le.mp h2215).le hz2 hz
                      · -- right
                        by_cases h2216 : a ≤ ((851271/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2217 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2218 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1297_pos (not_le.mp h2208).le h2216 hz1 h2218 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1299_pos (not_le.mp h2208).le h2216 (not_le.mp h2218).le h2217 hz
                          · -- right
                            by_cases h2219 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1305_pos (not_le.mp h2208).le h2216 (not_le.mp h2217).le h2219 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1307_pos (not_le.mp h2208).le h2216 (not_le.mp h2219).le hz2 hz
                        · -- right
                          by_cases h2220 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2221 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1298_pos (not_le.mp h2216).le h2191 hz1 h2221 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1300_pos (not_le.mp h2216).le h2191 (not_le.mp h2221).le h2220 hz
                          · -- right
                            by_cases h2222 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1306_pos (not_le.mp h2216).le h2191 (not_le.mp h2220).le h2222 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1308_pos (not_le.mp h2216).le h2191 (not_le.mp h2222).le hz2 hz
                  · -- right
                    by_cases h2223 : a ≤ ((213879/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2224 : a ≤ ((426909/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2225 : a ≤ ((852969/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2226 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2227 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1309_pos (not_le.mp h2191).le h2225 hz1 h2227 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1311_pos (not_le.mp h2191).le h2225 (not_le.mp h2227).le h2226 hz
                          · -- right
                            by_cases h2228 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1317_pos (not_le.mp h2191).le h2225 (not_le.mp h2226).le h2228 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1319_pos (not_le.mp h2191).le h2225 (not_le.mp h2228).le hz2 hz
                        · -- right
                          by_cases h2229 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2230 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1310_pos (not_le.mp h2225).le h2224 hz1 h2230 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1312_pos (not_le.mp h2225).le h2224 (not_le.mp h2230).le h2229 hz
                          · -- right
                            by_cases h2231 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1318_pos (not_le.mp h2225).le h2224 (not_le.mp h2229).le h2231 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1320_pos (not_le.mp h2225).le h2224 (not_le.mp h2231).le hz2 hz
                      · -- right
                        by_cases h2232 : a ≤ ((854667/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2233 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2234 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1313_pos (not_le.mp h2224).le h2232 hz1 h2234 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1315_pos (not_le.mp h2224).le h2232 (not_le.mp h2234).le h2233 hz
                          · -- right
                            by_cases h2235 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1321_pos (not_le.mp h2224).le h2232 (not_le.mp h2233).le h2235 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1323_pos (not_le.mp h2224).le h2232 (not_le.mp h2235).le hz2 hz
                        · -- right
                          by_cases h2236 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2237 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B021.e1314_pos (not_le.mp h2232).le h2223 hz1 h2237 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B021.e1316_pos (not_le.mp h2232).le h2223 (not_le.mp h2237).le h2236 hz
                          · -- right
                            by_cases h2238 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1322_pos (not_le.mp h2232).le h2223 (not_le.mp h2236).le h2238 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1324_pos (not_le.mp h2232).le h2223 (not_le.mp h2238).le hz2 hz
                    · -- right
                      by_cases h2239 : a ≤ ((428607/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2240 : a ≤ ((171273/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2241 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2242 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1325_pos (not_le.mp h2223).le h2240 hz1 h2242 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1327_pos (not_le.mp h2223).le h2240 (not_le.mp h2242).le h2241 hz
                          · -- right
                            by_cases h2243 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1333_pos (not_le.mp h2223).le h2240 (not_le.mp h2241).le h2243 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1335_pos (not_le.mp h2223).le h2240 (not_le.mp h2243).le hz2 hz
                        · -- right
                          by_cases h2244 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2245 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1326_pos (not_le.mp h2240).le h2239 hz1 h2245 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1328_pos (not_le.mp h2240).le h2239 (not_le.mp h2245).le h2244 hz
                          · -- right
                            by_cases h2246 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1334_pos (not_le.mp h2240).le h2239 (not_le.mp h2244).le h2246 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1336_pos (not_le.mp h2240).le h2239 (not_le.mp h2246).le hz2 hz
                      · -- right
                        by_cases h2247 : a ≤ ((858063/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2248 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2249 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1329_pos (not_le.mp h2239).le h2247 hz1 h2249 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1331_pos (not_le.mp h2239).le h2247 (not_le.mp h2249).le h2248 hz
                          · -- right
                            by_cases h2250 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1337_pos (not_le.mp h2239).le h2247 (not_le.mp h2248).le h2250 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1339_pos (not_le.mp h2239).le h2247 (not_le.mp h2250).le hz2 hz
                        · -- right
                          by_cases h2251 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2252 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1330_pos (not_le.mp h2247).le h2126 hz1 h2252 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1332_pos (not_le.mp h2247).le h2126 (not_le.mp h2252).le h2251 hz
                          · -- right
                            by_cases h2253 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1338_pos (not_le.mp h2247).le h2126 (not_le.mp h2251).le h2253 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1340_pos (not_le.mp h2247).le h2126 (not_le.mp h2253).le hz2 hz
              · -- right
                by_cases h2254 : a ≤ ((54531/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2255 : a ≤ ((108213/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2256 : a ≤ ((215577/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2257 : a ≤ ((86061/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2258 : a ≤ ((859761/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2259 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2260 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1341_pos (not_le.mp h2126).le h2258 hz1 h2260 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1343_pos (not_le.mp h2126).le h2258 (not_le.mp h2260).le h2259 hz
                          · -- right
                            by_cases h2261 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1349_pos (not_le.mp h2126).le h2258 (not_le.mp h2259).le h2261 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1351_pos (not_le.mp h2126).le h2258 (not_le.mp h2261).le hz2 hz
                        · -- right
                          by_cases h2262 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2263 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1342_pos (not_le.mp h2258).le h2257 hz1 h2263 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1344_pos (not_le.mp h2258).le h2257 (not_le.mp h2263).le h2262 hz
                          · -- right
                            by_cases h2264 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1350_pos (not_le.mp h2258).le h2257 (not_le.mp h2262).le h2264 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1352_pos (not_le.mp h2258).le h2257 (not_le.mp h2264).le hz2 hz
                      · -- right
                        by_cases h2265 : a ≤ ((861459/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2266 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2267 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1345_pos (not_le.mp h2257).le h2265 hz1 h2267 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1347_pos (not_le.mp h2257).le h2265 (not_le.mp h2267).le h2266 hz
                          · -- right
                            by_cases h2268 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1353_pos (not_le.mp h2257).le h2265 (not_le.mp h2266).le h2268 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1355_pos (not_le.mp h2257).le h2265 (not_le.mp h2268).le hz2 hz
                        · -- right
                          by_cases h2269 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2270 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1346_pos (not_le.mp h2265).le h2256 hz1 h2270 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1348_pos (not_le.mp h2265).le h2256 (not_le.mp h2270).le h2269 hz
                          · -- right
                            by_cases h2271 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1354_pos (not_le.mp h2265).le h2256 (not_le.mp h2269).le h2271 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1356_pos (not_le.mp h2265).le h2256 (not_le.mp h2271).le hz2 hz
                    · -- right
                      by_cases h2272 : a ≤ ((432003/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2273 : a ≤ ((863157/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2274 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2275 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1357_pos (not_le.mp h2256).le h2273 hz1 h2275 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1359_pos (not_le.mp h2256).le h2273 (not_le.mp h2275).le h2274 hz
                          · -- right
                            by_cases h2276 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1365_pos (not_le.mp h2256).le h2273 (not_le.mp h2274).le h2276 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1367_pos (not_le.mp h2256).le h2273 (not_le.mp h2276).le hz2 hz
                        · -- right
                          by_cases h2277 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2278 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1358_pos (not_le.mp h2273).le h2272 hz1 h2278 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1360_pos (not_le.mp h2273).le h2272 (not_le.mp h2278).le h2277 hz
                          · -- right
                            by_cases h2279 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1366_pos (not_le.mp h2273).le h2272 (not_le.mp h2277).le h2279 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1368_pos (not_le.mp h2273).le h2272 (not_le.mp h2279).le hz2 hz
                      · -- right
                        by_cases h2280 : a ≤ ((172971/819200 : ℚ) : ℝ)
                        · -- left
                          by_cases h2281 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2282 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1361_pos (not_le.mp h2272).le h2280 hz1 h2282 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1363_pos (not_le.mp h2272).le h2280 (not_le.mp h2282).le h2281 hz
                          · -- right
                            by_cases h2283 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1369_pos (not_le.mp h2272).le h2280 (not_le.mp h2281).le h2283 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1371_pos (not_le.mp h2272).le h2280 (not_le.mp h2283).le hz2 hz
                        · -- right
                          by_cases h2284 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2285 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1362_pos (not_le.mp h2280).le h2255 hz1 h2285 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1364_pos (not_le.mp h2280).le h2255 (not_le.mp h2285).le h2284 hz
                          · -- right
                            by_cases h2286 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1370_pos (not_le.mp h2280).le h2255 (not_le.mp h2284).le h2286 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1372_pos (not_le.mp h2280).le h2255 (not_le.mp h2286).le hz2 hz
                  · -- right
                    by_cases h2287 : a ≤ ((8691/40960 : ℚ) : ℝ)
                    · -- left
                      by_cases h2288 : a ≤ ((433701/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2289 : a ≤ ((866553/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2290 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2291 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1373_pos (not_le.mp h2255).le h2289 hz1 h2291 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1375_pos (not_le.mp h2255).le h2289 (not_le.mp h2291).le h2290 hz
                          · -- right
                            by_cases h2292 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1381_pos (not_le.mp h2255).le h2289 (not_le.mp h2290).le h2292 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1383_pos (not_le.mp h2255).le h2289 (not_le.mp h2292).le hz2 hz
                        · -- right
                          by_cases h2293 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2294 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1374_pos (not_le.mp h2289).le h2288 hz1 h2294 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1376_pos (not_le.mp h2289).le h2288 (not_le.mp h2294).le h2293 hz
                          · -- right
                            by_cases h2295 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1382_pos (not_le.mp h2289).le h2288 (not_le.mp h2293).le h2295 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1384_pos (not_le.mp h2289).le h2288 (not_le.mp h2295).le hz2 hz
                      · -- right
                        by_cases h2296 : a ≤ ((868251/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2297 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2298 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1377_pos (not_le.mp h2288).le h2296 hz1 h2298 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B022.e1379_pos (not_le.mp h2288).le h2296 (not_le.mp h2298).le h2297 hz
                          · -- right
                            by_cases h2299 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1385_pos (not_le.mp h2288).le h2296 (not_le.mp h2297).le h2299 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1387_pos (not_le.mp h2288).le h2296 (not_le.mp h2299).le hz2 hz
                        · -- right
                          by_cases h2300 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2301 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B022.e1378_pos (not_le.mp h2296).le h2287 hz1 h2301 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1380_pos (not_le.mp h2296).le h2287 (not_le.mp h2301).le h2300 hz
                          · -- right
                            by_cases h2302 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1386_pos (not_le.mp h2296).le h2287 (not_le.mp h2300).le h2302 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1388_pos (not_le.mp h2296).le h2287 (not_le.mp h2302).le hz2 hz
                    · -- right
                      by_cases h2303 : a ≤ ((435399/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2304 : a ≤ ((869949/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2305 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2306 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1389_pos (not_le.mp h2287).le h2304 hz1 h2306 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1391_pos (not_le.mp h2287).le h2304 (not_le.mp h2306).le h2305 hz
                          · -- right
                            by_cases h2307 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1397_pos (not_le.mp h2287).le h2304 (not_le.mp h2305).le h2307 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1399_pos (not_le.mp h2287).le h2304 (not_le.mp h2307).le hz2 hz
                        · -- right
                          by_cases h2308 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2309 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1390_pos (not_le.mp h2304).le h2303 hz1 h2309 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1392_pos (not_le.mp h2304).le h2303 (not_le.mp h2309).le h2308 hz
                          · -- right
                            by_cases h2310 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1398_pos (not_le.mp h2304).le h2303 (not_le.mp h2308).le h2310 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1400_pos (not_le.mp h2304).le h2303 (not_le.mp h2310).le hz2 hz
                      · -- right
                        by_cases h2311 : a ≤ ((871647/4096000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2312 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2313 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1393_pos (not_le.mp h2303).le h2311 hz1 h2313 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1395_pos (not_le.mp h2303).le h2311 (not_le.mp h2313).le h2312 hz
                          · -- right
                            by_cases h2314 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1401_pos (not_le.mp h2303).le h2311 (not_le.mp h2312).le h2314 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1403_pos (not_le.mp h2303).le h2311 (not_le.mp h2314).le hz2 hz
                        · -- right
                          by_cases h2315 : z ≤ ((1999/2000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2316 : z ≤ ((3997/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1394_pos (not_le.mp h2311).le h2254 hz1 h2316 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1396_pos (not_le.mp h2311).le h2254 (not_le.mp h2316).le h2315 hz
                          · -- right
                            by_cases h2317 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1402_pos (not_le.mp h2311).le h2254 (not_le.mp h2315).le h2317 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1404_pos (not_le.mp h2311).le h2254 (not_le.mp h2317).le hz2 hz
                · -- right
                  by_cases h2318 : a ≤ ((109911/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2319 : a ≤ ((218973/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2320 : a ≤ ((437097/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2321 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2322 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e544_pos (not_le.mp h2254).le h2320 hz1 h2322 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e545_pos (not_le.mp h2254).le h2320 (not_le.mp h2322).le h2321 hz
                        · -- right
                          by_cases h2323 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e548_pos (not_le.mp h2254).le h2320 (not_le.mp h2321).le h2323 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e549_pos (not_le.mp h2254).le h2320 (not_le.mp h2323).le hz2 hz
                      · -- right
                        by_cases h2324 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2325 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e546_pos (not_le.mp h2320).le h2319 hz1 h2325 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e547_pos (not_le.mp h2320).le h2319 (not_le.mp h2325).le h2324 hz
                        · -- right
                          by_cases h2326 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e550_pos (not_le.mp h2320).le h2319 (not_le.mp h2324).le h2326 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e551_pos (not_le.mp h2320).le h2319 (not_le.mp h2326).le hz2 hz
                    · -- right
                      by_cases h2327 : a ≤ ((87759/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2328 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2329 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e552_pos (not_le.mp h2319).le h2327 hz1 h2329 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e553_pos (not_le.mp h2319).le h2327 (not_le.mp h2329).le h2328 hz
                        · -- right
                          by_cases h2330 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e556_pos (not_le.mp h2319).le h2327 (not_le.mp h2328).le h2330 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e557_pos (not_le.mp h2319).le h2327 (not_le.mp h2330).le hz2 hz
                      · -- right
                        by_cases h2331 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2332 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e554_pos (not_le.mp h2327).le h2318 hz1 h2332 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e555_pos (not_le.mp h2327).le h2318 (not_le.mp h2332).le h2331 hz
                        · -- right
                          by_cases h2333 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e558_pos (not_le.mp h2327).le h2318 (not_le.mp h2331).le h2333 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e559_pos (not_le.mp h2327).le h2318 (not_le.mp h2333).le hz2 hz
                  · -- right
                    by_cases h2334 : a ≤ ((220671/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2335 : a ≤ ((440493/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2336 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2337 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e560_pos (not_le.mp h2318).le h2335 hz1 h2337 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e561_pos (not_le.mp h2318).le h2335 (not_le.mp h2337).le h2336 hz
                        · -- right
                          by_cases h2338 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e564_pos (not_le.mp h2318).le h2335 (not_le.mp h2336).le h2338 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e565_pos (not_le.mp h2318).le h2335 (not_le.mp h2338).le hz2 hz
                      · -- right
                        by_cases h2339 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2340 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e562_pos (not_le.mp h2335).le h2334 hz1 h2340 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e563_pos (not_le.mp h2335).le h2334 (not_le.mp h2340).le h2339 hz
                        · -- right
                          by_cases h2341 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e566_pos (not_le.mp h2335).le h2334 (not_le.mp h2339).le h2341 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e567_pos (not_le.mp h2335).le h2334 (not_le.mp h2341).le hz2 hz
                    · -- right
                      by_cases h2342 : a ≤ ((442191/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2343 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2344 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e568_pos (not_le.mp h2334).le h2342 hz1 h2344 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e569_pos (not_le.mp h2334).le h2342 (not_le.mp h2344).le h2343 hz
                        · -- right
                          by_cases h2345 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e572_pos (not_le.mp h2334).le h2342 (not_le.mp h2343).le h2345 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e573_pos (not_le.mp h2334).le h2342 (not_le.mp h2345).le hz2 hz
                      · -- right
                        by_cases h2346 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2347 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e570_pos (not_le.mp h2342).le h2125 hz1 h2347 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e571_pos (not_le.mp h2342).le h2125 (not_le.mp h2347).le h2346 hz
                        · -- right
                          by_cases h2348 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e574_pos (not_le.mp h2342).le h2125 (not_le.mp h2346).le h2348 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e575_pos (not_le.mp h2342).le h2125 (not_le.mp h2348).le hz2 hz
            · -- right
              by_cases h2349 : a ≤ ((28539/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2350 : a ≤ ((56229/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2351 : a ≤ ((111609/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2352 : a ≤ ((222369/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2353 : a ≤ ((443889/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2354 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2355 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e576_pos (not_le.mp h2125).le h2353 hz1 h2355 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e577_pos (not_le.mp h2125).le h2353 (not_le.mp h2355).le h2354 hz
                        · -- right
                          by_cases h2356 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e580_pos (not_le.mp h2125).le h2353 (not_le.mp h2354).le h2356 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e581_pos (not_le.mp h2125).le h2353 (not_le.mp h2356).le hz2 hz
                      · -- right
                        by_cases h2357 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2358 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e578_pos (not_le.mp h2353).le h2352 hz1 h2358 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e579_pos (not_le.mp h2353).le h2352 (not_le.mp h2358).le h2357 hz
                        · -- right
                          by_cases h2359 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e582_pos (not_le.mp h2353).le h2352 (not_le.mp h2357).le h2359 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e583_pos (not_le.mp h2353).le h2352 (not_le.mp h2359).le hz2 hz
                    · -- right
                      by_cases h2360 : a ≤ ((445587/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2361 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e275_pos (not_le.mp h2352).le h2360 hz1 h2361 hz
                        · -- right
                          by_cases h2362 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e584_pos (not_le.mp h2352).le h2360 (not_le.mp h2361).le h2362 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e585_pos (not_le.mp h2352).le h2360 (not_le.mp h2362).le hz2 hz
                      · -- right
                        by_cases h2363 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e276_pos (not_le.mp h2360).le h2351 hz1 h2363 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e277_pos (not_le.mp h2360).le h2351 (not_le.mp h2363).le hz2 hz
                  · -- right
                    by_cases h2364 : a ≤ ((224067/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2365 : a ≤ ((89457/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2366 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e278_pos (not_le.mp h2351).le h2365 hz1 h2366 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e280_pos (not_le.mp h2351).le h2365 (not_le.mp h2366).le hz2 hz
                      · -- right
                        by_cases h2367 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e279_pos (not_le.mp h2365).le h2364 hz1 h2367 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e281_pos (not_le.mp h2365).le h2364 (not_le.mp h2367).le hz2 hz
                    · -- right
                      by_cases h2368 : a ≤ ((448983/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2369 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e282_pos (not_le.mp h2364).le h2368 hz1 h2369 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e284_pos (not_le.mp h2364).le h2368 (not_le.mp h2369).le hz2 hz
                      · -- right
                        by_cases h2370 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e283_pos (not_le.mp h2368).le h2350 hz1 h2370 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e285_pos (not_le.mp h2368).le h2350 (not_le.mp h2370).le hz2 hz
                · -- right
                  by_cases h2371 : a ≤ ((113307/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2372 : a ≤ ((45153/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2373 : a ≤ ((450681/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2374 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e286_pos (not_le.mp h2350).le h2373 hz1 h2374 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e288_pos (not_le.mp h2350).le h2373 (not_le.mp h2374).le hz2 hz
                      · -- right
                        by_cases h2375 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e287_pos (not_le.mp h2373).le h2372 hz1 h2375 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e289_pos (not_le.mp h2373).le h2372 (not_le.mp h2375).le hz2 hz
                    · -- right
                      by_cases h2376 : a ≤ ((452379/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2377 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e290_pos (not_le.mp h2372).le h2376 hz1 h2377 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e292_pos (not_le.mp h2372).le h2376 (not_le.mp h2377).le hz2 hz
                      · -- right
                        by_cases h2378 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e291_pos (not_le.mp h2376).le h2371 hz1 h2378 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e293_pos (not_le.mp h2376).le h2371 (not_le.mp h2378).le hz2 hz
                  · -- right
                    by_cases h2379 : a ≤ ((227463/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2380 : a ≤ ((454077/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2381 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e294_pos (not_le.mp h2371).le h2380 hz1 h2381 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e296_pos (not_le.mp h2371).le h2380 (not_le.mp h2381).le hz2 hz
                      · -- right
                        by_cases h2382 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e295_pos (not_le.mp h2380).le h2379 hz1 h2382 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B004.e297_pos (not_le.mp h2380).le h2379 (not_le.mp h2382).le hz2 hz
                    · -- right
                      by_cases h2383 : a ≤ ((18231/81920 : ℚ) : ℝ)
                      · -- left
                        by_cases h2384 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e298_pos (not_le.mp h2379).le h2383 hz1 h2384 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e300_pos (not_le.mp h2379).le h2383 (not_le.mp h2384).le hz2 hz
                      · -- right
                        by_cases h2385 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B004.e299_pos (not_le.mp h2383).le h2349 hz1 h2385 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e301_pos (not_le.mp h2383).le h2349 (not_le.mp h2385).le hz2 hz
              · -- right
                by_cases h2386 : a ≤ ((57927/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2387 : a ≤ ((23001/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2388 : a ≤ ((229161/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2389 : a ≤ ((457473/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2390 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e302_pos (not_le.mp h2349).le h2389 hz1 h2390 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e304_pos (not_le.mp h2349).le h2389 (not_le.mp h2390).le hz2 hz
                      · -- right
                        by_cases h2391 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e303_pos (not_le.mp h2389).le h2388 hz1 h2391 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e305_pos (not_le.mp h2389).le h2388 (not_le.mp h2391).le hz2 hz
                    · -- right
                      by_cases h2392 : a ≤ ((459171/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2393 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e306_pos (not_le.mp h2388).le h2392 hz1 h2393 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e308_pos (not_le.mp h2388).le h2392 (not_le.mp h2393).le hz2 hz
                      · -- right
                        by_cases h2394 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e307_pos (not_le.mp h2392).le h2387 hz1 h2394 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e309_pos (not_le.mp h2392).le h2387 (not_le.mp h2394).le hz2 hz
                  · -- right
                    by_cases h2395 : a ≤ ((230859/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2396 : a ≤ ((460869/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2397 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e310_pos (not_le.mp h2387).le h2396 hz1 h2397 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e312_pos (not_le.mp h2387).le h2396 (not_le.mp h2397).le hz2 hz
                      · -- right
                        by_cases h2398 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e311_pos (not_le.mp h2396).le h2395 hz1 h2398 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e313_pos (not_le.mp h2396).le h2395 (not_le.mp h2398).le hz2 hz
                    · -- right
                      by_cases h2399 : a ≤ ((462567/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2400 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e314_pos (not_le.mp h2395).le h2399 hz1 h2400 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e316_pos (not_le.mp h2395).le h2399 (not_le.mp h2400).le hz2 hz
                      · -- right
                        by_cases h2401 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e315_pos (not_le.mp h2399).le h2386 hz1 h2401 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e317_pos (not_le.mp h2399).le h2386 (not_le.mp h2401).le hz2 hz
                · -- right
                  by_cases h2402 : a ≤ ((116703/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2403 : a ≤ ((232557/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2404 : a ≤ ((92853/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2405 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e318_pos (not_le.mp h2386).le h2404 hz1 h2405 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e320_pos (not_le.mp h2386).le h2404 (not_le.mp h2405).le hz2 hz
                      · -- right
                        by_cases h2406 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e319_pos (not_le.mp h2404).le h2403 hz1 h2406 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e321_pos (not_le.mp h2404).le h2403 (not_le.mp h2406).le hz2 hz
                    · -- right
                      by_cases h2407 : a ≤ ((465963/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2408 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e322_pos (not_le.mp h2403).le h2407 hz1 h2408 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e324_pos (not_le.mp h2403).le h2407 (not_le.mp h2408).le hz2 hz
                      · -- right
                        by_cases h2409 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e323_pos (not_le.mp h2407).le h2402 hz1 h2409 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e325_pos (not_le.mp h2407).le h2402 (not_le.mp h2409).le hz2 hz
                  · -- right
                    by_cases h2410 : a ≤ ((46851/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2411 : a ≤ ((467661/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2412 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e326_pos (not_le.mp h2402).le h2411 hz1 h2412 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e328_pos (not_le.mp h2402).le h2411 (not_le.mp h2412).le hz2 hz
                      · -- right
                        by_cases h2413 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e327_pos (not_le.mp h2411).le h2410 hz1 h2413 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e329_pos (not_le.mp h2411).le h2410 (not_le.mp h2413).le hz2 hz
                    · -- right
                      by_cases h2414 : a ≤ ((469359/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2415 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e330_pos (not_le.mp h2410).le h2414 hz1 h2415 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e332_pos (not_le.mp h2410).le h2414 (not_le.mp h2415).le hz2 hz
                      · -- right
                        by_cases h2416 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e331_pos (not_le.mp h2414).le h2124 hz1 h2416 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e333_pos (not_le.mp h2414).le h2124 (not_le.mp h2416).le hz2 hz
          · -- right
            by_cases h2417 : a ≤ ((15543/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2418 : a ≤ ((30237/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2419 : a ≤ ((477/2048 : ℚ) : ℝ)
                · -- left
                  by_cases h2420 : a ≤ ((118401/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2421 : a ≤ ((235953/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2422 : a ≤ ((471057/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2423 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e334_pos (not_le.mp h2124).le h2422 hz1 h2423 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e336_pos (not_le.mp h2124).le h2422 (not_le.mp h2423).le hz2 hz
                      · -- right
                        by_cases h2424 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e335_pos (not_le.mp h2422).le h2421 hz1 h2424 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e337_pos (not_le.mp h2422).le h2421 (not_le.mp h2424).le hz2 hz
                    · -- right
                      by_cases h2425 : a ≤ ((94551/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2426 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e338_pos (not_le.mp h2421).le h2425 hz1 h2426 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e340_pos (not_le.mp h2421).le h2425 (not_le.mp h2426).le hz2 hz
                      · -- right
                        by_cases h2427 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e339_pos (not_le.mp h2425).le h2420 hz1 h2427 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e341_pos (not_le.mp h2425).le h2420 (not_le.mp h2427).le hz2 hz
                  · -- right
                    by_cases h2428 : a ≤ ((237651/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2429 : a ≤ ((474453/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2430 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e342_pos (not_le.mp h2420).le h2429 hz1 h2430 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e344_pos (not_le.mp h2420).le h2429 (not_le.mp h2430).le hz2 hz
                      · -- right
                        by_cases h2431 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e343_pos (not_le.mp h2429).le h2428 hz1 h2431 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e345_pos (not_le.mp h2429).le h2428 (not_le.mp h2431).le hz2 hz
                    · -- right
                      by_cases h2432 : a ≤ ((476151/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2433 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e346_pos (not_le.mp h2428).le h2432 hz1 h2433 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e348_pos (not_le.mp h2428).le h2432 (not_le.mp h2433).le hz2 hz
                      · -- right
                        by_cases h2434 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e347_pos (not_le.mp h2432).le h2419 hz1 h2434 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e349_pos (not_le.mp h2432).le h2419 (not_le.mp h2434).le hz2 hz
                · -- right
                  by_cases h2435 : a ≤ ((120099/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2436 : a ≤ ((239349/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2437 : a ≤ ((477849/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2438 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e350_pos (not_le.mp h2419).le h2437 hz1 h2438 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e352_pos (not_le.mp h2419).le h2437 (not_le.mp h2438).le hz2 hz
                      · -- right
                        by_cases h2439 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e351_pos (not_le.mp h2437).le h2436 hz1 h2439 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e353_pos (not_le.mp h2437).le h2436 (not_le.mp h2439).le hz2 hz
                    · -- right
                      by_cases h2440 : a ≤ ((479547/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2441 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e354_pos (not_le.mp h2436).le h2440 hz1 h2441 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e356_pos (not_le.mp h2436).le h2440 (not_le.mp h2441).le hz2 hz
                      · -- right
                        by_cases h2442 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e355_pos (not_le.mp h2440).le h2435 hz1 h2442 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B005.e357_pos (not_le.mp h2440).le h2435 (not_le.mp h2442).le hz2 hz
                  · -- right
                    by_cases h2443 : a ≤ ((241047/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2444 : a ≤ ((96249/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2445 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e358_pos (not_le.mp h2435).le h2444 hz1 h2445 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e360_pos (not_le.mp h2435).le h2444 (not_le.mp h2445).le hz2 hz
                      · -- right
                        by_cases h2446 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B005.e359_pos (not_le.mp h2444).le h2443 hz1 h2446 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e361_pos (not_le.mp h2444).le h2443 (not_le.mp h2446).le hz2 hz
                    · -- right
                      by_cases h2447 : a ≤ ((482943/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2448 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e362_pos (not_le.mp h2443).le h2447 hz1 h2448 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e364_pos (not_le.mp h2443).le h2447 (not_le.mp h2448).le hz2 hz
                      · -- right
                        by_cases h2449 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e363_pos (not_le.mp h2447).le h2418 hz1 h2449 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e365_pos (not_le.mp h2447).le h2418 (not_le.mp h2449).le hz2 hz
              · -- right
                by_cases h2450 : a ≤ ((61323/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2451 : a ≤ ((121797/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2452 : a ≤ ((48549/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2453 : a ≤ ((484641/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2454 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e366_pos (not_le.mp h2418).le h2453 hz1 h2454 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e368_pos (not_le.mp h2418).le h2453 (not_le.mp h2454).le hz2 hz
                      · -- right
                        by_cases h2455 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e367_pos (not_le.mp h2453).le h2452 hz1 h2455 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e369_pos (not_le.mp h2453).le h2452 (not_le.mp h2455).le hz2 hz
                    · -- right
                      by_cases h2456 : a ≤ ((486339/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2457 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e370_pos (not_le.mp h2452).le h2456 hz1 h2457 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e372_pos (not_le.mp h2452).le h2456 (not_le.mp h2457).le hz2 hz
                      · -- right
                        by_cases h2458 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e371_pos (not_le.mp h2456).le h2451 hz1 h2458 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e373_pos (not_le.mp h2456).le h2451 (not_le.mp h2458).le hz2 hz
                  · -- right
                    by_cases h2459 : a ≤ ((244443/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2460 : a ≤ ((488037/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2461 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e374_pos (not_le.mp h2451).le h2460 hz1 h2461 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e376_pos (not_le.mp h2451).le h2460 (not_le.mp h2461).le hz2 hz
                      · -- right
                        by_cases h2462 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e375_pos (not_le.mp h2460).le h2459 hz1 h2462 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e377_pos (not_le.mp h2460).le h2459 (not_le.mp h2462).le hz2 hz
                    · -- right
                      by_cases h2463 : a ≤ ((97947/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2464 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e378_pos (not_le.mp h2459).le h2463 hz1 h2464 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e380_pos (not_le.mp h2459).le h2463 (not_le.mp h2464).le hz2 hz
                      · -- right
                        by_cases h2465 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e379_pos (not_le.mp h2463).le h2450 hz1 h2465 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e381_pos (not_le.mp h2463).le h2450 (not_le.mp h2465).le hz2 hz
                · -- right
                  by_cases h2466 : a ≤ ((24699/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2467 : a ≤ ((246141/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2468 : a ≤ ((491433/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2469 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e382_pos (not_le.mp h2450).le h2468 hz1 h2469 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e384_pos (not_le.mp h2450).le h2468 (not_le.mp h2469).le hz2 hz
                      · -- right
                        by_cases h2470 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e383_pos (not_le.mp h2468).le h2467 hz1 h2470 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e385_pos (not_le.mp h2468).le h2467 (not_le.mp h2470).le hz2 hz
                    · -- right
                      by_cases h2471 : a ≤ ((493131/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2472 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e386_pos (not_le.mp h2467).le h2471 hz1 h2472 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e388_pos (not_le.mp h2467).le h2471 (not_le.mp h2472).le hz2 hz
                      · -- right
                        by_cases h2473 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e387_pos (not_le.mp h2471).le h2466 hz1 h2473 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e389_pos (not_le.mp h2471).le h2466 (not_le.mp h2473).le hz2 hz
                  · -- right
                    by_cases h2474 : a ≤ ((247839/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2475 : a ≤ ((494829/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2476 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e390_pos (not_le.mp h2466).le h2475 hz1 h2476 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e392_pos (not_le.mp h2466).le h2475 (not_le.mp h2476).le hz2 hz
                      · -- right
                        by_cases h2477 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e391_pos (not_le.mp h2475).le h2474 hz1 h2477 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e393_pos (not_le.mp h2475).le h2474 (not_le.mp h2477).le hz2 hz
                    · -- right
                      by_cases h2478 : a ≤ ((496527/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2479 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e394_pos (not_le.mp h2474).le h2478 hz1 h2479 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e396_pos (not_le.mp h2474).le h2478 (not_le.mp h2479).le hz2 hz
                      · -- right
                        by_cases h2480 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e395_pos (not_le.mp h2478).le h2417 hz1 h2480 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e397_pos (not_le.mp h2478).le h2417 (not_le.mp h2480).le hz2 hz
            · -- right
              by_cases h2481 : a ≤ ((6387/25600 : ℚ) : ℝ)
              · -- left
                by_cases h2482 : a ≤ ((63021/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2483 : a ≤ ((125193/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2484 : a ≤ ((249537/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2485 : a ≤ ((19929/81920 : ℚ) : ℝ)
                      · -- left
                        by_cases h2486 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e398_pos (not_le.mp h2417).le h2485 hz1 h2486 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e400_pos (not_le.mp h2417).le h2485 (not_le.mp h2486).le hz2 hz
                      · -- right
                        by_cases h2487 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e399_pos (not_le.mp h2485).le h2484 hz1 h2487 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e401_pos (not_le.mp h2485).le h2484 (not_le.mp h2487).le hz2 hz
                    · -- right
                      by_cases h2488 : a ≤ ((499923/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2489 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e402_pos (not_le.mp h2484).le h2488 hz1 h2489 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e404_pos (not_le.mp h2484).le h2488 (not_le.mp h2489).le hz2 hz
                      · -- right
                        by_cases h2490 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e403_pos (not_le.mp h2488).le h2483 hz1 h2490 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e405_pos (not_le.mp h2488).le h2483 (not_le.mp h2490).le hz2 hz
                  · -- right
                    by_cases h2491 : a ≤ ((50247/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2492 : a ≤ ((501621/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2493 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e406_pos (not_le.mp h2483).le h2492 hz1 h2493 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e408_pos (not_le.mp h2483).le h2492 (not_le.mp h2493).le hz2 hz
                      · -- right
                        by_cases h2494 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e407_pos (not_le.mp h2492).le h2491 hz1 h2494 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e409_pos (not_le.mp h2492).le h2491 (not_le.mp h2494).le hz2 hz
                    · -- right
                      by_cases h2495 : a ≤ ((503319/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2496 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e410_pos (not_le.mp h2491).le h2495 hz1 h2496 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e412_pos (not_le.mp h2491).le h2495 (not_le.mp h2496).le hz2 hz
                      · -- right
                        by_cases h2497 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e411_pos (not_le.mp h2495).le h2482 hz1 h2497 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e413_pos (not_le.mp h2495).le h2482 (not_le.mp h2497).le hz2 hz
                · -- right
                  by_cases h2498 : a ≤ ((126891/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2499 : a ≤ ((252933/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2500 : a ≤ ((505017/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2501 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e414_pos (not_le.mp h2482).le h2500 hz1 h2501 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e416_pos (not_le.mp h2482).le h2500 (not_le.mp h2501).le hz2 hz
                      · -- right
                        by_cases h2502 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e415_pos (not_le.mp h2500).le h2499 hz1 h2502 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B006.e417_pos (not_le.mp h2500).le h2499 (not_le.mp h2502).le hz2 hz
                    · -- right
                      by_cases h2503 : a ≤ ((101343/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2504 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e418_pos (not_le.mp h2499).le h2503 hz1 h2504 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e420_pos (not_le.mp h2499).le h2503 (not_le.mp h2504).le hz2 hz
                      · -- right
                        by_cases h2505 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B006.e419_pos (not_le.mp h2503).le h2498 hz1 h2505 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e421_pos (not_le.mp h2503).le h2498 (not_le.mp h2505).le hz2 hz
                  · -- right
                    by_cases h2506 : a ≤ ((254631/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2507 : a ≤ ((508413/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2508 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e422_pos (not_le.mp h2498).le h2507 hz1 h2508 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e424_pos (not_le.mp h2498).le h2507 (not_le.mp h2508).le hz2 hz
                      · -- right
                        by_cases h2509 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e423_pos (not_le.mp h2507).le h2506 hz1 h2509 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e425_pos (not_le.mp h2507).le h2506 (not_le.mp h2509).le hz2 hz
                    · -- right
                      by_cases h2510 : a ≤ ((510111/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2511 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e426_pos (not_le.mp h2506).le h2510 hz1 h2511 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e428_pos (not_le.mp h2506).le h2510 (not_le.mp h2511).le hz2 hz
                      · -- right
                        by_cases h2512 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e427_pos (not_le.mp h2510).le h2481 hz1 h2512 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e429_pos (not_le.mp h2510).le h2481 (not_le.mp h2512).le hz2 hz
              · -- right
                by_cases h2513 : a ≤ ((64719/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2514 : a ≤ ((128589/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2515 : a ≤ ((256329/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2516 : a ≤ ((511809/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2517 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e430_pos (not_le.mp h2481).le h2516 hz1 h2517 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e432_pos (not_le.mp h2481).le h2516 (not_le.mp h2517).le hz2 hz
                      · -- right
                        by_cases h2518 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e431_pos (not_le.mp h2516).le h2515 hz1 h2518 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e433_pos (not_le.mp h2516).le h2515 (not_le.mp h2518).le hz2 hz
                    · -- right
                      by_cases h2519 : a ≤ ((513507/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2520 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e434_pos (not_le.mp h2515).le h2519 hz1 h2520 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e436_pos (not_le.mp h2515).le h2519 (not_le.mp h2520).le hz2 hz
                      · -- right
                        by_cases h2521 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e435_pos (not_le.mp h2519).le h2514 hz1 h2521 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e437_pos (not_le.mp h2519).le h2514 (not_le.mp h2521).le hz2 hz
                  · -- right
                    by_cases h2522 : a ≤ ((258027/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2523 : a ≤ ((103041/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2524 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e438_pos (not_le.mp h2514).le h2523 hz1 h2524 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e440_pos (not_le.mp h2514).le h2523 (not_le.mp h2524).le hz2 hz
                      · -- right
                        by_cases h2525 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e439_pos (not_le.mp h2523).le h2522 hz1 h2525 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e441_pos (not_le.mp h2523).le h2522 (not_le.mp h2525).le hz2 hz
                    · -- right
                      by_cases h2526 : a ≤ ((516903/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2527 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e442_pos (not_le.mp h2522).le h2526 hz1 h2527 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e444_pos (not_le.mp h2522).le h2526 (not_le.mp h2527).le hz2 hz
                      · -- right
                        by_cases h2528 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e443_pos (not_le.mp h2526).le h2513 hz1 h2528 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e445_pos (not_le.mp h2526).le h2513 (not_le.mp h2528).le hz2 hz
                · -- right
                  by_cases h2529 : a ≤ ((130287/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2530 : a ≤ ((10389/40960 : ℚ) : ℝ)
                    · -- left
                      by_cases h2531 : a ≤ ((518601/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2532 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e446_pos (not_le.mp h2513).le h2531 hz1 h2532 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e448_pos (not_le.mp h2513).le h2531 (not_le.mp h2532).le hz2 hz
                      · -- right
                        by_cases h2533 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e447_pos (not_le.mp h2531).le h2530 hz1 h2533 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e449_pos (not_le.mp h2531).le h2530 (not_le.mp h2533).le hz2 hz
                    · -- right
                      by_cases h2534 : a ≤ ((520299/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2535 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e450_pos (not_le.mp h2530).le h2534 hz1 h2535 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e452_pos (not_le.mp h2530).le h2534 (not_le.mp h2535).le hz2 hz
                      · -- right
                        by_cases h2536 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e451_pos (not_le.mp h2534).le h2529 hz1 h2536 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e453_pos (not_le.mp h2534).le h2529 (not_le.mp h2536).le hz2 hz
                  · -- right
                    by_cases h2537 : a ≤ ((261423/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2538 : a ≤ ((521997/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2539 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e454_pos (not_le.mp h2529).le h2538 hz1 h2539 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e456_pos (not_le.mp h2529).le h2538 (not_le.mp h2539).le hz2 hz
                      · -- right
                        by_cases h2540 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e455_pos (not_le.mp h2538).le h2537 hz1 h2540 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e457_pos (not_le.mp h2538).le h2537 (not_le.mp h2540).le hz2 hz
                    · -- right
                      by_cases h2541 : a ≤ ((104739/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2542 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e458_pos (not_le.mp h2537).le h2541 hz1 h2542 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e460_pos (not_le.mp h2537).le h2541 (not_le.mp h2542).le hz2 hz
                      · -- right
                        by_cases h2543 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e459_pos (not_le.mp h2541).le h2 hz1 h2543 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e461_pos (not_le.mp h2541).le h2 (not_le.mp h2543).le hz2 hz
      · -- right
        by_cases h2544 : a ≤ ((4947/16000 : ℚ) : ℝ)
        · -- left
          by_cases h2545 : a ≤ ((1809/6400 : ℚ) : ℝ)
          · -- left
            by_cases h2546 : a ≤ ((17241/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2547 : a ≤ ((33633/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2548 : a ≤ ((66417/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2549 : a ≤ ((26397/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2550 : a ≤ ((263121/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2551 : a ≤ ((525393/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2552 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e462_pos (not_le.mp h2).le h2551 hz1 h2552 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e464_pos (not_le.mp h2).le h2551 (not_le.mp h2552).le hz2 hz
                      · -- right
                        by_cases h2553 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e463_pos (not_le.mp h2551).le h2550 hz1 h2553 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e465_pos (not_le.mp h2551).le h2550 (not_le.mp h2553).le hz2 hz
                    · -- right
                      by_cases h2554 : a ≤ ((527091/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2555 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e466_pos (not_le.mp h2550).le h2554 hz1 h2555 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e468_pos (not_le.mp h2550).le h2554 (not_le.mp h2555).le hz2 hz
                      · -- right
                        by_cases h2556 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e467_pos (not_le.mp h2554).le h2549 hz1 h2556 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e469_pos (not_le.mp h2554).le h2549 (not_le.mp h2556).le hz2 hz
                  · -- right
                    by_cases h2557 : a ≤ ((264819/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2558 : a ≤ ((528789/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2559 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e470_pos (not_le.mp h2549).le h2558 hz1 h2559 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e472_pos (not_le.mp h2549).le h2558 (not_le.mp h2559).le hz2 hz
                      · -- right
                        by_cases h2560 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e471_pos (not_le.mp h2558).le h2557 hz1 h2560 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e473_pos (not_le.mp h2558).le h2557 (not_le.mp h2560).le hz2 hz
                    · -- right
                      by_cases h2561 : a ≤ ((530487/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2562 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e474_pos (not_le.mp h2557).le h2561 hz1 h2562 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e476_pos (not_le.mp h2557).le h2561 (not_le.mp h2562).le hz2 hz
                      · -- right
                        by_cases h2563 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e475_pos (not_le.mp h2561).le h2548 hz1 h2563 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B007.e477_pos (not_le.mp h2561).le h2548 (not_le.mp h2563).le hz2 hz
                · -- right
                  by_cases h2564 : a ≤ ((133683/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2565 : a ≤ ((266517/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2566 : a ≤ ((106437/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2567 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e478_pos (not_le.mp h2548).le h2566 hz1 h2567 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e480_pos (not_le.mp h2548).le h2566 (not_le.mp h2567).le hz2 hz
                      · -- right
                        by_cases h2568 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B007.e479_pos (not_le.mp h2566).le h2565 hz1 h2568 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e481_pos (not_le.mp h2566).le h2565 (not_le.mp h2568).le hz2 hz
                    · -- right
                      by_cases h2569 : a ≤ ((533883/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2570 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e482_pos (not_le.mp h2565).le h2569 hz1 h2570 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e484_pos (not_le.mp h2565).le h2569 (not_le.mp h2570).le hz2 hz
                      · -- right
                        by_cases h2571 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e483_pos (not_le.mp h2569).le h2564 hz1 h2571 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e485_pos (not_le.mp h2569).le h2564 (not_le.mp h2571).le hz2 hz
                  · -- right
                    by_cases h2572 : a ≤ ((53643/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2573 : a ≤ ((535581/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2574 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e486_pos (not_le.mp h2564).le h2573 hz1 h2574 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e488_pos (not_le.mp h2564).le h2573 (not_le.mp h2574).le hz2 hz
                      · -- right
                        by_cases h2575 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e487_pos (not_le.mp h2573).le h2572 hz1 h2575 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e489_pos (not_le.mp h2573).le h2572 (not_le.mp h2575).le hz2 hz
                    · -- right
                      by_cases h2576 : a ≤ ((537279/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2577 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e490_pos (not_le.mp h2572).le h2576 hz1 h2577 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e492_pos (not_le.mp h2572).le h2576 (not_le.mp h2577).le hz2 hz
                      · -- right
                        by_cases h2578 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e491_pos (not_le.mp h2576).le h2547 hz1 h2578 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e493_pos (not_le.mp h2576).le h2547 (not_le.mp h2578).le hz2 hz
              · -- right
                by_cases h2579 : a ≤ ((13623/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2580 : a ≤ ((135381/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2581 : a ≤ ((269913/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2582 : a ≤ ((538977/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2583 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e494_pos (not_le.mp h2547).le h2582 hz1 h2583 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e496_pos (not_le.mp h2547).le h2582 (not_le.mp h2583).le hz2 hz
                      · -- right
                        by_cases h2584 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e495_pos (not_le.mp h2582).le h2581 hz1 h2584 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e497_pos (not_le.mp h2582).le h2581 (not_le.mp h2584).le hz2 hz
                    · -- right
                      by_cases h2585 : a ≤ ((21627/81920 : ℚ) : ℝ)
                      · -- left
                        by_cases h2586 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e498_pos (not_le.mp h2581).le h2585 hz1 h2586 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e500_pos (not_le.mp h2581).le h2585 (not_le.mp h2586).le hz2 hz
                      · -- right
                        by_cases h2587 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e499_pos (not_le.mp h2585).le h2580 hz1 h2587 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e501_pos (not_le.mp h2585).le h2580 (not_le.mp h2587).le hz2 hz
                  · -- right
                    by_cases h2588 : a ≤ ((271611/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2589 : a ≤ ((542373/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2590 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e502_pos (not_le.mp h2580).le h2589 hz1 h2590 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e504_pos (not_le.mp h2580).le h2589 (not_le.mp h2590).le hz2 hz
                      · -- right
                        by_cases h2591 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e503_pos (not_le.mp h2589).le h2588 hz1 h2591 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e505_pos (not_le.mp h2589).le h2588 (not_le.mp h2591).le hz2 hz
                    · -- right
                      by_cases h2592 : a ≤ ((544071/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2593 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e506_pos (not_le.mp h2588).le h2592 hz1 h2593 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e508_pos (not_le.mp h2588).le h2592 (not_le.mp h2593).le hz2 hz
                      · -- right
                        by_cases h2594 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e507_pos (not_le.mp h2592).le h2579 hz1 h2594 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e509_pos (not_le.mp h2592).le h2579 (not_le.mp h2594).le hz2 hz
                · -- right
                  by_cases h2595 : a ≤ ((137079/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2596 : a ≤ ((273309/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2597 : a ≤ ((545769/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2598 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e510_pos (not_le.mp h2579).le h2597 hz1 h2598 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e512_pos (not_le.mp h2579).le h2597 (not_le.mp h2598).le hz2 hz
                      · -- right
                        by_cases h2599 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e511_pos (not_le.mp h2597).le h2596 hz1 h2599 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e513_pos (not_le.mp h2597).le h2596 (not_le.mp h2599).le hz2 hz
                    · -- right
                      by_cases h2600 : a ≤ ((547467/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2601 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e514_pos (not_le.mp h2596).le h2600 hz1 h2601 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e516_pos (not_le.mp h2596).le h2600 (not_le.mp h2601).le hz2 hz
                      · -- right
                        by_cases h2602 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e515_pos (not_le.mp h2600).le h2595 hz1 h2602 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e517_pos (not_le.mp h2600).le h2595 (not_le.mp h2602).le hz2 hz
                  · -- right
                    by_cases h2603 : a ≤ ((275007/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2604 : a ≤ ((109833/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2605 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e518_pos (not_le.mp h2595).le h2604 hz1 h2605 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e520_pos (not_le.mp h2595).le h2604 (not_le.mp h2605).le hz2 hz
                      · -- right
                        by_cases h2606 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e519_pos (not_le.mp h2604).le h2603 hz1 h2606 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e521_pos (not_le.mp h2604).le h2603 (not_le.mp h2606).le hz2 hz
                    · -- right
                      by_cases h2607 : a ≤ ((550863/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2608 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e522_pos (not_le.mp h2603).le h2607 hz1 h2608 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e524_pos (not_le.mp h2603).le h2607 (not_le.mp h2608).le hz2 hz
                      · -- right
                        by_cases h2609 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e523_pos (not_le.mp h2607).le h2546 hz1 h2609 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e525_pos (not_le.mp h2607).le h2546 (not_le.mp h2609).le hz2 hz
            · -- right
              by_cases h2610 : a ≤ ((35331/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2611 : a ≤ ((69813/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2612 : a ≤ ((138777/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2613 : a ≤ ((55341/204800 : ℚ) : ℝ)
                    · -- left
                      by_cases h2614 : a ≤ ((552561/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2615 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e526_pos (not_le.mp h2546).le h2614 hz1 h2615 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e528_pos (not_le.mp h2546).le h2614 (not_le.mp h2615).le hz2 hz
                      · -- right
                        by_cases h2616 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e527_pos (not_le.mp h2614).le h2613 hz1 h2616 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e529_pos (not_le.mp h2614).le h2613 (not_le.mp h2616).le hz2 hz
                    · -- right
                      by_cases h2617 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e255_pos (not_le.mp h2613).le h2612 hz1 h2617 hz
                      · -- right
                        by_cases h2618 : a ≤ ((554259/2048000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e530_pos (not_le.mp h2613).le h2618 (not_le.mp h2617).le hz2 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e531_pos (not_le.mp h2618).le h2612 (not_le.mp h2617).le hz2 hz
                  · -- right
                    by_cases h2619 : a ≤ ((278403/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2620 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e256_pos (not_le.mp h2612).le h2619 hz1 h2620 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e257_pos (not_le.mp h2612).le h2619 (not_le.mp h2620).le hz2 hz
                    · -- right
                      by_cases h2621 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e258_pos (not_le.mp h2619).le h2611 hz1 h2621 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e259_pos (not_le.mp h2619).le h2611 (not_le.mp h2621).le hz2 hz
                · -- right
                  by_cases h2622 : a ≤ ((5619/20480 : ℚ) : ℝ)
                  · -- left
                    by_cases h2623 : a ≤ ((280101/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2624 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e260_pos (not_le.mp h2611).le h2623 hz1 h2624 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e261_pos (not_le.mp h2611).le h2623 (not_le.mp h2624).le hz2 hz
                    · -- right
                      by_cases h2625 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e262_pos (not_le.mp h2623).le h2622 hz1 h2625 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e263_pos (not_le.mp h2623).le h2622 (not_le.mp h2625).le hz2 hz
                  · -- right
                    by_cases h2626 : a ≤ ((281799/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2627 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e264_pos (not_le.mp h2622).le h2626 hz1 h2627 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e265_pos (not_le.mp h2622).le h2626 (not_le.mp h2627).le hz2 hz
                    · -- right
                      by_cases h2628 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e266_pos (not_le.mp h2626).le h2610 hz1 h2628 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e267_pos (not_le.mp h2626).le h2610 (not_le.mp h2628).le hz2 hz
              · -- right
                by_cases h2629 : a ≤ ((71511/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2630 : a ≤ ((142173/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2631 : a ≤ ((283497/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2632 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e268_pos (not_le.mp h2610).le h2631 hz1 h2632 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e269_pos (not_le.mp h2610).le h2631 (not_le.mp h2632).le hz2 hz
                    · -- right
                      by_cases h2633 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e270_pos (not_le.mp h2631).le h2630 hz1 h2633 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e271_pos (not_le.mp h2631).le h2630 (not_le.mp h2633).le hz2 hz
                  · -- right
                    by_cases h2634 : a ≤ ((57039/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e167_pos (not_le.mp h2630).le h2634 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e168_pos (not_le.mp h2634).le h2629 hz1 hz2 hz
                · -- right
                  by_cases h2635 : a ≤ ((143871/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2636 : a ≤ ((286893/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e169_pos (not_le.mp h2629).le h2636 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e170_pos (not_le.mp h2636).le h2635 hz1 hz2 hz
                  · -- right
                    by_cases h2637 : a ≤ ((288591/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e171_pos (not_le.mp h2635).le h2637 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e172_pos (not_le.mp h2637).le h2545 hz1 hz2 hz
          · -- right
            by_cases h2638 : a ≤ ((18939/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2639 : a ≤ ((37029/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2640 : a ≤ ((73209/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2641 : a ≤ ((145569/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2642 : a ≤ ((290289/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e173_pos (not_le.mp h2545).le h2642 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e174_pos (not_le.mp h2642).le h2641 hz1 hz2 hz
                  · -- right
                    by_cases h2643 : a ≤ ((291987/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e175_pos (not_le.mp h2641).le h2643 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e176_pos (not_le.mp h2643).le h2640 hz1 hz2 hz
                · -- right
                  by_cases h2644 : a ≤ ((147267/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2645 : a ≤ ((58737/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e177_pos (not_le.mp h2640).le h2645 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B002.e178_pos (not_le.mp h2645).le h2644 hz1 hz2 hz
                  · -- right
                    by_cases h2646 : a ≤ ((295383/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B002.e179_pos (not_le.mp h2644).le h2646 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e180_pos (not_le.mp h2646).le h2639 hz1 hz2 hz
              · -- right
                by_cases h2647 : a ≤ ((74907/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2648 : a ≤ ((29793/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2649 : a ≤ ((297081/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e181_pos (not_le.mp h2639).le h2649 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e182_pos (not_le.mp h2649).le h2648 hz1 hz2 hz
                  · -- right
                    by_cases h2650 : a ≤ ((298779/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e183_pos (not_le.mp h2648).le h2650 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e184_pos (not_le.mp h2650).le h2647 hz1 hz2 hz
                · -- right
                  by_cases h2651 : a ≤ ((150663/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2652 : a ≤ ((300477/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e185_pos (not_le.mp h2647).le h2652 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e186_pos (not_le.mp h2652).le h2651 hz1 hz2 hz
                  · -- right
                    by_cases h2653 : a ≤ ((12087/40960 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e187_pos (not_le.mp h2651).le h2653 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e188_pos (not_le.mp h2653).le h2638 hz1 hz2 hz
            · -- right
              by_cases h2654 : a ≤ ((38727/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2655 : a ≤ ((15321/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2656 : a ≤ ((152361/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2657 : a ≤ ((303873/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e189_pos (not_le.mp h2638).le h2657 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e190_pos (not_le.mp h2657).le h2656 hz1 hz2 hz
                  · -- right
                    by_cases h2658 : a ≤ ((305571/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e191_pos (not_le.mp h2656).le h2658 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e192_pos (not_le.mp h2658).le h2655 hz1 hz2 hz
                · -- right
                  by_cases h2659 : a ≤ ((154059/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2660 : a ≤ ((307269/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e193_pos (not_le.mp h2655).le h2660 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e194_pos (not_le.mp h2660).le h2659 hz1 hz2 hz
                  · -- right
                    by_cases h2661 : a ≤ ((308967/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e195_pos (not_le.mp h2659).le h2661 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e196_pos (not_le.mp h2661).le h2654 hz1 hz2 hz
              · -- right
                by_cases h2662 : a ≤ ((78303/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2663 : a ≤ ((155757/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2664 : a ≤ ((62133/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e197_pos (not_le.mp h2654).le h2664 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e198_pos (not_le.mp h2664).le h2663 hz1 hz2 hz
                  · -- right
                    by_cases h2665 : a ≤ ((312363/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e199_pos (not_le.mp h2663).le h2665 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e200_pos (not_le.mp h2665).le h2662 hz1 hz2 hz
                · -- right
                  by_cases h2666 : a ≤ ((31491/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2667 : a ≤ ((314061/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e201_pos (not_le.mp h2662).le h2667 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e202_pos (not_le.mp h2667).le h2666 hz1 hz2 hz
                  · -- right
                    by_cases h2668 : a ≤ ((315759/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e203_pos (not_le.mp h2666).le h2668 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e204_pos (not_le.mp h2668).le h2544 hz1 hz2 hz
        · -- right
          by_cases h2669 : a ≤ ((10743/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2670 : a ≤ ((20637/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2671 : a ≤ ((1617/5120 : ℚ) : ℝ)
              · -- left
                by_cases h2672 : a ≤ ((80001/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2673 : a ≤ ((159153/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2674 : a ≤ ((317457/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e205_pos (not_le.mp h2544).le h2674 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e206_pos (not_le.mp h2674).le h2673 hz1 hz2 hz
                  · -- right
                    by_cases h2675 : a ≤ ((63831/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e207_pos (not_le.mp h2673).le h2675 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e208_pos (not_le.mp h2675).le h2672 hz1 hz2 hz
                · -- right
                  by_cases h2676 : a ≤ ((160851/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2677 : a ≤ ((320853/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e209_pos (not_le.mp h2672).le h2677 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e210_pos (not_le.mp h2677).le h2676 hz1 hz2 hz
                  · -- right
                    by_cases h2678 : a ≤ ((322551/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e211_pos (not_le.mp h2676).le h2678 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e212_pos (not_le.mp h2678).le h2671 hz1 hz2 hz
              · -- right
                by_cases h2679 : a ≤ ((81699/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2680 : a ≤ ((162549/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2681 : a ≤ ((324249/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e213_pos (not_le.mp h2671).le h2681 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e214_pos (not_le.mp h2681).le h2680 hz1 hz2 hz
                  · -- right
                    by_cases h2682 : a ≤ ((325947/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e215_pos (not_le.mp h2680).le h2682 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e216_pos (not_le.mp h2682).le h2679 hz1 hz2 hz
                · -- right
                  by_cases h2683 : a ≤ ((164247/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2684 : a ≤ ((65529/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e217_pos (not_le.mp h2679).le h2684 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e218_pos (not_le.mp h2684).le h2683 hz1 hz2 hz
                  · -- right
                    by_cases h2685 : a ≤ ((329343/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e219_pos (not_le.mp h2683).le h2685 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e220_pos (not_le.mp h2685).le h2670 hz1 hz2 hz
            · -- right
              by_cases h2686 : a ≤ ((42123/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2687 : a ≤ ((83397/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2688 : a ≤ ((33189/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2689 : a ≤ ((331041/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e221_pos (not_le.mp h2670).le h2689 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e222_pos (not_le.mp h2689).le h2688 hz1 hz2 hz
                  · -- right
                    by_cases h2690 : a ≤ ((332739/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e223_pos (not_le.mp h2688).le h2690 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e224_pos (not_le.mp h2690).le h2687 hz1 hz2 hz
                · -- right
                  by_cases h2691 : a ≤ ((167643/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2692 : a ≤ ((334437/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e225_pos (not_le.mp h2687).le h2692 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e226_pos (not_le.mp h2692).le h2691 hz1 hz2 hz
                  · -- right
                    by_cases h2693 : a ≤ ((67227/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e227_pos (not_le.mp h2691).le h2693 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e228_pos (not_le.mp h2693).le h2686 hz1 hz2 hz
              · -- right
                by_cases h2694 : a ≤ ((17019/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2695 : a ≤ ((169341/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2696 : a ≤ ((337833/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e229_pos (not_le.mp h2686).le h2696 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e230_pos (not_le.mp h2696).le h2695 hz1 hz2 hz
                  · -- right
                    by_cases h2697 : a ≤ ((339531/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e231_pos (not_le.mp h2695).le h2697 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e232_pos (not_le.mp h2697).le h2694 hz1 hz2 hz
                · -- right
                  by_cases h2698 : a ≤ ((171039/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2699 : a ≤ ((341229/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e233_pos (not_le.mp h2694).le h2699 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e234_pos (not_le.mp h2699).le h2698 hz1 hz2 hz
                  · -- right
                    by_cases h2700 : a ≤ ((342927/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e235_pos (not_le.mp h2698).le h2700 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e236_pos (not_le.mp h2700).le h2669 hz1 hz2 hz
          · -- right
            by_cases h2701 : a ≤ ((4467/12800 : ℚ) : ℝ)
            · -- left
              by_cases h2702 : a ≤ ((43821/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2703 : a ≤ ((86793/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2704 : a ≤ ((172737/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2705 : a ≤ ((2757/8192 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e237_pos (not_le.mp h2669).le h2705 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B003.e238_pos (not_le.mp h2705).le h2704 hz1 hz2 hz
                  · -- right
                    by_cases h2706 : a ≤ ((346323/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B003.e239_pos (not_le.mp h2704).le h2706 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e240_pos (not_le.mp h2706).le h2703 hz1 hz2 hz
                · -- right
                  by_cases h2707 : a ≤ ((34887/102400 : ℚ) : ℝ)
                  · -- left
                    by_cases h2708 : a ≤ ((348021/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e241_pos (not_le.mp h2703).le h2708 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e242_pos (not_le.mp h2708).le h2707 hz1 hz2 hz
                  · -- right
                    by_cases h2709 : a ≤ ((349719/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e243_pos (not_le.mp h2707).le h2709 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e244_pos (not_le.mp h2709).le h2702 hz1 hz2 hz
              · -- right
                by_cases h2710 : a ≤ ((88491/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2711 : a ≤ ((176133/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2712 : a ≤ ((351417/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e245_pos (not_le.mp h2702).le h2712 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e246_pos (not_le.mp h2712).le h2711 hz1 hz2 hz
                  · -- right
                    by_cases h2713 : a ≤ ((70623/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e247_pos (not_le.mp h2711).le h2713 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e248_pos (not_le.mp h2713).le h2710 hz1 hz2 hz
                · -- right
                  by_cases h2714 : a ≤ ((177831/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e105_pos (not_le.mp h2710).le h2714 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e106_pos (not_le.mp h2714).le h2701 hz1 hz2 hz
            · -- right
              by_cases h2715 : a ≤ ((45519/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2716 : a ≤ ((90189/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2717 : a ≤ ((179529/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e107_pos (not_le.mp h2701).le h2717 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e108_pos (not_le.mp h2717).le h2716 hz1 hz2 hz
                · -- right
                  by_cases h2718 : a ≤ ((181227/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e109_pos (not_le.mp h2716).le h2718 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e110_pos (not_le.mp h2718).le h2715 hz1 hz2 hz
              · -- right
                by_cases h2719 : a ≤ ((91887/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2720 : a ≤ ((7317/20480 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e111_pos (not_le.mp h2715).le h2720 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e112_pos (not_le.mp h2720).le h2719 hz1 hz2 hz
                · -- right
                  by_cases h2721 : a ≤ ((184623/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e113_pos (not_le.mp h2719).le h2721 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e114_pos (not_le.mp h2721).le h1 hz1 hz2 hz
    · -- right
      by_cases h2722 : a ≤ ((3747/8000 : ℚ) : ℝ)
      · -- left
        by_cases h2723 : a ≤ ((1329/3200 : ℚ) : ℝ)
        · -- left
          by_cases h2724 : a ≤ ((12441/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2725 : a ≤ ((24033/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2726 : a ≤ ((47217/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2727 : a ≤ ((18717/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2728 : a ≤ ((186321/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e115_pos (not_le.mp h1).le h2728 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e116_pos (not_le.mp h2728).le h2727 hz1 hz2 hz
                · -- right
                  by_cases h2729 : a ≤ ((188019/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e117_pos (not_le.mp h2727).le h2729 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B001.e118_pos (not_le.mp h2729).le h2726 hz1 hz2 hz
              · -- right
                by_cases h2730 : a ≤ ((95283/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2731 : a ≤ ((189717/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B001.e119_pos (not_le.mp h2726).le h2731 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e120_pos (not_le.mp h2731).le h2730 hz1 hz2 hz
                · -- right
                  by_cases h2732 : a ≤ ((38283/102400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e121_pos (not_le.mp h2730).le h2732 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e122_pos (not_le.mp h2732).le h2725 hz1 hz2 hz
            · -- right
              by_cases h2733 : a ≤ ((9783/25600 : ℚ) : ℝ)
              · -- left
                by_cases h2734 : a ≤ ((96981/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2735 : a ≤ ((193113/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e123_pos (not_le.mp h2725).le h2735 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e124_pos (not_le.mp h2735).le h2734 hz1 hz2 hz
                · -- right
                  by_cases h2736 : a ≤ ((194811/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e125_pos (not_le.mp h2734).le h2736 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e126_pos (not_le.mp h2736).le h2733 hz1 hz2 hz
              · -- right
                by_cases h2737 : a ≤ ((98679/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2738 : a ≤ ((196509/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e127_pos (not_le.mp h2733).le h2738 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e128_pos (not_le.mp h2738).le h2737 hz1 hz2 hz
                · -- right
                  by_cases h2739 : a ≤ ((198207/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e129_pos (not_le.mp h2737).le h2739 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e130_pos (not_le.mp h2739).le h2724 hz1 hz2 hz
          · -- right
            by_cases h2740 : a ≤ ((25731/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2741 : a ≤ ((50613/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2742 : a ≤ ((100377/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2743 : a ≤ ((39981/102400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e131_pos (not_le.mp h2724).le h2743 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e132_pos (not_le.mp h2743).le h2742 hz1 hz2 hz
                · -- right
                  by_cases h2744 : a ≤ ((201603/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e133_pos (not_le.mp h2742).le h2744 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e134_pos (not_le.mp h2744).le h2741 hz1 hz2 hz
              · -- right
                by_cases h2745 : a ≤ ((4083/10240 : ℚ) : ℝ)
                · -- left
                  by_cases h2746 : a ≤ ((203301/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e135_pos (not_le.mp h2741).le h2746 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e136_pos (not_le.mp h2746).le h2745 hz1 hz2 hz
                · -- right
                  by_cases h2747 : a ≤ ((204999/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e137_pos (not_le.mp h2745).le h2747 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e138_pos (not_le.mp h2747).le h2740 hz1 hz2 hz
            · -- right
              by_cases h2748 : a ≤ ((52311/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2749 : a ≤ ((103773/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2750 : a ≤ ((206697/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e139_pos (not_le.mp h2740).le h2750 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e140_pos (not_le.mp h2750).le h2749 hz1 hz2 hz
                · -- right
                  by_cases h2751 : a ≤ ((41679/102400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e141_pos (not_le.mp h2749).le h2751 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e142_pos (not_le.mp h2751).le h2748 hz1 hz2 hz
              · -- right
                by_cases h2752 : a ≤ ((105471/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2753 : a ≤ ((210093/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e143_pos (not_le.mp h2748).le h2753 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e144_pos (not_le.mp h2753).le h2752 hz1 hz2 hz
                · -- right
                  by_cases h2754 : a ≤ ((211791/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e145_pos (not_le.mp h2752).le h2754 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e146_pos (not_le.mp h2754).le h2723 hz1 hz2 hz
        · -- right
          by_cases h2755 : a ≤ ((14139/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2756 : a ≤ ((27429/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2757 : a ≤ ((54009/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2758 : a ≤ ((107169/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2759 : a ≤ ((213489/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e147_pos (not_le.mp h2723).le h2759 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e148_pos (not_le.mp h2759).le h2758 hz1 hz2 hz
                · -- right
                  by_cases h2760 : a ≤ ((215187/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e149_pos (not_le.mp h2758).le h2760 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e150_pos (not_le.mp h2760).le h2757 hz1 hz2 hz
              · -- right
                by_cases h2761 : a ≤ ((108867/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2762 : a ≤ ((43377/102400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e151_pos (not_le.mp h2757).le h2762 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e152_pos (not_le.mp h2762).le h2761 hz1 hz2 hz
                · -- right
                  by_cases h2763 : a ≤ ((218583/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e153_pos (not_le.mp h2761).le h2763 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e154_pos (not_le.mp h2763).le h2756 hz1 hz2 hz
            · -- right
              by_cases h2764 : a ≤ ((55707/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2765 : a ≤ ((22113/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2766 : a ≤ ((220281/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e155_pos (not_le.mp h2756).le h2766 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e156_pos (not_le.mp h2766).le h2765 hz1 hz2 hz
                · -- right
                  by_cases h2767 : a ≤ ((221979/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e157_pos (not_le.mp h2765).le h2767 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e158_pos (not_le.mp h2767).le h2764 hz1 hz2 hz
              · -- right
                by_cases h2768 : a ≤ ((112263/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B000.e58_pos (not_le.mp h2764).le h2768 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B000.e59_pos (not_le.mp h2768).le h2755 hz1 hz2 hz
          · -- right
            by_cases h2769 : a ≤ ((29127/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2770 : a ≤ ((11481/25600 : ℚ) : ℝ)
              · -- left
                by_cases h2771 : a ≤ ((113961/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e60_pos (not_le.mp h2755).le h2771 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e61_pos (not_le.mp h2771).le h2770 hz1 hz2 hz
              · -- right
                by_cases h2772 : a ≤ ((115659/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e62_pos (not_le.mp h2770).le h2772 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e63_pos (not_le.mp h2772).le h2769 hz1 hz2 hz
            · -- right
              by_cases h2773 : a ≤ ((59103/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2774 : a ≤ ((117357/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e64_pos (not_le.mp h2769).le h2774 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e65_pos (not_le.mp h2774).le h2773 hz1 hz2 hz
              · -- right
                by_cases h2775 : a ≤ ((23811/51200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e66_pos (not_le.mp h2773).le h2775 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e67_pos (not_le.mp h2775).le h2722 hz1 hz2 hz
      · -- right
        by_cases h2776 : a ≤ ((8343/16000 : ℚ) : ℝ)
        · -- left
          by_cases h2777 : a ≤ ((15837/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2778 : a ≤ ((1233/2560 : ℚ) : ℝ)
            · -- left
              by_cases h2779 : a ≤ ((60801/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2780 : a ≤ ((120753/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e68_pos (not_le.mp h2722).le h2780 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e69_pos (not_le.mp h2780).le h2779 hz1 hz2 hz
              · -- right
                by_cases h2781 : a ≤ ((122451/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e70_pos (not_le.mp h2779).le h2781 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e71_pos (not_le.mp h2781).le h2778 hz1 hz2 hz
            · -- right
              by_cases h2782 : a ≤ ((62499/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2783 : a ≤ ((124149/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e72_pos (not_le.mp h2778).le h2783 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e73_pos (not_le.mp h2783).le h2782 hz1 hz2 hz
              · -- right
                by_cases h2784 : a ≤ ((125847/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e74_pos (not_le.mp h2782).le h2784 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e75_pos (not_le.mp h2784).le h2777 hz1 hz2 hz
          · -- right
            by_cases h2785 : a ≤ ((32523/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2786 : a ≤ ((64197/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2787 : a ≤ ((25509/51200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e76_pos (not_le.mp h2777).le h2787 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e77_pos (not_le.mp h2787).le h2786 hz1 hz2 hz
              · -- right
                by_cases h2788 : a ≤ ((129243/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e78_pos (not_le.mp h2786).le h2788 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e79_pos (not_le.mp h2788).le h2785 hz1 hz2 hz
            · -- right
              by_cases h2789 : a ≤ ((13179/25600 : ℚ) : ℝ)
              · -- left
                by_cases h2790 : a ≤ ((130941/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e80_pos (not_le.mp h2785).le h2790 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e81_pos (not_le.mp h2790).le h2789 hz1 hz2 hz
              · -- right
                by_cases h2791 : a ≤ ((132639/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e82_pos (not_le.mp h2789).le h2791 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e83_pos (not_le.mp h2791).le h2776 hz1 hz2 hz
        · -- right
          by_cases h2792 : a ≤ ((3507/6400 : ℚ) : ℝ)
          · -- left
            by_cases h2793 : a ≤ ((34221/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2794 : a ≤ ((67593/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2795 : a ≤ ((134337/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e84_pos (not_le.mp h2776).le h2795 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e85_pos (not_le.mp h2795).le h2794 hz1 hz2 hz
              · -- right
                by_cases h2796 : a ≤ ((27207/51200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e86_pos (not_le.mp h2794).le h2796 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e87_pos (not_le.mp h2796).le h2793 hz1 hz2 hz
            · -- right
              by_cases h2797 : a ≤ ((69291/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2798 : a ≤ ((137733/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e88_pos (not_le.mp h2793).le h2798 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e89_pos (not_le.mp h2798).le h2797 hz1 hz2 hz
              · -- right
                by_cases h2799 : a ≤ ((139431/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e90_pos (not_le.mp h2797).le h2799 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e91_pos (not_le.mp h2799).le h2792 hz1 hz2 hz
          · -- right
            by_cases h2800 : a ≤ ((35919/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2801 : a ≤ ((70989/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2802 : a ≤ ((141129/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e92_pos (not_le.mp h2792).le h2802 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e93_pos (not_le.mp h2802).le h2801 hz1 hz2 hz
              · -- right
                by_cases h2803 : a ≤ ((142827/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e94_pos (not_le.mp h2801).le h2803 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e95_pos (not_le.mp h2803).le h2800 hz1 hz2 hz
            · -- right
              by_cases h2804 : a ≤ ((72687/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e0_pos (not_le.mp h2800).le h2804 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e1_pos (not_le.mp h2804).le h0 hz1 hz2 hz
  · -- right
    by_cases h2805 : a ≤ ((3147/4000 : ℚ) : ℝ)
    · -- left
      by_cases h2806 : a ≤ ((1089/1600 : ℚ) : ℝ)
      · -- left
        by_cases h2807 : a ≤ ((10041/16000 : ℚ) : ℝ)
        · -- left
          by_cases h2808 : a ≤ ((19233/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2809 : a ≤ ((37617/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2810 : a ≤ ((14877/25600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e2_pos (not_le.mp h0).le h2810 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e3_pos (not_le.mp h2810).le h2809 hz1 hz2 hz
            · -- right
              by_cases h2811 : a ≤ ((76083/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e4_pos (not_le.mp h2809).le h2811 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e5_pos (not_le.mp h2811).le h2808 hz1 hz2 hz
          · -- right
            by_cases h2812 : a ≤ ((7863/12800 : ℚ) : ℝ)
            · -- left
              by_cases h2813 : a ≤ ((77781/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e6_pos (not_le.mp h2808).le h2813 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e7_pos (not_le.mp h2813).le h2812 hz1 hz2 hz
            · -- right
              by_cases h2814 : a ≤ ((79479/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e8_pos (not_le.mp h2812).le h2814 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e9_pos (not_le.mp h2814).le h2807 hz1 hz2 hz
        · -- right
          by_cases h2815 : a ≤ ((20931/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2816 : a ≤ ((41013/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2817 : a ≤ ((81177/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e10_pos (not_le.mp h2807).le h2817 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e11_pos (not_le.mp h2817).le h2816 hz1 hz2 hz
            · -- right
              by_cases h2818 : a ≤ ((663/1024 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e12_pos (not_le.mp h2816).le h2818 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e13_pos (not_le.mp h2818).le h2815 hz1 hz2 hz
          · -- right
            by_cases h2819 : a ≤ ((42711/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2820 : a ≤ ((84573/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e14_pos (not_le.mp h2815).le h2820 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e15_pos (not_le.mp h2820).le h2819 hz1 hz2 hz
            · -- right
              by_cases h2821 : a ≤ ((86271/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e16_pos (not_le.mp h2819).le h2821 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e17_pos (not_le.mp h2821).le h2806 hz1 hz2 hz
      · -- right
        by_cases h2822 : a ≤ ((11739/16000 : ℚ) : ℝ)
        · -- left
          by_cases h2823 : a ≤ ((22629/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2824 : a ≤ ((44409/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2825 : a ≤ ((87969/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e18_pos (not_le.mp h2806).le h2825 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e19_pos (not_le.mp h2825).le h2824 hz1 hz2 hz
            · -- right
              by_cases h2826 : a ≤ ((89667/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e20_pos (not_le.mp h2824).le h2826 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e21_pos (not_le.mp h2826).le h2823 hz1 hz2 hz
          · -- right
            by_cases h2827 : a ≤ ((46107/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2828 : a ≤ ((18273/25600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e22_pos (not_le.mp h2823).le h2828 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e23_pos (not_le.mp h2828).le h2827 hz1 hz2 hz
            · -- right
              by_cases h2829 : a ≤ ((93063/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e24_pos (not_le.mp h2827).le h2829 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e25_pos (not_le.mp h2829).le h2822 hz1 hz2 hz
        · -- right
          by_cases h2830 : a ≤ ((24327/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2831 : a ≤ ((9561/12800 : ℚ) : ℝ)
            · -- left
              by_cases h2832 : a ≤ ((94761/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e26_pos (not_le.mp h2822).le h2832 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e27_pos (not_le.mp h2832).le h2831 hz1 hz2 hz
            · -- right
              by_cases h2833 : a ≤ ((96459/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e28_pos (not_le.mp h2831).le h2833 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e29_pos (not_le.mp h2833).le h2830 hz1 hz2 hz
          · -- right
            by_cases h2834 : a ≤ ((49503/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2835 : a ≤ ((98157/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e30_pos (not_le.mp h2830).le h2835 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e31_pos (not_le.mp h2835).le h2834 hz1 hz2 hz
            · -- right
              by_cases h2836 : a ≤ ((19971/25600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e32_pos (not_le.mp h2834).le h2836 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e33_pos (not_le.mp h2836).le h2805 hz1 hz2 hz
    · -- right
      by_cases h2837 : a ≤ ((7143/8000 : ℚ) : ℝ)
      · -- left
        by_cases h2838 : a ≤ ((13437/16000 : ℚ) : ℝ)
        · -- left
          by_cases h2839 : a ≤ ((1041/1280 : ℚ) : ℝ)
          · -- left
            by_cases h2840 : a ≤ ((51201/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2841 : a ≤ ((101553/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e34_pos (not_le.mp h2805).le h2841 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e35_pos (not_le.mp h2841).le h2840 hz1 hz2 hz
            · -- right
              by_cases h2842 : a ≤ ((103251/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e36_pos (not_le.mp h2840).le h2842 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e37_pos (not_le.mp h2842).le h2839 hz1 hz2 hz
          · -- right
            by_cases h2843 : a ≤ ((52899/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2844 : a ≤ ((104949/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e38_pos (not_le.mp h2839).le h2844 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e39_pos (not_le.mp h2844).le h2843 hz1 hz2 hz
            · -- right
              by_cases h2845 : a ≤ ((106647/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e40_pos (not_le.mp h2843).le h2845 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e41_pos (not_le.mp h2845).le h2838 hz1 hz2 hz
        · -- right
          by_cases h2846 : a ≤ ((27723/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2847 : a ≤ ((54597/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2848 : a ≤ ((21669/25600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e42_pos (not_le.mp h2838).le h2848 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e43_pos (not_le.mp h2848).le h2847 hz1 hz2 hz
            · -- right
              by_cases h2849 : a ≤ ((110043/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e44_pos (not_le.mp h2847).le h2849 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e45_pos (not_le.mp h2849).le h2846 hz1 hz2 hz
          · -- right
            by_cases h2850 : a ≤ ((11259/12800 : ℚ) : ℝ)
            · -- left
              by_cases h2851 : a ≤ ((111741/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e46_pos (not_le.mp h2846).le h2851 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e47_pos (not_le.mp h2851).le h2850 hz1 hz2 hz
            · -- right
              by_cases h2852 : a ≤ ((113439/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e48_pos (not_le.mp h2850).le h2852 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e49_pos (not_le.mp h2852).le h2837 hz1 hz2 hz
      · -- right
        by_cases h2853 : a ≤ ((3027/3200 : ℚ) : ℝ)
        · -- left
          by_cases h2854 : a ≤ ((29421/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2855 : a ≤ ((57993/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2856 : a ≤ ((115137/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e50_pos (not_le.mp h2837).le h2856 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e51_pos (not_le.mp h2856).le h2855 hz1 hz2 hz
            · -- right
              by_cases h2857 : a ≤ ((23367/25600 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e52_pos (not_le.mp h2855).le h2857 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e53_pos (not_le.mp h2857).le h2854 hz1 hz2 hz
          · -- right
            by_cases h2858 : a ≤ ((59691/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2859 : a ≤ ((118533/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e54_pos (not_le.mp h2854).le h2859 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e55_pos (not_le.mp h2859).le h2858 hz1 hz2 hz
            · -- right
              by_cases h2860 : a ≤ ((120231/128000 : ℚ) : ℝ)
              · -- left
                exact CKLaneC2R.EpCells.B000.e56_pos (not_le.mp h2858).le h2860 hz1 hz2 hz
              · -- right
                exact CKLaneC2R.EpCells.B000.e57_pos (not_le.mp h2860).le h2853 hz1 hz2 hz
        · -- right
          by_cases h2861 : a ≤ ((31119/32000 : ℚ) : ℝ)
          · -- left
            by_cases h2862 : a ≤ ((61389/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2863 : a ≤ ((121929/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2864 : a ≤ ((243009/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e96_pos (not_le.mp h2853).le h2864 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e97_pos (not_le.mp h2864).le h2863 hz1 hz2 hz
              · -- right
                by_cases h2865 : a ≤ ((244707/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e98_pos (not_le.mp h2863).le h2865 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e99_pos (not_le.mp h2865).le h2862 hz1 hz2 hz
            · -- right
              by_cases h2866 : a ≤ ((123627/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2867 : a ≤ ((49281/51200 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e100_pos (not_le.mp h2862).le h2867 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e101_pos (not_le.mp h2867).le h2866 hz1 hz2 hz
              · -- right
                by_cases h2868 : a ≤ ((248103/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e102_pos (not_le.mp h2866).le h2868 hz1 hz2 hz
                · -- right
                  exact CKLaneC2R.EpCells.B001.e103_pos (not_le.mp h2868).le h2861 hz1 hz2 hz
          · -- right
            by_cases h2869 : a ≤ ((63087/64000 : ℚ) : ℝ)
            · -- left
              by_cases h2870 : a ≤ ((5013/5120 : ℚ) : ℝ)
              · -- left
                by_cases h2871 : a ≤ ((249801/256000 : ℚ) : ℝ)
                · -- left
                  exact CKLaneC2R.EpCells.B001.e104_pos (not_le.mp h2861).le h2871 hz1 hz2 hz
                · -- right
                  by_cases h2872 : a ≤ ((500451/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e159_pos (not_le.mp h2871).le h2872 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e160_pos (not_le.mp h2872).le h2870 hz1 hz2 hz
              · -- right
                by_cases h2873 : a ≤ ((251499/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2874 : a ≤ ((502149/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e161_pos (not_le.mp h2870).le h2874 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e162_pos (not_le.mp h2874).le h2873 hz1 hz2 hz
                · -- right
                  by_cases h2875 : a ≤ ((503847/512000 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e163_pos (not_le.mp h2873).le h2875 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e164_pos (not_le.mp h2875).le h2869 hz1 hz2 hz
            · -- right
              by_cases h2876 : a ≤ ((127023/128000 : ℚ) : ℝ)
              · -- left
                by_cases h2877 : a ≤ ((253197/256000 : ℚ) : ℝ)
                · -- left
                  by_cases h2878 : a ≤ ((101109/102400 : ℚ) : ℝ)
                  · -- left
                    exact CKLaneC2R.EpCells.B002.e165_pos (not_le.mp h2869).le h2878 hz1 hz2 hz
                  · -- right
                    exact CKLaneC2R.EpCells.B002.e166_pos (not_le.mp h2878).le h2877 hz1 hz2 hz
                · -- right
                  by_cases h2879 : a ≤ ((507243/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2880 : a ≤ ((1013637/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e249_pos (not_le.mp h2877).le h2880 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e250_pos (not_le.mp h2880).le h2879 hz1 hz2 hz
                  · -- right
                    by_cases h2881 : a ≤ ((203067/204800 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e251_pos (not_le.mp h2879).le h2881 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e252_pos (not_le.mp h2881).le h2876 hz1 hz2 hz
              · -- right
                by_cases h2882 : a ≤ ((50979/51200 : ℚ) : ℝ)
                · -- left
                  by_cases h2883 : a ≤ ((508941/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2884 : a ≤ ((1017033/1024000 : ℚ) : ℝ)
                    · -- left
                      exact CKLaneC2R.EpCells.B004.e253_pos (not_le.mp h2876).le h2884 hz1 hz2 hz
                    · -- right
                      exact CKLaneC2R.EpCells.B004.e254_pos (not_le.mp h2884).le h2883 hz1 hz2 hz
                  · -- right
                    by_cases h2885 : a ≤ ((1018731/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2886 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e272_pos (not_le.mp h2883).le h2885 hz1 h2886 hz
                      · -- right
                        exact CKLaneC2R.EpCells.B004.e273_pos (not_le.mp h2883).le h2885 (not_le.mp h2886).le hz2 hz
                    · -- right
                      by_cases h2887 : z ≤ ((1999/2000 : ℚ) : ℝ)
                      · -- left
                        exact CKLaneC2R.EpCells.B004.e274_pos (not_le.mp h2885).le h2882 hz1 h2887 hz
                      · -- right
                        by_cases h2888 : a ≤ ((2038311/2048000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e532_pos (not_le.mp h2885).le h2888 (not_le.mp h2887).le hz2 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e533_pos (not_le.mp h2888).le h2882 (not_le.mp h2887).le hz2 hz
                · -- right
                  by_cases h2889 : a ≤ ((510639/512000 : ℚ) : ℝ)
                  · -- left
                    by_cases h2890 : a ≤ ((1020429/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2891 : a ≤ ((2040009/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2892 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e534_pos (not_le.mp h2882).le h2891 hz1 h2892 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e536_pos (not_le.mp h2882).le h2891 (not_le.mp h2892).le hz2 hz
                      · -- right
                        by_cases h2893 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e535_pos (not_le.mp h2891).le h2890 hz1 h2893 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B008.e537_pos (not_le.mp h2891).le h2890 (not_le.mp h2893).le hz2 hz
                    · -- right
                      by_cases h2894 : a ≤ ((2041707/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2895 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e538_pos (not_le.mp h2890).le h2894 hz1 h2895 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B009.e540_pos (not_le.mp h2890).le h2894 (not_le.mp h2895).le hz2 hz
                      · -- right
                        by_cases h2896 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B008.e539_pos (not_le.mp h2894).le h2889 hz1 h2896 hz
                        · -- right
                          exact CKLaneC2R.EpCells.B009.e541_pos (not_le.mp h2894).le h2889 (not_le.mp h2896).le hz2 hz
                  · -- right
                    by_cases h2897 : a ≤ ((1022127/1024000 : ℚ) : ℝ)
                    · -- left
                      by_cases h2898 : a ≤ ((408681/409600 : ℚ) : ℝ)
                      · -- left
                        by_cases h2899 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B009.e542_pos (not_le.mp h2889).le h2898 hz1 h2899 hz
                        · -- right
                          by_cases h2900 : z ≤ ((3999/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e586_pos (not_le.mp h2889).le h2898 (not_le.mp h2899).le h2900 hz
                          · -- right
                            by_cases h2901 : a ≤ ((4085961/4096000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1405_pos (not_le.mp h2889).le h2901 (not_le.mp h2900).le hz2 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1406_pos (not_le.mp h2901).le h2898 (not_le.mp h2900).le hz2 hz
                      · -- right
                        by_cases h2902 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          exact CKLaneC2R.EpCells.B009.e543_pos (not_le.mp h2898).le h2897 hz1 h2902 hz
                        · -- right
                          by_cases h2903 : a ≤ ((4087659/4096000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2904 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1407_pos (not_le.mp h2898).le h2903 (not_le.mp h2902).le h2904 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1409_pos (not_le.mp h2898).le h2903 (not_le.mp h2904).le hz2 hz
                          · -- right
                            by_cases h2905 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1408_pos (not_le.mp h2903).le h2897 (not_le.mp h2902).le h2905 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1410_pos (not_le.mp h2903).le h2897 (not_le.mp h2905).le hz2 hz
                    · -- right
                      by_cases h2906 : a ≤ ((2045103/2048000 : ℚ) : ℝ)
                      · -- left
                        by_cases h2907 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2908 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e587_pos (not_le.mp h2897).le h2906 hz1 h2908 hz
                          · -- right
                            exact CKLaneC2R.EpCells.B009.e588_pos (not_le.mp h2897).le h2906 (not_le.mp h2908).le h2907 hz
                        · -- right
                          by_cases h2909 : a ≤ ((4089357/4096000 : ℚ) : ℝ)
                          · -- left
                            by_cases h2910 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1413_pos (not_le.mp h2897).le h2909 (not_le.mp h2907).le h2910 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1415_pos (not_le.mp h2897).le h2909 (not_le.mp h2910).le hz2 hz
                          · -- right
                            by_cases h2911 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1414_pos (not_le.mp h2909).le h2906 (not_le.mp h2907).le h2911 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1416_pos (not_le.mp h2909).le h2906 (not_le.mp h2911).le hz2 hz
                      · -- right
                        by_cases h2912 : z ≤ ((1999/2000 : ℚ) : ℝ)
                        · -- left
                          by_cases h2913 : z ≤ ((3997/4000 : ℚ) : ℝ)
                          · -- left
                            exact CKLaneC2R.EpCells.B009.e589_pos (not_le.mp h2906).le ha2 hz1 h2913 hz
                          · -- right
                            by_cases h2914 : a ≤ ((818211/819200 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1411_pos (not_le.mp h2906).le h2914 (not_le.mp h2913).le h2912 hz
                            · -- right
                              exact CKLaneC2R.EpCells.B023.e1412_pos (not_le.mp h2914).le ha2 (not_le.mp h2913).le h2912 hz
                        · -- right
                          by_cases h2915 : a ≤ ((818211/819200 : ℚ) : ℝ)
                          · -- left
                            by_cases h2916 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1417_pos (not_le.mp h2906).le h2915 (not_le.mp h2912).le h2916 hz
                            · -- right
                              by_cases h2917 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1525_pos (not_le.mp h2906).le h2915 (not_le.mp h2916).le h2917 hz
                              · -- right
                                exact CKLaneC2R.EpCells.B025.e1526_pos (not_le.mp h2906).le h2915 (not_le.mp h2917).le hz2 hz
                          · -- right
                            by_cases h2918 : z ≤ ((3999/4000 : ℚ) : ℝ)
                            · -- left
                              exact CKLaneC2R.EpCells.B023.e1418_pos (not_le.mp h2915).le ha2 (not_le.mp h2912).le h2918 hz
                            · -- right
                              by_cases h2919 : z ≤ ((7999/8000 : ℚ) : ℝ)
                              · -- left
                                exact CKLaneC2R.EpCells.B025.e1527_pos (not_le.mp h2915).le ha2 (not_le.mp h2918).le h2919 hz
                              · -- right
                                by_cases h2920 : a ≤ ((8182959/8192000 : ℚ) : ℝ)
                                · -- left
                                  exact CKLaneC2R.EpCells.B048.e2920_pos (not_le.mp h2915).le h2920 (not_le.mp h2919).le hz2 hz
                                · -- right
                                  exact CKLaneC2R.EpCells.B048.e2921_pos (not_le.mp h2920).le ha2 (not_le.mp h2919).le hz2 hz

end CKLaneC2R.EndpointCover

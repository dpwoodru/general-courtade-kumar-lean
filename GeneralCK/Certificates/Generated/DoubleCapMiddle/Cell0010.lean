import GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0010Logs
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0010
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Reflection
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cell_bias_nonneg (m : ℝ) (hm : Bounds (1 / 4) (2563 / 10240) m) :
    let h := (1 + H (2*m - 1/2))/2
    let x := 1-2*m
    let y := 1-2*entropyInverse h
    let c := regularContact (x/(Real.log 2*h))
    0 ≤ 2*(biasE x-Real.log 2*h)-y*SmallMean.A y+x*SmallMean.A c := by
  have hEq : biasE (2-4*m) = Real.log 2 * H (2*m-1/2) := by
    by_cases hquarter : m = 1/4
    · subst m
      norm_num [biasE, H_zero]
    · have hmstrict : 1/4 < m := lt_of_le_of_ne hm.1 (Ne.symm hquarter)
      rw [show 2-4*m = 1-2*(2*m-1/2) by ring,
        GeneralCK.Correction.Natural.biasE_probability (by linarith [hmstrict]) (by linarith [hm.2]),
        GeneralCK.Certificates.Mixed.hn_eq_H_mul_log]
      ring
  have hLh : Real.log 2 * ((1 + H (2*m - 1/2))/2) = (Real.log 2 + biasE (2-4*m))/2 := by
    rw [hEq]
    ring
  let x0 : ℝ := (2 / 1)*m
  have hx0 : Bounds (1 / 2) (2563 / 5120) x0 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hm <;> norm_num
  let x1 : ℝ := -x0
  have hx1 : Bounds (-2563 / 5120) (-1 / 2) x1 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx0
  let x2 : ℝ := (1 / 1)+x1
  have hx2 : Bounds (2557 / 5120) (1 / 2) x2 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx1 <;> norm_num
  let x3 : ℝ := (1 / 1)-x0
  have hx3 : Bounds (2557 / 5120) (1 / 2) x3 := by
    exact hx2
  let x4 : ℝ := (4 / 1)*m
  have hx4 : Bounds (1 / 1) (2563 / 2560) x4 := by
    apply bounds_mul (bounds_const ((4 / 1) : ℝ)) hm <;> norm_num
  let x5 : ℝ := -x4
  have hx5 : Bounds (-2563 / 2560) (-1 / 1) x5 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx4
  let x6 : ℝ := (2 / 1)+x5
  have hx6 : Bounds (2557 / 2560) (1 / 1) x6 := by
    apply bounds_add (bounds_const ((2 / 1) : ℝ)) hx5 <;> norm_num
  let x7 : ℝ := (2 / 1)-x4
  have hx7 : Bounds (2557 / 2560) (1 / 1) x7 := by
    exact hx6
  let x8 : ℝ := Real.log (2 / 1)
  have hx8 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x8 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x9 : ℝ := (1 / 1)+(1 / 2)
  have hx9 : Bounds (3 / 2) (3 / 2) x9 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x10 : ℝ := (1 / 1)+(1 / 2)
  have hx10 : Bounds (3 / 2) (3 / 2) x10 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((1 / 2) : ℝ)) <;> norm_num
  let x11 : ℝ := Real.log x10
  have hx11 : Bounds (101366277 / 250000000) (405465109 / 1000000000) x11 := by
    exact bounds_log hx10 (by norm_num) (by simpa only [div_one] using reflection_log_1.1) (by simpa only [div_one] using reflection_log_1.2)
  let x12 : ℝ := x9*x11
  have hx12 : Bounds (304098831 / 500000000) (1216395327 / 2000000000) x12 := by
    apply bounds_mul hx9 hx11 <;> norm_num
  let x13 : ℝ := -(1 / 2)
  have hx13 : Bounds (-1 / 2) (-1 / 2) x13 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x14 : ℝ := (1 / 1)+x13
  have hx14 : Bounds (1 / 2) (1 / 2) x14 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx13 <;> norm_num
  let x15 : ℝ := (1 / 1)-(1 / 2)
  have hx15 : Bounds (1 / 2) (1 / 2) x15 := by
    exact hx14
  let x16 : ℝ := -(1 / 2)
  have hx16 : Bounds (-1 / 2) (-1 / 2) x16 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((1 / 2) : ℝ))
  let x17 : ℝ := (1 / 1)+x16
  have hx17 : Bounds (1 / 2) (1 / 2) x17 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx16 <;> norm_num
  let x18 : ℝ := (1 / 1)-(1 / 2)
  have hx18 : Bounds (1 / 2) (1 / 2) x18 := by
    exact hx17
  let x19 : ℝ := Real.log x18
  have hx19 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) x19 := by
    exact bounds_log hx18 (by norm_num) (by simpa only [div_one] using reflection_log_2.1) (by simpa only [div_one] using reflection_log_2.2)
  let x20 : ℝ := x15*x19
  have hx20 : Bounds (-693147181 / 2000000000) (-34657359 / 100000000) x20 := by
    apply bounds_mul hx15 hx19 <;> norm_num
  let x21 : ℝ := x12+x20
  have hx21 : Bounds (523248143 / 2000000000) (523248147 / 2000000000) x21 := by
    apply bounds_add hx12 hx20 <;> norm_num
  let x22 : ℝ := (2 / 1)⁻¹
  have hx22 : Bounds (1 / 2) (1 / 2) x22 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x23 : ℝ := x21*x22
  have hx23 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x23 := by
    apply bounds_mul hx21 hx22 <;> norm_num
  let x24 : ℝ := x21/(2 / 1)
  have hx24 : Bounds (523248143 / 4000000000) (523248147 / 4000000000) x24 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx23
  let x25 : ℝ := -x24
  have hx25 : Bounds (-523248147 / 4000000000) (-523248143 / 4000000000) x25 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx24
  let x26 : ℝ := x8+x25
  have hx26 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x26 := by
    apply bounds_add hx8 hx25 <;> norm_num
  let x27 : ℝ := x8-x24
  have hx27 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x27 := by
    exact hx26
  let x28 : ℝ := biasE (1 / 2)
  have hx28 : Bounds (2249340573 / 4000000000) (2249340581 / 4000000000) x28 := by
    simpa +zetaDelta only [biasE, div_one] using hx27
  let x29 : ℝ := Real.log (2 / 1)
  have hx29 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x29 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x30 : ℝ := (1 / 1)+(2557 / 5120)
  have hx30 : Bounds (7677 / 5120) (7677 / 5120) x30 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x31 : ℝ := (1 / 1)+(2557 / 5120)
  have hx31 : Bounds (7677 / 5120) (7677 / 5120) x31 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 5120) : ℝ)) <;> norm_num
  let x32 : ℝ := Real.log x31
  have hx32 : Bounds (202537203 / 500000000) (405074407 / 1000000000) x32 := by
    exact bounds_log hx31 (by norm_num) (by simpa only [div_one] using reflection_log_3.1) (by simpa only [div_one] using reflection_log_3.2)
  let x33 : ℝ := x30*x32
  have hx33 : Bounds (121474852143 / 200000000000) (121474852443 / 200000000000) x33 := by
    apply bounds_mul hx30 hx32 <;> norm_num
  let x34 : ℝ := -(2557 / 5120)
  have hx34 : Bounds (-2557 / 5120) (-2557 / 5120) x34 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x35 : ℝ := (1 / 1)+x34
  have hx35 : Bounds (2563 / 5120) (2563 / 5120) x35 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx34 <;> norm_num
  let x36 : ℝ := (1 / 1)-(2557 / 5120)
  have hx36 : Bounds (2563 / 5120) (2563 / 5120) x36 := by
    exact hx35
  let x37 : ℝ := -(2557 / 5120)
  have hx37 : Bounds (-2557 / 5120) (-2557 / 5120) x37 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 5120) : ℝ))
  let x38 : ℝ := (1 / 1)+x37
  have hx38 : Bounds (2563 / 5120) (2563 / 5120) x38 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx37 <;> norm_num
  let x39 : ℝ := (1 / 1)-(2557 / 5120)
  have hx39 : Bounds (2563 / 5120) (2563 / 5120) x39 := by
    exact hx38
  let x40 : ℝ := Real.log x39
  have hx40 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) x40 := by
    exact bounds_log hx39 (by norm_num) (by simpa only [div_one] using reflection_log_4.1) (by simpa only [div_one] using reflection_log_4.2)
  let x41 : ℝ := x36*x40
  have hx41 : Bounds (-346393450683 / 1000000000000) (-173196725091 / 500000000000) x41 := by
    apply bounds_mul hx36 hx40 <;> norm_num
  let x42 : ℝ := x33+x41
  have hx42 : Bounds (16311300627 / 62500000000) (260980812033 / 1000000000000) x42 := by
    apply bounds_add hx33 hx41 <;> norm_num
  let x43 : ℝ := (2 / 1)⁻¹
  have hx43 : Bounds (1 / 2) (1 / 2) x43 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x44 : ℝ := x42*x43
  have hx44 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x44 := by
    apply bounds_mul hx42 hx43 <;> norm_num
  let x45 : ℝ := x42/(2 / 1)
  have hx45 : Bounds (16311300627 / 125000000000) (130490406017 / 1000000000000) x45 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx44
  let x46 : ℝ := -x45
  have hx46 : Bounds (-130490406017 / 1000000000000) (-16311300627 / 125000000000) x46 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx45
  let x47 : ℝ := x29+x46
  have hx47 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x47 := by
    apply bounds_add hx29 hx46 <;> norm_num
  let x48 : ℝ := x29-x45
  have hx48 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x48 := by
    exact hx47
  let x49 : ℝ := biasE (2557 / 5120)
  have hx49 : Bounds (562656773983 / 1000000000000) (35166048499 / 62500000000) x49 := by
    simpa +zetaDelta only [biasE, div_one] using hx48
  let x50 : ℝ := biasE x3
  have hx50 : Bounds (2249340573 / 4000000000) (35166048499 / 62500000000) x50 := by
    exact bounds_biasE hx3 (by norm_num) (by norm_num) hx28.1 hx49.2
  let x51 : ℝ := Real.log (2 / 1)
  have hx51 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x51 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x52 : ℝ := (1 / 1)+(2557 / 2560)
  have hx52 : Bounds (5117 / 2560) (5117 / 2560) x52 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x53 : ℝ := (1 / 1)+(2557 / 2560)
  have hx53 : Bounds (5117 / 2560) (5117 / 2560) x53 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((2557 / 2560) : ℝ)) <;> norm_num
  let x54 : ℝ := Real.log x53
  have hx54 : Bounds (692561071 / 1000000000) (43285067 / 62500000) x54 := by
    exact bounds_log hx53 (by norm_num) (by simpa only [div_one] using reflection_log_5.1) (by simpa only [div_one] using reflection_log_5.2)
  let x55 : ℝ := x52*x54
  have hx55 : Bounds (692155273497 / 500000000000) (692155274497 / 500000000000) x55 := by
    apply bounds_mul hx52 hx54 <;> norm_num
  let x56 : ℝ := -(2557 / 2560)
  have hx56 : Bounds (-2557 / 2560) (-2557 / 2560) x56 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x57 : ℝ := (1 / 1)+x56
  have hx57 : Bounds (3 / 2560) (3 / 2560) x57 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx56 <;> norm_num
  let x58 : ℝ := (1 / 1)-(2557 / 2560)
  have hx58 : Bounds (3 / 2560) (3 / 2560) x58 := by
    exact hx57
  let x59 : ℝ := -(2557 / 2560)
  have hx59 : Bounds (-2557 / 2560) (-2557 / 2560) x59 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((2557 / 2560) : ℝ))
  let x60 : ℝ := (1 / 1)+x59
  have hx60 : Bounds (3 / 2560) (3 / 2560) x60 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx59 <;> norm_num
  let x61 : ℝ := (1 / 1)-(2557 / 2560)
  have hx61 : Bounds (3 / 2560) (3 / 2560) x61 := by
    exact hx60
  let x62 : ℝ := Real.log x61
  have hx62 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) x62 := by
    exact bounds_log hx61 (by norm_num) (by simpa only [div_one] using reflection_log_6.1) (by simpa only [div_one] using reflection_log_6.2)
  let x63 : ℝ := x58*x62
  have hx63 : Bounds (-7909160453 / 1000000000000) (-7909160441 / 1000000000000) x63 := by
    apply bounds_mul hx58 hx62 <;> norm_num
  let x64 : ℝ := x55+x63
  have hx64 : Bounds (1376401386541 / 1000000000000) (1376401388553 / 1000000000000) x64 := by
    apply bounds_add hx55 hx63 <;> norm_num
  let x65 : ℝ := (2 / 1)⁻¹
  have hx65 : Bounds (1 / 2) (1 / 2) x65 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x66 : ℝ := x64*x65
  have hx66 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x66 := by
    apply bounds_mul hx64 hx65 <;> norm_num
  let x67 : ℝ := x64/(2 / 1)
  have hx67 : Bounds (68820069327 / 100000000000) (688200694277 / 1000000000000) x67 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx66
  let x68 : ℝ := -x67
  have hx68 : Bounds (-688200694277 / 1000000000000) (-68820069327 / 100000000000) x68 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx67
  let x69 : ℝ := x51+x68
  have hx69 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x69 := by
    apply bounds_add hx51 hx68 <;> norm_num
  let x70 : ℝ := x51-x67
  have hx70 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x70 := by
    exact hx69
  let x71 : ℝ := biasE (2557 / 2560)
  have hx71 : Bounds (4946485723 / 1000000000000) (494648773 / 100000000000) x71 := by
    simpa +zetaDelta only [biasE, div_one] using hx70
  let x72 : ℝ := biasE x7
  have hx72 : Bounds (0 / 1) (494648773 / 100000000000) x72 := by
    exact bounds_biasE hx7 (by norm_num) (by norm_num) (by norm_num [biasE]) hx71.2
  let x73 : ℝ := Real.log (2 / 1)
  have hx73 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x73 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x74 : ℝ := x73+x72
  have hx74 : Bounds (34657359 / 50000000) (69809366873 / 100000000000) x74 := by
    apply bounds_add hx73 hx72 <;> norm_num
  let x75 : ℝ := (2 / 1)⁻¹
  have hx75 : Bounds (1 / 2) (1 / 2) x75 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x76 : ℝ := x74*x75
  have hx76 : Bounds (34657359 / 100000000) (69809366873 / 200000000000) x76 := by
    apply bounds_mul hx74 hx75 <;> norm_num
  let x77 : ℝ := x74/(2 / 1)
  have hx77 : Bounds (34657359 / 100000000) (69809366873 / 200000000000) x77 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx76
  let x78 : ℝ := Real.log (2 / 1)
  have hx78 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x78 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x79 : ℝ := (1 / 1)+(777571 / 1000000)
  have hx79 : Bounds (1777571 / 1000000) (1777571 / 1000000) x79 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((777571 / 1000000) : ℝ)) <;> norm_num
  let x80 : ℝ := (1 / 1)+(777571 / 1000000)
  have hx80 : Bounds (1777571 / 1000000) (1777571 / 1000000) x80 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((777571 / 1000000) : ℝ)) <;> norm_num
  let x81 : ℝ := Real.log x80
  have hx81 : Bounds (23009913 / 40000000) (287623913 / 500000000) x81 := by
    exact bounds_log hx80 (by norm_num) (by simpa only [div_one] using reflection_log_7.1) (by simpa only [div_one] using reflection_log_7.2)
  let x82 : ℝ := x79*x81
  have hx82 : Bounds (1022543851533 / 1000000000000) (1022543853311 / 1000000000000) x82 := by
    apply bounds_mul hx79 hx81 <;> norm_num
  let x83 : ℝ := -(777571 / 1000000)
  have hx83 : Bounds (-777571 / 1000000) (-777571 / 1000000) x83 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((777571 / 1000000) : ℝ))
  let x84 : ℝ := (1 / 1)+x83
  have hx84 : Bounds (222429 / 1000000) (222429 / 1000000) x84 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx83 <;> norm_num
  let x85 : ℝ := (1 / 1)-(777571 / 1000000)
  have hx85 : Bounds (222429 / 1000000) (222429 / 1000000) x85 := by
    exact hx84
  let x86 : ℝ := -(777571 / 1000000)
  have hx86 : Bounds (-777571 / 1000000) (-777571 / 1000000) x86 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((777571 / 1000000) : ℝ))
  let x87 : ℝ := (1 / 1)+x86
  have hx87 : Bounds (222429 / 1000000) (222429 / 1000000) x87 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx86 <;> norm_num
  let x88 : ℝ := (1 / 1)-(777571 / 1000000)
  have hx88 : Bounds (222429 / 1000000) (222429 / 1000000) x88 := by
    exact hx87
  let x89 : ℝ := Real.log x88
  have hx89 : Bounds (-1503147331 / 1000000000) (-23486677 / 15625000) x89 := by
    exact bounds_log hx88 (by norm_num) (by simpa only [div_one] using reflection_log_8.1) (by simpa only [div_one] using reflection_log_8.2)
  let x90 : ℝ := x85*x89
  have hx90 : Bounds (-334343557687 / 1000000000000) (-334343557019 / 1000000000000) x90 := by
    apply bounds_mul hx85 hx89 <;> norm_num
  let x91 : ℝ := x82+x90
  have hx91 : Bounds (344100146923 / 500000000000) (172050074073 / 250000000000) x91 := by
    apply bounds_add hx82 hx90 <;> norm_num
  let x92 : ℝ := (2 / 1)⁻¹
  have hx92 : Bounds (1 / 2) (1 / 2) x92 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x93 : ℝ := x91*x92
  have hx93 : Bounds (344100146923 / 1000000000000) (172050074073 / 500000000000) x93 := by
    apply bounds_mul hx91 hx92 <;> norm_num
  let x94 : ℝ := x91/(2 / 1)
  have hx94 : Bounds (344100146923 / 1000000000000) (172050074073 / 500000000000) x94 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx93
  let x95 : ℝ := -x94
  have hx95 : Bounds (-172050074073 / 500000000000) (-344100146923 / 1000000000000) x95 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx94
  let x96 : ℝ := x78+x95
  have hx96 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x96 := by
    apply bounds_add hx78 hx95 <;> norm_num
  let x97 : ℝ := x78-x94
  have hx97 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x97 := by
    exact hx96
  let x98 : ℝ := biasE (777571 / 1000000)
  have hx98 : Bounds (174523515927 / 500000000000) (349047034077 / 1000000000000) x98 := by
    simpa +zetaDelta only [biasE, div_one] using hx97
  let x99 : ℝ := Real.log (2 / 1)
  have hx99 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x99 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x100 : ℝ := (1 / 1)+(155989 / 200000)
  have hx100 : Bounds (355989 / 200000) (355989 / 200000) x100 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((155989 / 200000) : ℝ)) <;> norm_num
  let x101 : ℝ := (1 / 1)+(155989 / 200000)
  have hx101 : Bounds (355989 / 200000) (355989 / 200000) x101 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((155989 / 200000) : ℝ)) <;> norm_num
  let x102 : ℝ := Real.log x101
  have hx102 : Bounds (9009101 / 15625000) (115316493 / 200000000) x102 := by
    exact bounds_log hx101 (by norm_num) (by simpa only [div_one] using reflection_log_9.1) (by simpa only [div_one] using reflection_log_9.2)
  let x103 : ℝ := x100*x102
  have hx103 : Bounds (256571268471 / 250000000000) (205257015133 / 200000000000) x103 := by
    apply bounds_mul hx100 hx102 <;> norm_num
  let x104 : ℝ := -(155989 / 200000)
  have hx104 : Bounds (-155989 / 200000) (-155989 / 200000) x104 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((155989 / 200000) : ℝ))
  let x105 : ℝ := (1 / 1)+x104
  have hx105 : Bounds (44011 / 200000) (44011 / 200000) x105 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx104 <;> norm_num
  let x106 : ℝ := (1 / 1)-(155989 / 200000)
  have hx106 : Bounds (44011 / 200000) (44011 / 200000) x106 := by
    exact hx105
  let x107 : ℝ := -(155989 / 200000)
  have hx107 : Bounds (-155989 / 200000) (-155989 / 200000) x107 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((155989 / 200000) : ℝ))
  let x108 : ℝ := (1 / 1)+x107
  have hx108 : Bounds (44011 / 200000) (44011 / 200000) x108 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx107 <;> norm_num
  let x109 : ℝ := (1 / 1)-(155989 / 200000)
  have hx109 : Bounds (44011 / 200000) (44011 / 200000) x109 := by
    exact hx108
  let x110 : ℝ := Real.log x109
  have hx110 : Bounds (-302775553 / 200000000) (-756938881 / 500000000) x110 := by
    exact bounds_log hx109 (by norm_num) (by simpa only [div_one] using reflection_log_10.1) (by simpa only [div_one] using reflection_log_10.2)
  let x111 : ℝ := x106*x110
  have hx111 : Bounds (-166568185789 / 500000000000) (-83284092729 / 250000000000) x111 := by
    apply bounds_mul hx106 hx110 <;> norm_num
  let x112 : ℝ := x103+x111
  have hx112 : Bounds (346574351153 / 500000000000) (693148704749 / 1000000000000) x112 := by
    apply bounds_add hx103 hx111 <;> norm_num
  let x113 : ℝ := (2 / 1)⁻¹
  have hx113 : Bounds (1 / 2) (1 / 2) x113 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x114 : ℝ := x112*x113
  have hx114 : Bounds (346574351153 / 1000000000000) (2772594819 / 8000000000) x114 := by
    apply bounds_mul hx112 hx113 <;> norm_num
  let x115 : ℝ := x112/(2 / 1)
  have hx115 : Bounds (346574351153 / 1000000000000) (2772594819 / 8000000000) x115 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx114
  let x116 : ℝ := -x115
  have hx116 : Bounds (-2772594819 / 8000000000) (-346574351153 / 1000000000000) x116 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx115
  let x117 : ℝ := x99+x116
  have hx117 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x117 := by
    apply bounds_add hx99 hx116 <;> norm_num
  let x118 : ℝ := x99-x115
  have hx118 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x118 := by
    exact hx117
  let x119 : ℝ := biasE (155989 / 200000)
  have hx119 : Bounds (2772582621 / 8000000000) (346572829847 / 1000000000000) x119 := by
    simpa +zetaDelta only [biasE, div_one] using hx118
  let y : ℝ := 1 - 2 * entropyInverse ((1 + H (2*m - 1/2))/2)
  have hLh' : Real.log 2 * ((1 + H (2*m - 1/2))/2) = x77 := by
    simpa +zetaDelta only [div_one] using hLh
  have hy : Bounds (777571 / 1000000) (155989 / 200000) y := by
    apply entropyInverseBias_bracket
    · exact div_nonneg (add_nonneg zero_le_one
        (H_nonneg (by linarith [hm.1]) (by linarith [hm.2]))) two_pos.le
    · linarith [H_le_one (2*m-1/2)]
    · norm_num
    · norm_num
    · norm_num
    · have h1 : biasE (155989 / 200000) ≤ (346572829847 / 1000000000000) := hx119.2
      have h2 : (34657359 / 100000000) ≤ x77 := hx77.1
      linarith [hLh']
    · have h1 : x77 ≤ (69809366873 / 200000000000) := hx77.2
      have h2 : (174523515927 / 500000000000) ≤ biasE (777571 / 1000000) := hx98.1
      linarith [hLh']
  let x120 : ℝ := x3⁻¹
  have hx120 : Bounds (2 / 1) (400469299961 / 200000000000) x120 := by
    apply bounds_inv hx3 <;> norm_num
  let x121 : ℝ := x77*x120
  have hx121 : Bounds (34657359 / 50000000) (698912707059 / 1000000000000) x121 := by
    apply bounds_mul hx77 hx120 <;> norm_num
  let x122 : ℝ := x77/x3
  have hx122 : Bounds (34657359 / 50000000) (698912707059 / 1000000000000) x122 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx121
  let x123 : ℝ := Real.log (2 / 1)
  have hx123 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x123 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x124 : ℝ := (1 / 1)+(328187 / 500000)
  have hx124 : Bounds (828187 / 500000) (828187 / 500000) x124 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x125 : ℝ := (1 / 1)+(328187 / 500000)
  have hx125 : Bounds (828187 / 500000) (828187 / 500000) x125 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x126 : ℝ := Real.log x125
  have hx126 : Bounds (4037047 / 8000000) (126157719 / 250000000) x126 := by
    exact bounds_log hx125 (by norm_num) (by simpa only [div_one] using reflection_log_11.1) (by simpa only [div_one] using reflection_log_11.2)
  let x127 : ℝ := x124*x126
  have hx127 : Bounds (835857460947 / 1000000000000) (208964365651 / 250000000000) x127 := by
    apply bounds_mul hx124 hx126 <;> norm_num
  let x128 : ℝ := -(328187 / 500000)
  have hx128 : Bounds (-328187 / 500000) (-328187 / 500000) x128 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((328187 / 500000) : ℝ))
  let x129 : ℝ := (1 / 1)+x128
  have hx129 : Bounds (171813 / 500000) (171813 / 500000) x129 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx128 <;> norm_num
  let x130 : ℝ := (1 / 1)-(328187 / 500000)
  have hx130 : Bounds (171813 / 500000) (171813 / 500000) x130 := by
    exact hx129
  let x131 : ℝ := -(328187 / 500000)
  have hx131 : Bounds (-328187 / 500000) (-328187 / 500000) x131 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((328187 / 500000) : ℝ))
  let x132 : ℝ := (1 / 1)+x131
  have hx132 : Bounds (171813 / 500000) (171813 / 500000) x132 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx131 <;> norm_num
  let x133 : ℝ := (1 / 1)-(328187 / 500000)
  have hx133 : Bounds (171813 / 500000) (171813 / 500000) x133 := by
    exact hx132
  let x134 : ℝ := Real.log x133
  have hx134 : Bounds (-1068201423 / 1000000000) (-1068201421 / 1000000000) x134 := by
    exact bounds_log hx133 (by norm_num) (by simpa only [div_one] using reflection_log_12.1) (by simpa only [div_one] using reflection_log_12.2)
  let x135 : ℝ := x130*x134
  have hx135 : Bounds (-18353089109 / 50000000000) (-91765445373 / 250000000000) x135 := by
    apply bounds_mul hx130 hx134 <;> norm_num
  let x136 : ℝ := x127+x135
  have hx136 : Bounds (468795678767 / 1000000000000) (58599460139 / 125000000000) x136 := by
    apply bounds_add hx127 hx135 <;> norm_num
  let x137 : ℝ := (2 / 1)⁻¹
  have hx137 : Bounds (1 / 2) (1 / 2) x137 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x138 : ℝ := x136*x137
  have hx138 : Bounds (234397839383 / 1000000000000) (58599460139 / 250000000000) x138 := by
    apply bounds_mul hx136 hx137 <;> norm_num
  let x139 : ℝ := x136/(2 / 1)
  have hx139 : Bounds (234397839383 / 1000000000000) (58599460139 / 250000000000) x139 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx138
  let x140 : ℝ := -x139
  have hx140 : Bounds (-58599460139 / 250000000000) (-234397839383 / 1000000000000) x140 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx139
  let x141 : ℝ := x123+x140
  have hx141 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x141 := by
    apply bounds_add hx123 hx140 <;> norm_num
  let x142 : ℝ := x123-x139
  have hx142 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x142 := by
    exact hx141
  let x143 : ℝ := biasE (328187 / 500000)
  have hx143 : Bounds (114687334861 / 250000000000) (458749341617 / 1000000000000) x143 := by
    simpa +zetaDelta only [biasE, div_one] using hx142
  let x144 : ℝ := Real.log (2 / 1)
  have hx144 : Bounds (34657359 / 50000000) (693147181 / 1000000000) x144 := by
    exact bounds_log (bounds_const ((2 / 1) : ℝ)) (by norm_num) (by simpa only [div_one] using reflection_log_0.1) (by simpa only [div_one] using reflection_log_0.2)
  let x145 : ℝ := (1 / 1)+(658929 / 1000000)
  have hx145 : Bounds (1658929 / 1000000) (1658929 / 1000000) x145 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let x146 : ℝ := (1 / 1)+(658929 / 1000000)
  have hx146 : Bounds (1658929 / 1000000) (1658929 / 1000000) x146 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let x147 : ℝ := Real.log x146
  have hx147 : Bounds (506172213 / 1000000000) (253086107 / 500000000) x147 := by
    exact bounds_log hx146 (by norm_num) (by simpa only [div_one] using reflection_log_13.1) (by simpa only [div_one] using reflection_log_13.2)
  let x148 : ℝ := x145*x147
  have hx148 : Bounds (839703763139 / 1000000000000) (839703764799 / 1000000000000) x148 := by
    apply bounds_mul hx145 hx147 <;> norm_num
  let x149 : ℝ := -(658929 / 1000000)
  have hx149 : Bounds (-658929 / 1000000) (-658929 / 1000000) x149 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((658929 / 1000000) : ℝ))
  let x150 : ℝ := (1 / 1)+x149
  have hx150 : Bounds (341071 / 1000000) (341071 / 1000000) x150 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx149 <;> norm_num
  let x151 : ℝ := (1 / 1)-(658929 / 1000000)
  have hx151 : Bounds (341071 / 1000000) (341071 / 1000000) x151 := by
    exact hx150
  let x152 : ℝ := -(658929 / 1000000)
  have hx152 : Bounds (-658929 / 1000000) (-658929 / 1000000) x152 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg (bounds_const ((658929 / 1000000) : ℝ))
  let x153 : ℝ := (1 / 1)+x152
  have hx153 : Bounds (341071 / 1000000) (341071 / 1000000) x153 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx152 <;> norm_num
  let x154 : ℝ := (1 / 1)-(658929 / 1000000)
  have hx154 : Bounds (341071 / 1000000) (341071 / 1000000) x154 := by
    exact hx153
  let x155 : ℝ := Real.log x154
  have hx155 : Bounds (-1075664613 / 1000000000) (-1075664611 / 1000000000) x155 := by
    exact bounds_log hx154 (by norm_num) (by simpa only [div_one] using reflection_log_14.1) (by simpa only [div_one] using reflection_log_14.2)
  let x156 : ℝ := x151*x155
  have hx156 : Bounds (-366878005221 / 1000000000000) (-183439002269 / 500000000000) x156 := by
    apply bounds_mul hx151 hx155 <;> norm_num
  let x157 : ℝ := x148+x156
  have hx157 : Bounds (236412878959 / 500000000000) (472825760261 / 1000000000000) x157 := by
    apply bounds_add hx148 hx156 <;> norm_num
  let x158 : ℝ := (2 / 1)⁻¹
  have hx158 : Bounds (1 / 2) (1 / 2) x158 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x159 : ℝ := x157*x158
  have hx159 : Bounds (236412878959 / 1000000000000) (236412880131 / 1000000000000) x159 := by
    apply bounds_mul hx157 hx158 <;> norm_num
  let x160 : ℝ := x157/(2 / 1)
  have hx160 : Bounds (236412878959 / 1000000000000) (236412880131 / 1000000000000) x160 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx159
  let x161 : ℝ := -x160
  have hx161 : Bounds (-236412880131 / 1000000000000) (-236412878959 / 1000000000000) x161 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx160
  let x162 : ℝ := x144+x161
  have hx162 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x162 := by
    apply bounds_add hx144 hx161 <;> norm_num
  let x163 : ℝ := x144-x160
  have hx163 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x163 := by
    exact hx162
  let x164 : ℝ := biasE (658929 / 1000000)
  have hx164 : Bounds (456734299869 / 1000000000000) (456734302041 / 1000000000000) x164 := by
    simpa +zetaDelta only [biasE, div_one] using hx163
  let x165 : ℝ := x122*(328187 / 500000)
  have hx165 : Bounds (3639710297 / 8000000000) (14335879037 / 31250000000) x165 := by
    apply bounds_mul hx122 (bounds_const ((328187 / 500000) : ℝ)) <;> norm_num
  let x166 : ℝ := x122*(658929 / 1000000)
  have hx166 : Bounds (45673477817 / 100000000000) (9210677023 / 20000000000) x166 := by
    apply bounds_mul hx122 (bounds_const ((658929 / 1000000) : ℝ)) <;> norm_num
  let c : ℝ := Reflection.regularContact (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hcMem := Reflection.regularContact_mem
    (x3 / (Real.log 2 * ((1 + H (2*m - 1/2))/2)))
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    apply GeneralCK.Certificates.RegularContactBounds.regularContact_nonneg
    rw [hLh']
    exact div_nonneg (by linarith [hx3.1]) (by linarith [hx77.1])
  have hcEq : biasE c = x122 * c := by
    have he := Reflection.regularContact_equation (x3 / x77)
    have hcdef : c = Reflection.regularContact (x3 / x77) := by
      dsimp only [c]
      rw [hLh']
    rw [← hcdef] at he
    change biasE c = (x77 / x3) * c
    have hx0 : 0 < x3 := by linarith [hx3.1]
    have hh0 : 0 < x77 := by linarith [hx77.1]
    field_simp [hx0.ne', hh0.ne'] at he ⊢
    nlinarith
  have hc : Bounds (328187 / 500000) (658929 / 1000000) c := by
    apply contact_bracket hc0 hcMem.2.le (by norm_num) (by norm_num) (by norm_num)
      (show 0 < x122 by linarith [hx122.1]) hcEq
    · have h1 : x122 * (328187 / 500000) ≤ (14335879037 / 31250000000) := hx165.2
      have h2 : (114687334861 / 250000000000) ≤ biasE (328187 / 500000) := hx143.1
      linarith
    · have h1 : biasE (658929 / 1000000) ≤ (456734302041 / 1000000000000) := hx164.2
      have h2 : (45673477817 / 100000000000) ≤ x122 * (658929 / 1000000) := hx166.1
      linarith
  let x167 : ℝ := (1 / 1)+y
  have hx167 : Bounds (1777571 / 1000000) (355989 / 200000) x167 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hy <;> norm_num
  let x168 : ℝ := -y
  have hx168 : Bounds (-155989 / 200000) (-777571 / 1000000) x168 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hy
  let x169 : ℝ := (1 / 1)+x168
  have hx169 : Bounds (44011 / 200000) (222429 / 1000000) x169 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx168 <;> norm_num
  let x170 : ℝ := (1 / 1)-y
  have hx170 : Bounds (44011 / 200000) (222429 / 1000000) x170 := by
    exact hx169
  let x171 : ℝ := x170⁻¹
  have hx171 : Bounds (2247908321307 / 500000000000) (4544318465839 / 1000000000000) x171 := by
    apply bounds_inv hx170 <;> norm_num
  let x172 : ℝ := x167*x171
  have hx172 : Bounds (1997908321307 / 250000000000) (4044318465839 / 500000000000) x172 := by
    apply bounds_mul hx167 hx171 <;> norm_num
  let x173 : ℝ := x167/x170
  have hx173 : Bounds (1997908321307 / 250000000000) (4044318465839 / 500000000000) x173 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx172
  let x174 : ℝ := Real.log x173
  have hx174 : Bounds (2078395153 / 1000000000) (2090460231 / 1000000000) x174 := by
    exact bounds_log hx173 (by norm_num) (by simpa only [div_one] using reflection_log_15.1) (by simpa only [div_one] using reflection_log_16.2)
  let x175 : ℝ := (2 / 1)⁻¹
  have hx175 : Bounds (1 / 2) (1 / 2) x175 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x176 : ℝ := x174*x175
  have hx176 : Bounds (2078395153 / 2000000000) (2090460231 / 2000000000) x176 := by
    apply bounds_mul hx174 hx175 <;> norm_num
  let x177 : ℝ := x174/(2 / 1)
  have hx177 : Bounds (2078395153 / 2000000000) (2090460231 / 2000000000) x177 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx176
  let x178 : ℝ := (1 / 1)+c
  have hx178 : Bounds (828187 / 500000) (1658929 / 1000000) x178 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hc <;> norm_num
  let x179 : ℝ := -c
  have hx179 : Bounds (-658929 / 1000000) (-328187 / 500000) x179 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hc
  let x180 : ℝ := (1 / 1)+x179
  have hx180 : Bounds (341071 / 1000000) (171813 / 500000) x180 := by
    apply bounds_add (bounds_const ((1 / 1) : ℝ)) hx179 <;> norm_num
  let x181 : ℝ := (1 / 1)-c
  have hx181 : Bounds (341071 / 1000000) (171813 / 500000) x181 := by
    exact hx180
  let x182 : ℝ := x181⁻¹
  have hx182 : Bounds (14550703381 / 5000000000) (293194085689 / 100000000000) x182 := by
    apply bounds_inv hx181 <;> norm_num
  let x183 : ℝ := x178*x182
  have hx183 : Bounds (12050703381 / 2500000000) (243194085689 / 50000000000) x183 := by
    apply bounds_mul hx178 hx182 <;> norm_num
  let x184 : ℝ := x178/x181
  have hx184 : Bounds (12050703381 / 2500000000) (243194085689 / 50000000000) x184 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx183
  let x185 : ℝ := Real.log x184
  have hx185 : Bounds (1572832297 / 1000000000) (1581836827 / 1000000000) x185 := by
    exact bounds_log hx184 (by norm_num) (by simpa only [div_one] using reflection_log_17.1) (by simpa only [div_one] using reflection_log_18.2)
  let x186 : ℝ := (2 / 1)⁻¹
  have hx186 : Bounds (1 / 2) (1 / 2) x186 := by
    apply bounds_inv (bounds_const ((2 / 1) : ℝ)) <;> norm_num
  let x187 : ℝ := x185*x186
  have hx187 : Bounds (1572832297 / 2000000000) (1581836827 / 2000000000) x187 := by
    apply bounds_mul hx185 hx186 <;> norm_num
  let x188 : ℝ := x185/(2 / 1)
  have hx188 : Bounds (1572832297 / 2000000000) (1581836827 / 2000000000) x188 := by
    simpa +zetaDelta only [div_eq_mul_inv] using hx187
  let x189 : ℝ := (2 / 1)*x50
  have hx189 : Bounds (2249340573 / 2000000000) (35166048499 / 31250000000) x189 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx50 <;> norm_num
  let x190 : ℝ := (2 / 1)*x77
  have hx190 : Bounds (34657359 / 50000000) (69809366873 / 100000000000) x190 := by
    apply bounds_mul (bounds_const ((2 / 1) : ℝ)) hx77 <;> norm_num
  let x191 : ℝ := -x190
  have hx191 : Bounds (-69809366873 / 100000000000) (-34657359 / 50000000) x191 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx190
  let x192 : ℝ := x189+x191
  have hx192 : Bounds (42657661777 / 100000000000) (3376299781 / 7812500000) x192 := by
    apply bounds_add hx189 hx191 <;> norm_num
  let x193 : ℝ := x189-x190
  have hx193 : Bounds (42657661777 / 100000000000) (3376299781 / 7812500000) x193 := by
    exact hx192
  let x194 : ℝ := y*x177
  have hx194 : Bounds (202012474689 / 250000000000) (407611001217 / 500000000000) x194 := by
    apply bounds_mul hy hx177 <;> norm_num
  let x195 : ℝ := -x194
  have hx195 : Bounds (-407611001217 / 500000000000) (-202012474689 / 250000000000) x195 := by
    simpa only [neg_div, neg_neg, zero_div, neg_zero] using bounds_neg hx194
  let x196 : ℝ := x193+x195
  have hx196 : Bounds (-48580673083 / 125000000000) (-93970881697 / 250000000000) x196 := by
    apply bounds_add hx193 hx195 <;> norm_num
  let x197 : ℝ := x193-x194
  have hx197 : Bounds (-48580673083 / 125000000000) (-93970881697 / 250000000000) x197 := by
    exact hx196
  let x198 : ℝ := x3*x188
  have hx198 : Bounds (392747283537 / 1000000000000) (1581836827 / 4000000000) x198 := by
    apply bounds_mul hx3 hx188 <;> norm_num
  let x199 : ℝ := x197+x198
  have hx199 : Bounds (4101898873 / 1000000000000) (9787839981 / 500000000000) x199 := by
    apply bounds_add hx197 hx198 <;> norm_num
  have hpos : 0 < x199 := lt_of_lt_of_le (by norm_num) hx199.1
  have hcert :
      0 ≤ 2 * biasE (1 - 2*m) - 2*(x77)
        - (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2)) *
            SmallMean.A (1 - 2*entropyInverse ((1 + H (2*m - 1/2))/2))
        + (1 - 2*m) *
            SmallMean.A (regularContact ((1 - 2*m)/(Real.log 2*((1 + H (2*m - 1/2))/2)))) := by
    simpa +zetaDelta only [SmallMean.A, div_one] using hpos.le
  dsimp only
  nlinarith [hcert, hLh]

theorem acceptedCertificate : DoubleCapBiasCellCertificate (1 / 4) (2563 / 10240) (fun m => (1 + H (2*m - 1/2))/2) where
  domain := by norm_num
  sound m hmLo hmHi := by
    exact cell_bias_nonneg m ⟨hmLo, hmHi⟩

theorem accepted_cell :
    ∀ m, (1 / 4) ≤ m → m ≤ (2563 / 10240) → 0 ≤ doubleCapHighResidual m := by
  intro m hmLo hmHi
  unfold doubleCapHighResidual
  apply doubleCapEndpointResidual_nonneg_of_biasCell acceptedCertificate hmLo hmHi
  exact div_pos (by linarith [H_nonneg (by linarith : 0 ≤ 2*m-1/2) (by linarith : 2*m-1/2 ≤ 1)]) two_pos

#print axioms cell_bias_nonneg
#print axioms accepted_cell

end GeneralCK.Certificates.DoubleCapMiddle.Cell0010

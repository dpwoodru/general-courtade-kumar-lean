import GeneralCK.Certificates.DyadicFastLog
import GeneralCK.Certificates.BivariateProvedProgram
import GeneralCK.CorrectionHessianNatural
import GeneralCK.Certificates.CorrectionFactorizedProgramKernel
import GeneralCK.CorrectionInteriorRatioBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LaneCBRB2Cell002433Endpoints
open GeneralCK.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo*16777216, a.hi*16777216⟩

theorem lift40_contains {a : DyadicInterval 40} {x : ℝ} :
    (lift40 a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift40, Int.cast_mul, Int.cast_ofNat]
  norm_num [DyadicInterval.scale]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem direct {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check z 1099511627776 e n (lift40 a)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  apply lift40_contains.mp
  simpa only [Int.cast_ofNat] using DyadicFastLog.check_sound hc

theorem reciprocal {z : ℤ} {e n : ℕ} {a : DyadicInterval 40}
    (hc : DyadicFastLog.check 1099511627776 z e n (lift40 a.neg)=true) :
    a.Contains (Real.log ((z:ℝ)/1099511627776)) := by
  have h := lift40_contains.mp (DyadicFastLog.check_sound hc)
  have hn := DyadicInterval.neg_sound h
  rw [← Real.log_inv, inv_div] at hn
  simpa only [DyadicInterval.neg, neg_neg, Int.cast_ofNat] using hn

noncomputable def sharedTwo : DyadicInterval 64 := ⟨12786308645202655420,12786308645202662926⟩
theorem sharedTwo_eq : DyadicLogSeries.enclosure (DyadicFastLog.fraction 64 1 3) 16=sharedTwo := by rfl
noncomputable def out_w0 : DyadicInterval 40 := ⟨-2186270971968,-2186270931392⟩
theorem checked_w0 : DyadicFastLog.check 150538603724 1099511627776 2 16 (lift40 out_w0)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w0 : out_w0.Contains (Real.log ((150538603724:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w0
#print axioms endpoint_w0
noncomputable def out_w1 : DyadicInterval 40 := ⟨-2186270971968,-2186270931392⟩
theorem checked_w1 : DyadicFastLog.check 150538603725 1099511627776 2 16 (lift40 out_w1)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w1 : out_w1.Contains (Real.log ((150538603725:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w1
#print axioms endpoint_w1
noncomputable def out_w2 : DyadicInterval 40 := ⟨-161893205824,-161893205760⟩
theorem checked_w2 : DyadicFastLog.check 948973024051 1099511627776 0 16 (lift40 out_w2)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w2 : out_w2.Contains (Real.log ((948973024051:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w2
#print axioms endpoint_w2
noncomputable def out_w3 : DyadicInterval 40 := ⟨-161893205824,-161893205760⟩
theorem checked_w3 : DyadicFastLog.check 948973024052 1099511627776 0 16 (lift40 out_w3)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w3 : out_w3.Contains (Real.log ((948973024052:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w3
#print axioms endpoint_w3
noncomputable def out_w4 : DyadicInterval 40 := ⟨-1783561752704,-1783561714112⟩
theorem checked_w4 : DyadicFastLog.check 217126786825 1099511627776 2 16 (lift40 out_w4)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w4 : out_w4.Contains (Real.log ((217126786825:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w4
#print axioms endpoint_w4
noncomputable def out_w5 : DyadicInterval 40 := ⟨-1783561752704,-1783561714112⟩
theorem checked_w5 : DyadicFastLog.check 217126786827 1099511627776 2 16 (lift40 out_w5)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w5 : out_w5.Contains (Real.log ((217126786827:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w5
#print axioms endpoint_w5
noncomputable def out_w6 : DyadicInterval 40 := ⟨-241884968192,-241884968128⟩
theorem checked_w6 : DyadicFastLog.check 882384840949 1099511627776 0 16 (lift40 out_w6)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w6 : out_w6.Contains (Real.log ((882384840949:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w6
#print axioms endpoint_w6
noncomputable def out_w7 : DyadicInterval 40 := ⟨-241884968192,-241884968128⟩
theorem checked_w7 : DyadicFastLog.check 882384840951 1099511627776 0 16 (lift40 out_w7)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w7 : out_w7.Contains (Real.log ((882384840951:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w7
#print axioms endpoint_w7
noncomputable def out_w8 : DyadicInterval 40 := ⟨762123383616,762123402880⟩
theorem checked_w8 : DyadicFastLog.check 1099511627776 2199023255552 1 16 (lift40 out_w8.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w8 : out_w8.Contains (Real.log ((2199023255552:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w8
#print axioms endpoint_w8
noncomputable def out_w9 : DyadicInterval 40 := ⟨97869117248,97869117312⟩
theorem checked_w9 : DyadicFastLog.check 1099511627776 1201868645376 0 16 (lift40 out_w9.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w9 : out_w9.Contains (Real.log ((1201868645376:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w9
#print axioms endpoint_w9
noncomputable def out_w10 : DyadicInterval 40 := ⟨-107439385792,-107439385728⟩
theorem checked_w10 : DyadicFastLog.check 997154610176 1099511627776 0 16 (lift40 out_w10)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w10 : out_w10.Contains (Real.log ((997154610176:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w10
#print axioms endpoint_w10
noncomputable def out_w11 : DyadicInterval 40 := ⟨97869239232,97869239296⟩
theorem checked_w11 : DyadicFastLog.check 1099511627776 1201868778752 0 16 (lift40 out_w11.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w11 : out_w11.Contains (Real.log ((1201868778752:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w11
#print axioms endpoint_w11
noncomputable def out_w12 : DyadicInterval 40 := ⟨-107439532864,-107439532800⟩
theorem checked_w12 : DyadicFastLog.check 997154476800 1099511627776 0 16 (lift40 out_w12)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w12 : out_w12.Contains (Real.log ((997154476800:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w12
#print axioms endpoint_w12
noncomputable def out_w13 : DyadicInterval 40 := ⟨-9570293568,-9570293504⟩
theorem checked_w13 : DyadicFastLog.check 1089982864194 1099511627776 0 16 (lift40 out_w13)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w13 : out_w13.Contains (Real.log ((1089982864194:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w13
#print axioms endpoint_w13
noncomputable def out_w14 : DyadicInterval 40 := ⟨-9570268544,-9570268480⟩
theorem checked_w14 : DyadicFastLog.check 1089982889028 1099511627776 0 16 (lift40 out_w14)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w14 : out_w14.Contains (Real.log ((1089982889028:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w14
#print axioms endpoint_w14
noncomputable def out_w15 : DyadicInterval 40 := ⟨205308502976,205308503040⟩
theorem checked_w15 : DyadicFastLog.check 1099511627776 1325239373276 0 16 (lift40 out_w15.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w15 : out_w15.Contains (Real.log ((1325239373276:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w15
#print axioms endpoint_w15
noncomputable def out_w16 : DyadicInterval 40 := ⟨205308772096,205308772160⟩
theorem checked_w16 : DyadicFastLog.check 1099511627776 1325239697604 0 16 (lift40 out_w16.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w16 : out_w16.Contains (Real.log ((1325239697604:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w16
#print axioms endpoint_w16
noncomputable def out_w17 : DyadicInterval 40 := ⟨2024377725696,2024377764352⟩
theorem checked_w17 : DyadicFastLog.check 1099511627776 6931158178508 2 16 (lift40 out_w17.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w17 : out_w17.Contains (Real.log ((6931158178508:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w17
#print axioms endpoint_w17
noncomputable def out_w18 : DyadicInterval 40 := ⟨2024377725760,2024377764352⟩
theorem checked_w18 : DyadicFastLog.check 1099511627776 6931158178563 2 16 (lift40 out_w18.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w18 : out_w18.Contains (Real.log ((6931158178563:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w18
#print axioms endpoint_w18
noncomputable def out_w19 : DyadicInterval 40 := ⟨1541676745920,1541676784512⟩
theorem checked_w19 : DyadicFastLog.check 1099511627776 4468321974338 2 16 (lift40 out_w19.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w19 : out_w19.Contains (Real.log ((4468321974338:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w19
#print axioms endpoint_w19
noncomputable def out_w20 : DyadicInterval 40 := ⟨1541676745984,1541676784576⟩
theorem checked_w20 : DyadicFastLog.check 1099511627776 4468321974391 2 16 (lift40 out_w20.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w20 : out_w20.Contains (Real.log ((4468321974391:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w20
#print axioms endpoint_w20
noncomputable def out_w21 : DyadicInterval 40 := ⟨-2187840582080,-2187840541376⟩
theorem checked_w21 : DyadicFastLog.check 150323855360 1099511627776 2 16 (lift40 out_w21)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w21 : out_w21.Contains (Real.log ((150323855360:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w21
#print axioms endpoint_w21
noncomputable def out_w22 : DyadicInterval 40 := ⟨-2184703599360,-2184703558912⟩
theorem checked_w22 : DyadicFastLog.check 150753352090 1099511627776 2 16 (lift40 out_w22)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w22 : out_w22.Contains (Real.log ((150753352090:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w22
#print axioms endpoint_w22
noncomputable def out_w23 : DyadicInterval 40 := ⟨-162142048512,-162142048448⟩
theorem checked_w23 : DyadicFastLog.check 948758275686 1099511627776 0 16 (lift40 out_w23)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w23 : out_w23.Contains (Real.log ((948758275686:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w23
#print axioms endpoint_w23
noncomputable def out_w24 : DyadicInterval 40 := ⟨-161644419392,-161644419328⟩
theorem checked_w24 : DyadicFastLog.check 949187772416 1099511627776 0 16 (lift40 out_w24)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w24 : out_w24.Contains (Real.log ((949187772416:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w24
#print axioms endpoint_w24
noncomputable def out_w25 : DyadicInterval 40 := ⟨-1791966016000,-1791965977408⟩
theorem checked_w25 : DyadicFastLog.check 215473476075 1099511627776 2 16 (lift40 out_w25)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w25 : out_w25.Contains (Real.log ((215473476075:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w25
#print axioms endpoint_w25
noncomputable def out_w26 : DyadicInterval 40 := ⟨-1775213653120,-1775213614528⟩
theorem checked_w26 : DyadicFastLog.check 218781607527 1099511627776 2 16 (lift40 out_w26)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w26 : out_w26.Contains (Real.log ((218781607527:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w26
#print axioms endpoint_w26
noncomputable def out_w27 : DyadicInterval 40 := ⟨-243948923520,-243948923456⟩
theorem checked_w27 : DyadicFastLog.check 880730020249 1099511627776 0 16 (lift40 out_w27)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w27 : out_w27.Contains (Real.log ((880730020249:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w27
#print axioms endpoint_w27
noncomputable def out_w28 : DyadicInterval 40 := ⟨-239826758016,-239826757952⟩
theorem checked_w28 : DyadicFastLog.check 884038151701 1099511627776 0 16 (lift40 out_w28)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w28 : out_w28.Contains (Real.log ((884038151701:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w28
#print axioms endpoint_w28
noncomputable def out_w29 : DyadicInterval 40 := ⟨94609834752,94609834816⟩
theorem checked_w29 : DyadicFastLog.check 1099511627776 1198311221248 0 16 (lift40 out_w29.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w29 : out_w29.Contains (Real.log ((1198311221248:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w29
#print axioms endpoint_w29
noncomputable def out_w30 : DyadicInterval 40 := ⟨-103523775744,-103523775680⟩
theorem checked_w30 : DyadicFastLog.check 1000712034304 1099511627776 0 16 (lift40 out_w30)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w30 : out_w30.Contains (Real.log ((1000712034304:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w30
#print axioms endpoint_w30
noncomputable def out_w31 : DyadicInterval 40 := ⟨101159964224,101159964288⟩
theorem checked_w31 : DyadicFastLog.check 1099511627776 1205471236352 0 16 (lift40 out_w31.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w31 : out_w31.Contains (Real.log ((1205471236352:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w31
#print axioms endpoint_w31
noncomputable def out_w32 : DyadicInterval 40 := ⟨-111418972672,-111418972608⟩
theorem checked_w32 : DyadicFastLog.check 993552019200 1099511627776 0 16 (lift40 out_w32)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w32 : out_w32.Contains (Real.log ((993552019200:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w32
#print axioms endpoint_w32
noncomputable def out_w33 : DyadicInterval 40 := ⟨-10259008384,-10259008320⟩
theorem checked_w33 : DyadicFastLog.check 1089300331809 1099511627776 0 16 (lift40 out_w33)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w33 : out_w33.Contains (Real.log ((1089300331809:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w33
#print axioms endpoint_w33
noncomputable def out_w34 : DyadicInterval 40 := ⟨-8913940928,-8913940864⟩
theorem checked_w34 : DyadicFastLog.check 1090633722874 1099511627776 0 16 (lift40 out_w34)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w34 : out_w34.Contains (Real.log ((1090633722874:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using direct checked_w34
#print axioms endpoint_w34
noncomputable def out_w35 : DyadicInterval 40 := ⟨198133610496,198133610560⟩
theorem checked_w35 : DyadicFastLog.check 1099511627776 1316619643104 0 16 (lift40 out_w35.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w35 : out_w35.Contains (Real.log ((1316619643104:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w35
#print axioms endpoint_w35
noncomputable def out_w36 : DyadicInterval 40 := ⟨212578936896,212578936960⟩
theorem checked_w36 : DyadicFastLog.check 1099511627776 1334031450498 0 16 (lift40 out_w36.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w36 : out_w36.Contains (Real.log ((1334031450498:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w36
#print axioms endpoint_w36
noncomputable def out_w37 : DyadicInterval 40 := ⟨2022561510464,2022561549120⟩
theorem checked_w37 : DyadicFastLog.check 1099511627776 6919718477919 2 16 (lift40 out_w37.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w37 : out_w37.Contains (Real.log ((6919718477919:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w37
#print axioms endpoint_w37
noncomputable def out_w38 : DyadicInterval 40 := ⟨2026196122176,2026196160768⟩
theorem checked_w38 : DyadicFastLog.check 1099511627776 6942630563958 2 16 (lift40 out_w38.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w38 : out_w38.Contains (Real.log ((6942630563958:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w38
#print axioms endpoint_w38
noncomputable def out_w39 : DyadicInterval 40 := ⟨1531264691072,1531264729664⟩
theorem checked_w39 : DyadicFastLog.check 1099511627776 4426207984945 2 16 (lift40 out_w39.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w39 : out_w39.Contains (Real.log ((4426207984945:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w39
#print axioms endpoint_w39
noncomputable def out_w40 : DyadicInterval 40 := ⟨1552139219392,1552139257984⟩
theorem checked_w40 : DyadicFastLog.check 1099511627776 4511043516347 2 16 (lift40 out_w40.neg)=true := by
  simp only [DyadicFastLog.check,DyadicFastLog.approximation,sharedTwo_eq]
  decide
theorem endpoint_w40 : out_w40.Contains (Real.log ((4511043516347:ℝ)/1099511627776)) := by
  simpa only [Int.cast_ofNat] using reciprocal checked_w40
#print axioms endpoint_w40
end LaneCBRB2Cell002433Endpoints

namespace GeneralCK.Certificates.LaneCB.RB2Cell002433
open Set LaneCBRB2Cell002433Endpoints
open BivariateJetProgram (RegistersContain RegistersSound zeroBox zeroJet)
open BivariateProvedProgram
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem lc0 : ProvedTranscendental.LogEncloses (⟨150538603724,150538603725⟩ : DyadicInterval 40) (⟨-2186270971968,-2186270931392⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w0
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w1
theorem lc1 : ProvedTranscendental.LogEncloses (⟨948973024051,948973024052⟩ : DyadicInterval 40) (⟨-161893205824,-161893205760⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w2
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w3
theorem lc2 : ProvedTranscendental.LogEncloses (⟨217126786825,217126786827⟩ : DyadicInterval 40) (⟨-1783561752704,-1783561714112⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w4
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w5
theorem lc3 : ProvedTranscendental.LogEncloses (⟨882384840949,882384840951⟩ : DyadicInterval 40) (⟨-241884968192,-241884968128⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w6
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w7
theorem lc4 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc5 : ProvedTranscendental.LogEncloses (⟨1201868645376,1201868645376⟩ : DyadicInterval 40) (⟨97869117248,97869117312⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
theorem lc6 : ProvedTranscendental.LogEncloses (⟨997154610176,997154610176⟩ : DyadicInterval 40) (⟨-107439385792,-107439385728⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc7 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc8 : ProvedTranscendental.LogEncloses (⟨1201868778752,1201868778752⟩ : DyadicInterval 40) (⟨97869239232,97869239296⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc9 : ProvedTranscendental.LogEncloses (⟨997154476800,997154476800⟩ : DyadicInterval 40) (⟨-107439532864,-107439532800⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
theorem lc10 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc11 : ProvedTranscendental.LogEncloses (⟨1089982864194,1089982889028⟩ : DyadicInterval 40) (⟨-9570293568,-9570268480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc12 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc13 : ProvedTranscendental.LogEncloses (⟨1201868645376,1201868778752⟩ : DyadicInterval 40) (⟨97869117248,97869239296⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w9
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w11
theorem lc14 : ProvedTranscendental.LogEncloses (⟨997154476800,997154610176⟩ : DyadicInterval 40) (⟨-107439532864,-107439385728⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w12
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w10
theorem lc15 : ProvedTranscendental.LogEncloses (⟨1089982864194,1089982889028⟩ : DyadicInterval 40) (⟨-9570293568,-9570268480⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w13
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w14
theorem lc16 : ProvedTranscendental.LogEncloses (⟨1325239373276,1325239697604⟩ : DyadicInterval 40) (⟨205308502976,205308772160⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w15
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w16
theorem lc17 : ProvedTranscendental.LogEncloses (⟨6931158178508,6931158178563⟩ : DyadicInterval 40) (⟨2024377725696,2024377764352⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w17
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w18
theorem lc18 : ProvedTranscendental.LogEncloses (⟨4468321974338,4468321974391⟩ : DyadicInterval 40) (⟨1541676745920,1541676784576⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w19
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w20
theorem lc19 : ProvedTranscendental.LogEncloses (⟨150323855360,150753352090⟩ : DyadicInterval 40) (⟨-2187840582080,-2184703558912⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w21
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w22
theorem lc20 : ProvedTranscendental.LogEncloses (⟨948758275686,949187772416⟩ : DyadicInterval 40) (⟨-162142048512,-161644419328⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w23
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w24
theorem lc21 : ProvedTranscendental.LogEncloses (⟨215473476075,218781607527⟩ : DyadicInterval 40) (⟨-1791966016000,-1775213614528⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w25
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w26
theorem lc22 : ProvedTranscendental.LogEncloses (⟨880730020249,884038151701⟩ : DyadicInterval 40) (⟨-243948923520,-239826757952⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w27
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w28
theorem lc23 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc24 : ProvedTranscendental.LogEncloses (⟨1198311221248,1198311221248⟩ : DyadicInterval 40) (⟨94609834752,94609834816⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
theorem lc25 : ProvedTranscendental.LogEncloses (⟨1000712034304,1000712034304⟩ : DyadicInterval 40) (⟨-103523775744,-103523775680⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc26 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc27 : ProvedTranscendental.LogEncloses (⟨1205471236352,1205471236352⟩ : DyadicInterval 40) (⟨101159964224,101159964288⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc28 : ProvedTranscendental.LogEncloses (⟨993552019200,993552019200⟩ : DyadicInterval 40) (⟨-111418972672,-111418972608⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
theorem lc29 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc30 : ProvedTranscendental.LogEncloses (⟨1089300331809,1090633722874⟩ : DyadicInterval 40) (⟨-10259008384,-8913940864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc31 : ProvedTranscendental.LogEncloses (⟨2199023255552,2199023255552⟩ : DyadicInterval 40) (⟨762123383616,762123402880⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w8
theorem lc32 : ProvedTranscendental.LogEncloses (⟨1198311221248,1205471236352⟩ : DyadicInterval 40) (⟨94609834752,101159964288⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w29
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w31
theorem lc33 : ProvedTranscendental.LogEncloses (⟨993552019200,1000712034304⟩ : DyadicInterval 40) (⟨-111418972672,-103523775680⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w32
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w30
theorem lc34 : ProvedTranscendental.LogEncloses (⟨1089300331809,1090633722874⟩ : DyadicInterval 40) (⟨-10259008384,-8913940864⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w33
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w34
theorem lc35 : ProvedTranscendental.LogEncloses (⟨1316619643104,1334031450498⟩ : DyadicInterval 40) (⟨198133610496,212578936960⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w35
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w36
theorem lc36 : ProvedTranscendental.LogEncloses (⟨6919718477919,6942630563958⟩ : DyadicInterval 40) (⟨2022561510464,2026196160768⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w37
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w38
theorem lc37 : ProvedTranscendental.LogEncloses (⟨4426207984945,4511043516347⟩ : DyadicInterval 40) (⟨1531264691072,1552139257984⟩ : DyadicInterval 40) := by
  apply ProvedTranscendental.log_of_endpoints (by decide)
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w39
  · exact DyadicInterval.subsetCheck_sound (by decide) endpoint_w40
theorem ew11_ok (x : ℝ) (hx : (⟨102357017600,102357017600⟩ : DyadicInterval 40).Contains x) : (⟨757352108628,757352127958⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨102357017600,102357017600⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨97869117248,97869117312⟩ : DyadicInterval 40)) (minus:=(⟨-107439385792,-107439385728⟩ : DyadicInterval 40))
    (lc4 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc5 lc6 (by decide) hx
theorem ew14_ok (x : ℝ) (hx : (⟨102357150976,102357150976⟩ : DyadicInterval 40).Contains x) : (⟨757352096196,757352115526⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨102357150976,102357150976⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨97869239232,97869239296⟩ : DyadicInterval 40)) (minus:=(⟨-107439532864,-107439532800⟩ : DyadicInterval 40))
    (lc7 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc8 lc9 (by decide) hx
theorem ew35_ok (x : ℝ) (hx : (⟨98799593472,98799593472⟩ : DyadicInterval 40).Contains x) : (⟨757678438108,757678457437⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨98799593472,98799593472⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨94609834752,94609834816⟩ : DyadicInterval 40)) (minus:=(⟨-103523775744,-103523775680⟩ : DyadicInterval 40))
    (lc23 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc24 lc25 (by decide) hx
theorem ew38_ok (x : ℝ) (hx : (⟨105959608576,105959608576⟩ : DyadicInterval 40).Contains x) : (⟨757009803311,757009822641⟩ : DyadicInterval 40).Contains (Reflection.biasE x) := by
  exact ProvedTranscendental.entropy_encloses (c:=(⟨105959608576,105959608576⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (plus:=(⟨101159964224,101159964288⟩ : DyadicInterval 40)) (minus:=(⟨-111418972672,-111418972608⟩ : DyadicInterval 40))
    (lc26 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc27 lc28 (by decide) hx
theorem bw17_ok (x : ℝ) (hx : (⟨102357017600,102357150976⟩ : DyadicInterval 40).Contains x) : (⟨766908517856,766908549664⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨102357017600,102357150976⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-9570293568,-9570268480⟩ : DyadicInterval 40))
    (lc10 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc11 (by decide) hx
theorem bw41_ok (x : ℝ) (hx : (⟨98799593472,105959608576⟩ : DyadicInterval 40).Contains x) : (⟨766580354048,767252907072⟩ : DyadicInterval 40).Contains (Reflection.biasB x) := by
  exact ProvedTranscendental.denominator_encloses (c:=(⟨98799593472,105959608576⟩ : DyadicInterval 40)) (two:=(⟨762123383616,762123402880⟩ : DyadicInterval 40)) (gapLog:=(⟨-10259008384,-8913940864⟩ : DyadicInterval 40))
    (lc29 2 (by norm_num [DyadicInterval.Contains,DyadicInterval.scale])) lc30 (by decide) hx
theorem brcenter28_contact (y : ℝ) (hy : (⟨8135415783586,8135415893710⟩ : DyadicInterval 40).Contains y) : (⟨102357017600,102357150976⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨8135415783586,8135415893710⟩ : DyadicInterval 40)) (c:=(⟨102357017600,102357150976⟩ : DyadicInterval 40)) (elo:=(⟨757352108628,757352127958⟩ : DyadicInterval 40)) (ehi:=(⟨757352096196,757352115526⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew11_ok _ (DyadicContact.point_contains 40 102357017600)) (ew14_ok _ (DyadicContact.point_contains 40 102357150976))
    (by decide) (by decide) hy
theorem brcenter28_jet (y : ℝ) (hy : (⟨8135415783586,8135415893710⟩ : DyadicInterval 40).Contains y) : (⟨⟨102357017600,102357150976⟩,⟨-13661324804,-13661288632⟩,⟨3623810769,3623825494⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨102357017600,102357150976⟩ : DyadicInterval 40)) (B:=(⟨766908517856,766908549664⟩ : DyadicInterval 40)) (by decide) brcenter28_contact bw17_ok (by decide) (by decide) (by decide) hy
theorem brwhole28_contact (y : ℝ) (hy : (⟨7855272646188,8431974827151⟩ : DyadicInterval 40).Contains y) : (⟨98799593472,105959608576⟩ : DyadicInterval 40).Contains (Reflection.biasContact y) := by
  exact ProvedTranscendental.contact_bracket (Y:=(⟨7855272646188,8431974827151⟩ : DyadicInterval 40)) (c:=(⟨98799593472,105959608576⟩ : DyadicInterval 40)) (elo:=(⟨757678438108,757678457437⟩ : DyadicInterval 40)) (ehi:=(⟨757009803311,757009822641⟩ : DyadicInterval 40))
    (by decide) (by decide) (by decide) (by decide)
    (ew35_ok _ (DyadicContact.point_contains 40 98799593472)) (ew38_ok _ (DyadicContact.point_contains 40 105959608576))
    (by decide) (by decide) hy
theorem brwhole28_jet (y : ℝ) (hy : (⟨7855272646188,8431974827151⟩ : DyadicInterval 40).Contains y) : (⟨⟨98799593472,105959608576⟩,⟨-14646134083,-12722479876⟩,⟨3249342385,4029776153⟩⟩ : DyadicJetEnclosure 40).Contains reflectionContactJet y := by
  exact ProvedTranscendental.contact_jet (c:=(⟨98799593472,105959608576⟩ : DyadicInterval 40)) (B:=(⟨766580354048,767252907072⟩ : DyadicInterval 40)) (by decide) brwhole28_contact bw41_ok (by decide) (by decide) (by decide) hy
noncomputable def centerInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨150538603724,150538603725⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨183395103539,183395103540⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def centerBoxes0 := centerInitial
noncomputable def centerStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes1 := centerStep0.proposed :: centerBoxes0
theorem centerAccepted0 : StepValid centerStep0.shape centerBoxes0 centerStep0.proposed := by
  dsimp only [StepValid,centerStep0]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes2 := centerStep1.proposed :: centerBoxes1
theorem centerAccepted1 : StepValid centerStep1.shape centerBoxes1 centerStep1.proposed := by
  dsimp only [StepValid,centerStep1]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-150538603725,-150538603724⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes3 := centerStep2.proposed :: centerBoxes2
theorem centerAccepted2 : StepValid centerStep2.shape centerBoxes2 centerStep2.proposed := by
  dsimp only [StepValid,centerStep2]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨399217210163,399217210164⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes4 := centerStep3.proposed :: centerBoxes3
theorem centerAccepted3 : StepValid centerStep3.shape centerBoxes3 centerStep3.proposed := by
  dsimp only [StepValid,centerStep3]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨66588183101,66588183102⟩,⟨-183395103540,-183395103539⟩,⟨399217210163,399217210164⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes5 := centerStep4.proposed :: centerBoxes4
theorem centerAccepted4 : StepValid centerStep4.shape centerBoxes4 centerStep4.proposed := by
  dsimp only [StepValid,centerStep4]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨217126786825,217126786827⟩,⟨916116524236,916116524237⟩,⟨399217210163,399217210164⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes6 := centerStep5.proposed :: centerBoxes5
theorem centerAccepted5 : StepValid centerStep5.shape centerBoxes5 centerStep5.proposed := by
  dsimp only [StepValid,centerStep5]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨66588183100,66588183103⟩,⟨-183395103540,-183395103539⟩,⟨399217210163,399217210164⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes7 := centerStep6.proposed :: centerBoxes6
theorem centerAccepted6 : StepValid centerStep6.shape centerBoxes6 centerStep6.proposed := by
  dsimp only [StepValid,centerStep6]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2186270971968,-2186270931392⟩,⟨8030669806284,8030669806339⟩,⟨0,0⟩,⟨-58654820839770,-58654820838966⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes8 := centerStep7.proposed :: centerBoxes7
theorem centerAccepted7 : StepValid centerStep7.shape centerBoxes7 centerStep7.proposed := by
  dsimp only [StepValid,centerStep7]
  exact ⟨by decide,by decide,lc0,by decide⟩
noncomputable def centerStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-299331240499,-299331234940⟩,⟨-1086759344200,-1086759303608⟩,⟨0,0⟩,⟨8030669806174,8030669806449⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes9 := centerStep8.proposed :: centerBoxes8
theorem centerAccepted8 : StepValid centerStep8.shape centerBoxes8 centerStep8.proposed := by
  dsimp only [StepValid,centerStep8]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep9 : Instruction 40 := ⟨.neg 0,⟨⟨299331234940,299331240499⟩,⟨1086759303608,1086759344200⟩,⟨0,0⟩,⟨-8030669806449,-8030669806174⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes10 := centerStep9.proposed :: centerBoxes9
theorem centerAccepted9 : StepValid centerStep9.shape centerBoxes9 centerStep9.proposed := by
  dsimp only [StepValid,centerStep9]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨948973024051,948973024052⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes11 := centerStep10.proposed :: centerBoxes10
theorem centerAccepted10 : StepValid centerStep10.shape centerBoxes10 centerStep10.proposed := by
  dsimp only [StepValid,centerStep10]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep11 : Instruction 40 := ⟨.log 0,⟨⟨-161893205824,-161893205760⟩,⟨-1273930648159,-1273930648157⟩,⟨0,0⟩,⟨-1476018311513,-1476018311508⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes12 := centerStep11.proposed :: centerBoxes11
theorem centerAccepted11 : StepValid centerStep11.shape centerBoxes11 centerStep11.proposed := by
  dsimp only [StepValid,centerStep11]
  exact ⟨by decide,by decide,lc1,by decide⟩
noncomputable def centerStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-139727749324,-139727749268⟩,⟨-937618422018,-937618421950⟩,⟨0,0⟩,⟨1273930648153,1273930648164⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes13 := centerStep12.proposed :: centerBoxes12
theorem centerAccepted12 : StepValid centerStep12.shape centerBoxes12 centerStep12.proposed := by
  dsimp only [StepValid,centerStep12]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep13 : Instruction 40 := ⟨.neg 0,⟨⟨139727749268,139727749324⟩,⟨937618421950,937618422018⟩,⟨0,0⟩,⟨-1273930648164,-1273930648153⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes14 := centerStep13.proposed :: centerBoxes13
theorem centerAccepted13 : StepValid centerStep13.shape centerBoxes13 centerStep13.proposed := by
  dsimp only [StepValid,centerStep13]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨439058984208,439058989823⟩,⟨2024377725558,2024377766218⟩,⟨0,0⟩,⟨-9304600454613,-9304600454327⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes15 := centerStep14.proposed :: centerBoxes14
theorem centerAccepted14 : StepValid centerStep14.shape centerBoxes14 centerStep14.proposed := by
  dsimp only [StepValid,centerStep14]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep15 : Instruction 40 := ⟨.log 9,⟨⟨-1783561752704,-1783561714112⟩,⟨4639136356757,4639136356807⟩,⟨2021602083266,2021602083291⟩,⟨-19573768565393,-19573768564975⟩,⟨-14097518497416,-14097518497168⟩,⟨-3716991143998,-3716991143908⟩⟩⟩
noncomputable def centerBoxes16 := centerStep15.proposed :: centerBoxes15
theorem centerAccepted15 : StepValid centerStep15.shape centerBoxes15 centerStep15.proposed := by
  dsimp only [StepValid,centerStep15]
  exact ⟨by decide,by decide,lc2,by decide⟩
noncomputable def centerStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-352210038248,-352210030622⟩,⟨-569952701757,-569952669581⟩,⟨-248368980912,-248368966889⟩,⟨3865342909665,3865342909877⟩,⟨2368455259568,2368455298282⟩,⟨734015287636,734015287684⟩⟩⟩
noncomputable def centerBoxes17 := centerStep16.proposed :: centerBoxes16
theorem centerAccepted16 : StepValid centerStep16.shape centerBoxes16 centerStep16.proposed := by
  dsimp only [StepValid,centerStep16]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep17 : Instruction 40 := ⟨.neg 0,⟨⟨352210030622,352210038248⟩,⟨569952669581,569952701757⟩,⟨248368966889,248368980912⟩,⟨-3865342909877,-3865342909665⟩,⟨-2368455298282,-2368455259568⟩,⟨-734015287684,-734015287636⟩⟩⟩
noncomputable def centerBoxes18 := centerStep17.proposed :: centerBoxes17
theorem centerAccepted17 : StepValid centerStep17.shape centerBoxes17 centerStep17.proposed := by
  dsimp only [StepValid,centerStep17]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-217126786827,-217126786825⟩,⟨-916116524237,-916116524236⟩,⟨-399217210164,-399217210163⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes19 := centerStep18.proposed :: centerBoxes18
theorem centerAccepted18 : StepValid centerStep18.shape centerBoxes18 centerStep18.proposed := by
  dsimp only [StepValid,centerStep18]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨882384840949,882384840951⟩,⟨-916116524237,-916116524236⟩,⟨-399217210164,-399217210163⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes20 := centerStep19.proposed :: centerBoxes19
theorem centerAccepted19 : StepValid centerStep19.shape centerBoxes19 centerStep19.proposed := by
  dsimp only [StepValid,centerStep19]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep20 : Instruction 40 := ⟨.log 0,⟨⟨-241884968192,-241884968128⟩,⟨-1141543603258,-1141543603252⟩,⟨-497451842115,-497451842111⟩,⟨-1185182371172,-1185182371160⟩,⟨853598035782,853598035792⟩,⟨-225062044795,-225062044792⟩⟩⟩
noncomputable def centerBoxes21 := centerStep20.proposed :: centerBoxes20
theorem centerAccepted20 : StepValid centerStep20.shape centerBoxes20 centerStep20.proposed := by
  dsimp only [StepValid,centerStep20]
  exact ⟨by decide,by decide,lc3,by decide⟩
noncomputable def centerStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-194118573915,-194118573862⟩,⟨-714577212906,-714577212843⟩,⟨-311392179747,-311392179717⟩,⟨951137697542,951137697569⟩,⟨1272105088959,1272105089043⟩,⟨180617768450,180617768459⟩⟩⟩
noncomputable def centerBoxes22 := centerStep21.proposed :: centerBoxes21
theorem centerAccepted21 : StepValid centerStep21.shape centerBoxes21 centerStep21.proposed := by
  dsimp only [StepValid,centerStep21]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep22 : Instruction 40 := ⟨.neg 0,⟨⟨194118573862,194118573915⟩,⟨714577212843,714577212906⟩,⟨311392179717,311392179747⟩,⟨-951137697569,-951137697542⟩,⟨-1272105089043,-1272105088959⟩,⟨-180617768459,-180617768450⟩⟩⟩
noncomputable def centerBoxes23 := centerStep22.proposed :: centerBoxes22
theorem centerAccepted22 : StepValid centerStep22.shape centerBoxes22 centerStep22.proposed := by
  dsimp only [StepValid,centerStep22]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨546328604484,546328612163⟩,⟨1284529882424,1284529914663⟩,⟨559761146606,559761160659⟩,⟨-4816480607446,-4816480607207⟩,⟨-3640560387325,-3640560348527⟩,⟨-914633056143,-914633056086⟩⟩⟩
noncomputable def centerBoxes24 := centerStep23.proposed :: centerBoxes23
theorem centerAccepted23 : StepValid centerStep23.shape centerBoxes23 centerStep23.proposed := by
  dsimp only [StepValid,centerStep23]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨985387588692,985387601986⟩,⟨3308907607982,3308907680881⟩,⟨559761146606,559761160659⟩,⟨-14121081062059,-14121081061534⟩,⟨-3640560387325,-3640560348527⟩,⟨-914633056143,-914633056086⟩⟩⟩
noncomputable def centerBoxes25 := centerStep24.proposed :: centerBoxes24
theorem centerAccepted24 : StepValid centerStep24.shape centerBoxes24 centerStep24.proposed := by
  dsimp only [StepValid,centerStep24]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨133176366200,133176366206⟩,⟨-366790207080,-366790207078⟩,⟨798434420326,798434420328⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes26 := centerStep25.proposed :: centerBoxes25
theorem centerAccepted25 : StepValid centerStep25.shape centerBoxes25 centerStep25.proposed := by
  dsimp only [StepValid,centerStep25]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep26 : Instruction 40 := ⟨.inv 0,⟨⟨9077630318765,9077630319175⟩,⟨25001327181782,25001327184178⟩,⟨-54423263741542,-54423263736488⟩,⟨137715755962966,137715755983131⟩,⟨-149890860891301,-149890860834748⟩,⟨652569345021380,652569345113082⟩⟩⟩
noncomputable def centerBoxes27 := centerStep26.proposed :: centerBoxes26
theorem centerAccepted26 : StepValid centerStep26.shape centerBoxes26 centerStep26.proposed := by
  dsimp only [StepValid,centerStep26]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨8135415783586,8135415893710⟩,⟨49724837963335,49724838870864⟩,⟨-44152970617536,-44152969838752⟩,⟨157316759712246,157316764734678⟩,⟨-315444632330693,-315444626201720⟩,⟨521870764738139,521870774107565⟩⟩⟩
noncomputable def centerBoxes28 := centerStep27.proposed :: centerBoxes27
theorem centerAccepted27 : StepValid centerStep27.shape centerBoxes27 centerStep27.proposed := by
  dsimp only [StepValid,centerStep27]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep28 : Instruction 40 := ⟨.contact 0,⟨⟨102357017600,102357150976⟩,⟨-617826276213,-617824629076⟩,⟨548594894032,548596356264⟩,⟨5456965431345,5457001056112⟩,⟨-2661778704722,-2661741273085⟩,⟨-640523276806,-640482040391⟩⟩⟩
noncomputable def centerBoxes29 := centerStep28.proposed :: centerBoxes28
theorem centerAccepted28 : StepValid centerStep28.shape centerBoxes28 centerStep28.proposed := by
  dsimp only [StepValid,centerStep28]
  exact ⟨by decide,by decide,(⟨⟨102357017600,102357150976⟩,⟨-13661324804,-13661288632⟩,⟨3623810769,3623825494⟩⟩ : DyadicJetEnclosure 40),brcenter28_jet,by decide⟩
noncomputable def centerStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes30 := centerStep29.proposed :: centerBoxes29
theorem centerAccepted29 : StepValid centerStep29.shape centerBoxes29 centerStep29.proposed := by
  dsimp only [StepValid,centerStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def centerStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1201868645376,1201868778752⟩,⟨-617826276213,-617824629076⟩,⟨548594894032,548596356264⟩,⟨5456965431345,5457001056112⟩,⟨-2661778704722,-2661741273085⟩,⟨-640523276806,-640482040391⟩⟩⟩
noncomputable def centerBoxes31 := centerStep30.proposed :: centerBoxes30
theorem centerAccepted30 : StepValid centerStep30.shape centerBoxes30 centerStep30.proposed := by
  dsimp only [StepValid,centerStep30]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep31 : Instruction 40 := ⟨.log 0,⟨⟨97869117248,97869239296⟩,⟨-565209165957,-565207596373⟩,⟨501873811509,501875204906⟩,⟨4701674534689,4701709293189⟩,⟨-2177098703297,-2177062756570⟩,⟨-815055541378,-815016479794⟩⟩⟩
noncomputable def centerBoxes32 := centerStep31.proposed :: centerBoxes31
theorem centerAccepted31 : StepValid centerStep31.shape centerBoxes31 centerStep31.proposed := by
  dsimp only [StepValid,centerStep31]
  exact ⟨by decide,by decide,lc13,by decide⟩
noncomputable def centerStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨106980063147,106980208430⟩,⟨-672820022100,-672818022640⟩,⟨597426056622,597427831668⟩,⟨6260290266057,6260336064790⟩,⟨-3180718153729,-3180671899601⟩,⟨-447131708915,-447082445146⟩⟩⟩
noncomputable def centerBoxes33 := centerStep32.proposed :: centerBoxes32
theorem centerAccepted32 : StepValid centerStep32.shape centerBoxes32 centerStep32.proposed := by
  dsimp only [StepValid,centerStep32]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-102357150976,-102357017600⟩,⟨617824629076,617826276213⟩,⟨-548596356264,-548594894032⟩,⟨-5457001056112,-5456965431345⟩,⟨2661741273085,2661778704722⟩,⟨640482040391,640523276806⟩⟩⟩
noncomputable def centerBoxes34 := centerStep33.proposed :: centerBoxes33
theorem centerAccepted33 : StepValid centerStep33.shape centerBoxes33 centerStep33.proposed := by
  dsimp only [StepValid,centerStep33]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨997154476800,997154610176⟩,⟨617824629076,617826276213⟩,⟨-548596356264,-548594894032⟩,⟨-5457001056112,-5456965431345⟩,⟨2661741273085,2661778704722⟩,⟨640482040391,640523276806⟩⟩⟩
noncomputable def centerBoxes35 := centerStep34.proposed :: centerBoxes34
theorem centerAccepted34 : StepValid centerStep34.shape centerBoxes34 centerStep34.proposed := by
  dsimp only [StepValid,centerStep34]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep35 : Instruction 40 := ⟨.log 0,⟨⟨-107439532864,-107439385728⟩,⟨681243767679,681245675015⟩,⟨-604909356276,-604907663035⟩,⟨-6439250629621,-6439208179636⟩,⟨3309759889535,3309803654530⟩,⟨373428888439,373476315316⟩⟩⟩
noncomputable def centerBoxes36 := centerStep35.proposed :: centerBoxes35
theorem centerAccepted35 : StepValid centerStep35.shape centerBoxes35 centerStep35.proposed := by
  dsimp only [StepValid,centerStep35]
  exact ⟨by decide,by decide,lc14,by decide⟩
noncomputable def centerStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-97437646683,-97437500210⟩,⟨557453228089,557455284133⟩,⟨-494990176705,-494988351418⟩,⟨-4540977062217,-4540929386985⟩,⟨2061737032173,2061784853564⟩,⟨879706273578,879756744387⟩⟩⟩
noncomputable def centerBoxes37 := centerStep36.proposed :: centerBoxes36
theorem centerAccepted36 : StepValid centerStep36.shape centerBoxes36 centerStep36.proposed := by
  dsimp only [StepValid,centerStep36]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨9542416464,9542708220⟩,⟨-115366794011,-115362738507⟩,⟨102435879917,102439480250⟩,⟨1719313203840,1719406677805⟩,⟨-1118981121556,-1118887046037⟩,⟨432574564663,432674299241⟩⟩⟩
noncomputable def centerBoxes38 := centerStep37.proposed :: centerBoxes37
theorem centerAccepted37 : StepValid centerStep37.shape centerBoxes37 centerStep37.proposed := by
  dsimp only [StepValid,centerStep37]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨4771208232,4771354110⟩,⟨-57683397006,-57681369253⟩,⟨51217939958,51219740125⟩,⟨859656601920,859703338903⟩,⟨-559490560778,-559443523018⟩,⟨216287282331,216337149621⟩⟩⟩
noncomputable def centerBoxes39 := centerStep38.proposed :: centerBoxes38
theorem centerAccepted38 : StepValid centerStep38.shape centerBoxes38 centerStep38.proposed := by
  dsimp only [StepValid,centerStep38]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-4771354110,-4771208232⟩,⟨57681369253,57683397006⟩,⟨-51219740125,-51217939958⟩,⟨-859703338903,-859656601920⟩,⟨559443523018,559490560778⟩,⟨-216337149621,-216287282331⟩⟩⟩
noncomputable def centerBoxes40 := centerStep39.proposed :: centerBoxes39
theorem centerAccepted39 : StepValid centerStep39.shape centerBoxes39 centerStep39.proposed := by
  dsimp only [StepValid,centerStep39]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨757352029506,757352194648⟩,⟨57681369253,57683397006⟩,⟨-51219740125,-51217939958⟩,⟨-859703338903,-859656601920⟩,⟨559443523018,559490560778⟩,⟨-216337149621,-216287282331⟩⟩⟩
noncomputable def centerBoxes41 := centerStep40.proposed :: centerBoxes40
theorem centerAccepted40 : StepValid centerStep40.shape centerBoxes40 centerStep40.proposed := by
  dsimp only [StepValid,centerStep40]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨9528738748,9528763582⟩,⟨-115030957080,-115030500514⟩,⟨102140870192,102141275536⟩,⟨1710333852299,1710345511232⟩,⟨-1112110710310,-1112099808330⟩,⟨428179591853,428190343202⟩⟩⟩
noncomputable def centerBoxes42 := centerStep41.proposed :: centerBoxes41
theorem centerAccepted41 : StepValid centerStep41.shape centerBoxes41 centerStep41.proposed := by
  dsimp only [StepValid,centerStep41]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-9528763582,-9528738748⟩,⟨115030500514,115030957080⟩,⟨-102141275536,-102140870192⟩,⟨-1710345511232,-1710333852299⟩,⟨1112099808330,1112110710310⟩,⟨-428190343202,-428179591853⟩⟩⟩
noncomputable def centerBoxes43 := centerStep42.proposed :: centerBoxes42
theorem centerAccepted42 : StepValid centerStep42.shape centerBoxes42 centerStep42.proposed := by
  dsimp only [StepValid,centerStep42]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089982864194,1089982889028⟩,⟨115030500514,115030957080⟩,⟨-102141275536,-102140870192⟩,⟨-1710345511232,-1710333852299⟩,⟨1112099808330,1112110710310⟩,⟨-428190343202,-428179591853⟩⟩⟩
noncomputable def centerBoxes44 := centerStep43.proposed :: centerBoxes43
theorem centerAccepted43 : StepValid centerStep43.shape centerBoxes43 centerStep43.proposed := by
  dsimp only [StepValid,centerStep43]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep44 : Instruction 40 := ⟨.log 0,⟨⟨-9570293568,-9570268480⟩,⟨116036108582,116036571784⟩,⟨-103034207067,-103033795830⟩,⟨-1737543439663,-1737531541726⟩,⟨1132695487275,1132706596930⟩,⟨-441588874833,-441577942579⟩⟩⟩
noncomputable def centerBoxes45 := centerStep44.proposed :: centerBoxes44
theorem centerAccepted44 : StepValid centerStep44.shape centerBoxes44 centerStep44.proposed := by
  dsimp only [StepValid,centerStep44]
  exact ⟨by decide,by decide,lc11,by decide⟩
noncomputable def centerStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-4785146784,-4785134240⟩,⟨58018054291,58018285892⟩,⟨-51517103534,-51516897915⟩,⟨-868771719832,-868765770863⟩,⟨566347743637,566353298465⟩,⟨-220794437417,-220788971289⟩⟩⟩
noncomputable def centerBoxes46 := centerStep45.proposed :: centerBoxes45
theorem centerAccepted45 : StepValid centerStep45.shape centerBoxes45 centerStep45.proposed := by
  dsimp only [StepValid,centerStep45]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4785134240,4785146784⟩,⟨-58018285892,-58018054291⟩,⟨51516897915,51517103534⟩,⟨868765770863,868771719832⟩,⟨-566353298465,-566347743637⟩,⟨220788971289,220794437417⟩⟩⟩
noncomputable def centerBoxes47 := centerStep46.proposed :: centerBoxes46
theorem centerAccepted46 : StepValid centerStep46.shape centerBoxes46 centerStep46.proposed := by
  dsimp only [StepValid,centerStep46]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766908517856,766908549664⟩,⟨-58018285892,-58018054291⟩,⟨51516897915,51517103534⟩,⟨868765770863,868771719832⟩,⟨-566353298465,-566347743637⟩,⟨220788971289,220794437417⟩⟩⟩
noncomputable def centerBoxes48 := centerStep47.proposed :: centerBoxes47
theorem centerAccepted47 : StepValid centerStep47.shape centerBoxes47 centerStep47.proposed := by
  dsimp only [StepValid,centerStep47]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes49 := centerStep48.proposed :: centerBoxes48
theorem centerAccepted48 : StepValid centerStep48.shape centerBoxes48 centerStep48.proposed := by
  dsimp only [StepValid,centerStep48]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes50 := centerStep49.proposed :: centerBoxes49
theorem centerAccepted49 : StepValid centerStep49.shape centerBoxes49 centerStep49.proposed := by
  dsimp only [StepValid,centerStep49]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272495716048,272495722257⟩,⟨28757625128,28757739270⟩,⟨-25535318884,-25535217548⟩,⟨-427586377808,-427583463074⟩,⟨278024952082,278027677578⟩,⟨-107047585801,-107044897963⟩⟩⟩
noncomputable def centerBoxes51 := centerStep50.proposed :: centerBoxes50
theorem centerAccepted50 : StepValid centerStep50.shape centerBoxes50 centerStep50.proposed := by
  dsimp only [StepValid,centerStep50]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533817035712,1533817099328⟩,⟨-116036571784,-116036108582⟩,⟨103033795830,103034207068⟩,⟨1737531541726,1737543439664⟩,⟨-1132706596930,-1132695487274⟩,⟨441577942578,441588874834⟩⟩⟩
noncomputable def centerBoxes52 := centerStep51.proposed :: centerBoxes51
theorem centerAccepted51 : StepValid centerStep51.shape centerBoxes51 centerStep51.proposed := by
  dsimp only [StepValid,centerStep51]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1212375500526,1212375662690⟩,⟨-751175027018,-751172823420⟩,⟨667000886773,667002843040⟩,⟨7565604432037,7565654857582⟩,⟨-4062820336075,-4062769221349⟩,⟨-44856007287,-44801455394⟩⟩⟩
noncomputable def centerBoxes53 := centerStep52.proposed :: centerBoxes52
theorem centerAccepted52 : StepValid centerStep52.shape centerBoxes52 centerStep52.proposed := by
  dsimp only [StepValid,centerStep52]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1325239373276,1325239697604⟩,⟨-1502350054036,-1502345646840⟩,⟨1334001773546,1334005686081⟩,⟨15131208864080,15131309715162⟩,⟨-8125640672150,-8125538442702⟩,⟨-89711925546,-89602999817⟩⟩⟩
noncomputable def centerBoxes54 := centerStep53.proposed :: centerBoxes53
theorem centerAccepted53 : StepValid centerStep53.shape centerBoxes53 centerStep53.proposed := by
  dsimp only [StepValid,centerStep53]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep54 : Instruction 40 := ⟨.log 0,⟨⟨205308502976,205308772160⟩,⟨-1246455083297,-1246451121729⟩,⟨1106781259374,1106784776354⟩,⟨11140873454829,11140969182328⟩,⟨-5486909722657,-5486815281291⟩,⟨-1188537348029,-1188439876922⟩⟩⟩
noncomputable def centerBoxes55 := centerStep54.proposed :: centerBoxes54
theorem centerAccepted54 : StepValid centerStep54.shape centerBoxes54 centerStep54.proposed := by
  dsimp only [StepValid,centerStep54]
  exact ⟨by decide,by decide,lc16,by decide⟩
noncomputable def centerStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨70504297594,70504404839⟩,⟨-420193822060,-420192398935⟩,⟨373108150323,373109413715⟩,⟨3613941246998,3613973512061⟩,⟨-1723814024216,-1723781217756⟩,⟨-512448686370,-512413585059⟩⟩⟩
noncomputable def centerBoxes56 := centerStep55.proposed :: centerBoxes55
theorem centerAccepted55 : StepValid centerStep55.shape centerBoxes55 centerStep55.proposed := by
  dsimp only [StepValid,centerStep55]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨380131106278,380131130707⟩,⟨11359103055,11359379401⟩,⟨-10086515222,-10086269878⟩,⟨-171933875262,-171926777630⟩,⟨112511516063,112518136860⟩,⟨-44679238780,-44672733087⟩⟩⟩
noncomputable def centerBoxes57 := centerStep56.proposed :: centerBoxes56
theorem centerAccepted56 : StepValid centerStep56.shape centerBoxes56 centerStep56.proposed := by
  dsimp only [StepValid,centerStep56]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3180286280069,3180286484450⟩,⟨-95035844698,-95033520492⟩,⟨84384632351,84386695817⟩,⟨1444068424908,1444128268069⟩,⟨-946402609412,-946346850587⟩,⟨378222989033,378277684297⟩⟩⟩
noncomputable def centerBoxes58 := centerStep57.proposed :: centerBoxes57
theorem centerAccepted57 : StepValid centerStep57.shape centerBoxes57 centerStep57.proposed := by
  dsimp only [StepValid,centerStep57]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨203930403880,203930727188⟩,⟨-1221485198418,-1221480845680⟩,⟨1084609003269,1084612867475⟩,⟨10618392044023,10618492041662⟩,⟨-5111237926193,-5111137251150⟩,⟨-1400711059321,-1400604296653⟩⟩⟩
noncomputable def centerBoxes59 := centerStep58.proposed :: centerBoxes58
theorem centerAccepted58 : StepValid centerStep58.shape centerBoxes58 centerStep58.proposed := by
  dsimp only [StepValid,centerStep58]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨409238906856,409239499348⟩,⟨-2467940281715,-2467931967409⟩,⟨2191390262643,2191397643829⟩,⟨21759265498852,21759461223990⟩,⟨-10598147648850,-10597952532441⟩,⟨-2589248407350,-2589044173575⟩⟩⟩
noncomputable def centerBoxes60 := centerStep59.proposed :: centerBoxes59
theorem centerAccepted59 : StepValid centerStep59.shape centerBoxes59 centerStep59.proposed := by
  dsimp only [StepValid,centerStep59]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨521669877886,521670105389⟩,⟨79462737754,79465548548⟩,⟨-70561113886,-70558618560⟩,⟨-1178288712448,-1178223643094⟩,⟨765323709760,765389055566⟩,⟨-293257722071,-293188623710⟩⟩⟩
noncomputable def centerBoxes61 := centerStep60.proposed :: centerBoxes60
theorem centerAccepted60 : StepValid centerStep60.shape centerBoxes60 centerStep60.proposed := by
  dsimp only [StepValid,centerStep60]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨359330206946,359330442006⟩,⟨82101813461,82104735510⟩,⟨-72904569323,-72901975226⟩,⟨-1211168668920,-1211100731130⟩,⟨785188503559,785256584401⟩,⟨-298067124162,-297995316508⟩⟩⟩
noncomputable def centerBoxes62 := centerStep61.proposed :: centerBoxes61
theorem centerAccepted61 : StepValid centerStep61.shape centerBoxes61 centerStep61.proposed := by
  dsimp only [StepValid,centerStep61]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨718660413892,718660884012⟩,⟨164203626922,164209471020⟩,⟨-145809138646,-145803950452⟩,⟨-2422337337840,-2422201462260⟩,⟨1570377007118,1570513168802⟩,⟨-596134248324,-595990633016⟩⟩⟩
noncomputable def centerBoxes63 := centerStep62.proposed :: centerBoxes62
theorem centerAccepted62 : StepValid centerStep62.shape centerBoxes62 centerStep62.proposed := by
  dsimp only [StepValid,centerStep62]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1524288272130,1524288360580⟩,⟨-1006071270,-1005151502⟩,⟨892520294,893336876⟩,⟨27186030494,27209587365⟩,⟨-20606788600,-20584776964⟩,⟨13387599376,13409282981⟩⟩⟩
noncomputable def centerBoxes64 := centerStep63.proposed :: centerBoxes63
theorem centerAccepted63 : StepValid centerStep63.shape centerBoxes63 centerStep63.proposed := by
  dsimp only [StepValid,centerStep63]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨996302006151,996302715707⟩,⟨226983173606,226991890285⟩,⟨-201556535014,-201548796607⟩,⟨-3340695455704,-3340491197917⟩,⟨2163861674479,2164065215560⟩,⟨-817926658527,-817713108529⟩⟩⟩
noncomputable def centerBoxes65 := centerStep64.proposed :: centerBoxes64
theorem centerAccepted64 : StepValid centerStep64.shape centerBoxes64 centerStep64.proposed := by
  dsimp only [StepValid,centerStep64]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67533542518,67533545597⟩,⟨14254200598,14254257500⟩,⟨-12657010598,-12656960080⟩,⟨-210436078933,-210434617423⟩,⟨136471990758,136473355444⟩,⟨-51873870459,-51872527562⟩⟩⟩
noncomputable def centerBoxes66 := centerStep65.proposed :: centerBoxes65
theorem centerAccepted65 : StepValid centerStep65.shape centerBoxes65 centerStep65.proposed := by
  dsimp only [StepValid,centerStep65]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨60523884365,60523887942⟩,⟨216012417683,216012482597⟩,⟨23038039100,23038086960⟩,⟨-970136269978,-970134573666⟩,⟨-132135098224,-132133678934⟩,⟨-115555019789,-115553761322⟩⟩⟩
noncomputable def centerBoxes67 := centerStep66.proposed :: centerBoxes66
theorem centerAccepted66 : StepValid centerStep66.shape centerBoxes66 centerStep66.proposed := by
  dsimp only [StepValid,centerStep66]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2139672414196,2139672591685⟩,⟨-323741693046,-323740387284⟩,⟨287463974560,287465133838⟩,⟨4872199237581,4872232829391⟩,⟨-3181995422090,-3181964121494⟩,⟨1251311430684,1251342136894⟩⟩⟩
noncomputable def centerBoxes68 := centerStep67.proposed :: centerBoxes67
theorem centerAccepted67 : StepValid centerStep67.shape centerBoxes67 centerStep67.proposed := by
  dsimp only [StepValid,centerStep67]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2984839738689,2984840110085⟩,⟨-677428776580,-677426016179⟩,⟨601517705945,601520156681⟩,⟨10246314241224,10246385366144⟩,⟨-6703824679366,-6703758541612⟩,⟨2658773101521,2658837787025⟩⟩⟩
noncomputable def centerBoxes69 := centerStep68.proposed :: centerBoxes68
theorem centerAccepted68 : StepValid centerStep68.shape centerBoxes68 centerStep68.proposed := by
  dsimp only [StepValid,centerStep68]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨164303942431,164303972586⟩,⟨549118180958,549118584300⟩,⟨95652506101,95652780671⟩,⟨-2335783443596,-2335773397821⟩,⟨-623745148852,-623736984522⟩,⟨-142134381697,-142127201901⟩⟩⟩
noncomputable def centerBoxes70 := centerStep69.proposed :: centerBoxes69
theorem centerAccepted69 : StepValid centerStep69.shape centerBoxes69 centerStep69.proposed := by
  dsimp only [StepValid,centerStep69]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep70 : Instruction 40 := ⟨.inv 0,⟨⟨7357861167853,7357862518256⟩,⟨-24590639699325,-24590612610524⟩,⟨-4283524784938,-4283510916815⟩,⟨268968550278133,268969370509233⟩,⟨56563925001956,56564419852703⟩,⟨11352186429912,11352541670949⟩⟩⟩
noncomputable def centerBoxes71 := centerStep70.proposed :: centerBoxes70
theorem centerAccepted70 : StepValid centerStep70.shape centerBoxes70 centerStep70.proposed := by
  dsimp only [StepValid,centerStep70]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨6667189011307,6667194983254⟩,⟨-20763409733790,-20763310708271⟩,⟨-5230242686887,-5230175323753⟩,⟨211211751573375,211214440451967⟩,⟨69358092090570,69360156592457⟩,⟨6383458778088,6385283446300⟩⟩⟩
noncomputable def centerBoxes72 := centerStep71.proposed :: centerBoxes71
theorem centerAccepted71 : StepValid centerStep71.shape centerBoxes71 centerStep71.proposed := by
  dsimp only [StepValid,centerStep71]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨13334378022614,13334389966508⟩,⟨-41526819467580,-41526621416542⟩,⟨-10460485373774,-10460350647506⟩,⟨422423503146750,422428880903934⟩,⟨138716184181140,138720313184914⟩,⟨12766917556176,12770566892600⟩⟩⟩
noncomputable def centerBoxes73 := centerStep72.proposed :: centerBoxes72
theorem centerAccepted72 : StepValid centerStep72.shape centerBoxes72 centerStep72.proposed := by
  dsimp only [StepValid,centerStep72]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep73 : Instruction 40 := ⟨.inv 73,⟨⟨8030669806284,8030669806339⟩,⟨-58654820839770,-58654820838966⟩,⟨0,0⟩,⟨856812218816196,856812218833812⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes74 := centerStep73.proposed :: centerBoxes73
theorem centerAccepted73 : StepValid centerStep73.shape centerBoxes73 centerStep73.proposed := by
  dsimp only [StepValid,centerStep73]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨6931158178508,6931158178563⟩,⟨-58654820839770,-58654820838966⟩,⟨0,0⟩,⟨856812218816207,856812218833800⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes75 := centerStep74.proposed :: centerBoxes74
theorem centerAccepted74 : StepValid centerStep74.shape centerBoxes74 centerStep74.proposed := by
  dsimp only [StepValid,centerStep74]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep75 : Instruction 40 := ⟨.log 0,⟨⟨2024377725696,2024377764352⟩,⟨-9304600454574,-9304600454338⟩,⟨0,0⟩,⟨57178802523621,57178802533053⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes76 := centerStep75.proposed :: centerBoxes75
theorem centerAccepted75 : StepValid centerStep75.shape centerBoxes75 centerStep75.proposed := by
  dsimp only [StepValid,centerStep75]
  exact ⟨by decide,by decide,lc17,by decide⟩
noncomputable def centerStep76 : Instruction 40 := ⟨.inv 70,⟨⟨5567833602114,5567833602167⟩,⟨-23492192933612,-23492192933137⟩,⟨-10237221440146,-10237221439924⟩,⟨198239806806805,198239806812911⟩,⟨114582238319680,114582238323002⟩,⟨37645055617417,37645055618684⟩⟩⟩
noncomputable def centerBoxes77 := centerStep76.proposed :: centerBoxes76
theorem centerAccepted76 : StepValid centerStep76.shape centerBoxes76 centerStep76.proposed := by
  dsimp only [StepValid,centerStep76]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨4468321974338,4468321974391⟩,⟨-23492192933612,-23492192933137⟩,⟨-10237221440146,-10237221439923⟩,⟨198239806806811,198239806812908⟩,⟨114582238319682,114582238323001⟩,⟨37645055617417,37645055618684⟩⟩⟩
noncomputable def centerBoxes78 := centerStep77.proposed :: centerBoxes77
theorem centerAccepted77 : StepValid centerStep77.shape centerBoxes77 centerStep77.proposed := by
  dsimp only [StepValid,centerStep77]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep78 : Instruction 40 := ⟨.log 0,⟨⟨1541676745920,1541676784576⟩,⟨-5780679960137,-5780679959933⟩,⟨-2519053925437,-2519053925344⟩,⟨18388586191564,18388586196410⟩,⟨14951116531864,14951116534263⟩,⟨3491929098665,3491929099641⟩⟩⟩
noncomputable def centerBoxes79 := centerStep78.proposed :: centerBoxes78
theorem centerAccepted78 : StepValid centerStep78.shape centerBoxes78 centerStep78.proposed := by
  dsimp only [StepValid,centerStep78]
  exact ⟨by decide,by decide,lc18,by decide⟩
noncomputable def centerStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨129927751925,129927751927⟩,⟨798434420326,798434420328⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes80 := centerStep79.proposed :: centerBoxes79
theorem centerAccepted79 : StepValid centerStep79.shape centerBoxes79 centerStep79.proposed := by
  dsimp only [StepValid,centerStep79]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨174249530808,174249530811⟩,⟨554295089624,554295089631⟩,⟨241545844259,241545844264⟩,⟨-1526622301718,-1526622301713⟩,⟨-1330516108252,-1330516108244⟩,⟨-289900310038,-289900310036⟩⟩⟩
noncomputable def centerBoxes81 := centerStep80.proposed :: centerBoxes80
theorem centerAccepted80 : StepValid centerStep80.shape centerBoxes80 centerStep80.proposed := by
  dsimp only [StepValid,centerStep80]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨3566054471616,3566054548928⟩,⟨-15085280414711,-15085280414271⟩,⟨-2519053925437,-2519053925344⟩,⟨75567388715185,75567388729463⟩,⟨14951116531864,14951116534263⟩,⟨3491929098665,3491929099641⟩⟩⟩
noncomputable def centerBoxes82 := centerStep81.proposed :: centerBoxes81
theorem centerAccepted81 : StepValid centerStep81.shape centerBoxes81 centerStep81.proposed := by
  dsimp only [StepValid,centerStep81]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨818477813712,818478998696⟩,⟨-4935880563430,-4935863934818⟩,⟨4382780525286,4382795287658⟩,⟨43518530997704,43518922447980⟩,⟨-21196295297700,-21195905064882⟩,⟨-5178496814700,-5178088347150⟩⟩⟩
noncomputable def centerBoxes83 := centerStep82.proposed :: centerBoxes82
theorem centerAccepted82 : StepValid centerStep82.shape centerBoxes82 centerStep82.proposed := by
  dsimp only [StepValid,centerStep82]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4384532285328,4384533547624⟩,⟨-20021160978141,-20021144349089⟩,⟨1863726599849,1863741362314⟩,⟨119085919712889,119086311177443⟩,⟨-6245178765836,-6244788530619⟩,⟨-1686567716035,-1686159247509⟩⟩⟩
noncomputable def centerBoxes84 := centerStep83.proposed :: centerBoxes83
theorem centerAccepted83 : StepValid centerStep83.shape centerBoxes83 centerStep83.proposed := by
  dsimp only [StepValid,centerStep83]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨518114050533,518114199705⟩,⟨818051427611,818054309333⟩,⟨220233966793,220235711258⟩,⟨-23774458460602,-23774385525799⟩,⟨615401795557,615458629210⟩,⟨-199299349167,-199251081009⟩⟩⟩
noncomputable def centerBoxes85 := centerStep84.proposed :: centerBoxes84
theorem centerAccepted84 : StepValid centerStep84.shape centerBoxes84 centerStep84.proposed := by
  dsimp only [StepValid,centerStep84]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨301077207448,301077207450⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes86 := centerStep85.proposed :: centerBoxes85
theorem centerAccepted85 : StepValid centerStep85.shape centerBoxes85 centerStep85.proposed := by
  dsimp only [StepValid,centerStep85]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-301077207450,-301077207448⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes87 := centerStep86.proposed :: centerBoxes86
theorem centerAccepted86 : StepValid centerStep86.shape centerBoxes86 centerStep86.proposed := by
  dsimp only [StepValid,centerStep86]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨798434420326,798434420328⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes88 := centerStep87.proposed :: centerBoxes87
theorem centerAccepted87 : StepValid centerStep87.shape centerBoxes87 centerStep87.proposed := by
  dsimp only [StepValid,centerStep87]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1470046168776,1470046196851⟩,⟨-10805494686942,-10805494609441⟩,⟨0,0⟩,⟨78740040056163,78740040064062⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes89 := centerStep88.proposed :: centerBoxes88
theorem centerAccepted88 : StepValid centerStep88.shape centerBoxes88 centerStep88.proposed := by
  dsimp only [StepValid,centerStep88]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes90 := centerStep89.proposed :: centerBoxes89
theorem centerAccepted89 : StepValid centerStep89.shape centerBoxes89 centerStep89.proposed := by
  dsimp only [StepValid,centerStep89]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨370534541000,370534569075⟩,⟨-10805494686942,-10805494609441⟩,⟨0,0⟩,⟨78740040056163,78740040064062⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes91 := centerStep90.proposed :: centerBoxes90
theorem centerAccepted90 : StepValid centerStep90.shape centerBoxes90 centerStep90.proposed := by
  dsimp only [StepValid,centerStep90]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨22440164558,22440166260⟩,⟨-716202052349,-716202042941⟩,⟨134535881195,134535891390⟩,⟨8373268255980,8373268282548⟩,⟨-4293857737643,-4293857681418⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes92 := centerStep91.proposed :: centerBoxes91
theorem centerAccepted91 : StepValid centerStep91.shape centerBoxes91 centerStep91.proposed := by
  dsimp only [StepValid,centerStep91]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨540554215091,540554365965⟩,⟨101849375262,101852266392⟩,⟨354769847988,354771602648⟩,⟨-15401190204622,-15401117243251⟩,⟨-3678455942086,-3678399052208⟩,⟨-199299349167,-199251081009⟩⟩⟩
noncomputable def centerBoxes93 := centerStep92.proposed :: centerBoxes92
theorem centerAccepted92 : StepValid centerStep92.shape centerBoxes92 centerStep92.proposed := by
  dsimp only [StepValid,centerStep92]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep93 : Instruction 40 := ⟨.inv 17,⟨⟨597183905545,597183916949⟩,⟨2744822501362,2744822606274⟩,⟨0,0⟩,⟨8364393133125,8364395227208⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes94 := centerStep93.proposed :: centerBoxes93
theorem centerAccepted93 : StepValid centerStep93.shape centerBoxes93 centerStep93.proposed := by
  dsimp only [StepValid,centerStep93]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨293594236906,293594324459⟩,⟨1404758386782,1404760386336⟩,⟨192688133566,192689090265⟩,⟨-3744224353202,-3744167933991⟩,⟨-1112252417678,-1112217066417⟩,⟨-108246573274,-108220355051⟩⟩⟩
noncomputable def centerBoxes95 := centerStep94.proposed :: centerBoxes94
theorem centerAccepted94 : StepValid centerStep94.shape centerBoxes94 centerStep94.proposed := by
  dsimp only [StepValid,centerStep94]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-818478998696,-818477813712⟩,⟨4935863934818,4935880563430⟩,⟨-4382795287658,-4382780525286⟩,⟨-43518922447980,-43518530997704⟩,⟨21195905064882,21196295297700⟩,⟨5178088347150,5178496814700⟩⟩⟩
noncomputable def centerBoxes96 := centerStep95.proposed :: centerBoxes95
theorem centerAccepted95 : StepValid centerStep95.shape centerBoxes95 centerStep95.proposed := by
  dsimp only [StepValid,centerStep95]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨2747575472920,2747576735216⟩,⟨-10149416479893,-10149399850841⟩,⟨-6901849213095,-6901834450630⟩,⟨32048466267205,32048857731759⟩,⟨36147021596746,36147411831963⟩,⟨8670017445815,8670425914341⟩⟩⟩
noncomputable def centerBoxes97 := centerStep96.proposed :: centerBoxes96
theorem centerAccepted96 : StepValid centerStep96.shape centerBoxes96 centerStep96.proposed := by
  dsimp only [StepValid,centerStep96]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨435433082216,435433282272⟩,⟨-223338671837,-223335400074⟩,⟨-490198135448,-490195518566⟩,⟨-8969095819645,-8969015261494⟩,⟨-3305380280054,-3305305812917⟩,⟨-2382878724969,-2382807172186⟩⟩⟩
noncomputable def centerBoxes98 := centerStep97.proposed :: centerBoxes97
theorem centerAccepted97 : StepValid centerStep97.shape centerBoxes97 centerStep97.proposed := by
  dsimp only [StepValid,centerStep97]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨434253573650,434253573654⟩,⟨1832233048472,1832233048474⟩,⟨798434420326,798434420328⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes99 := centerStep98.proposed :: centerBoxes98
theorem centerAccepted98 : StepValid centerStep98.shape centerBoxes98 centerStep98.proposed := by
  dsimp only [StepValid,centerStep98]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-434253573654,-434253573650⟩,⟨-1832233048474,-1832233048472⟩,⟨-798434420328,-798434420326⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes100 := centerStep99.proposed :: centerBoxes99
theorem centerAccepted99 : StepValid centerStep99.shape centerBoxes99 centerStep99.proposed := by
  dsimp only [StepValid,centerStep99]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨665258054122,665258054126⟩,⟨-1832233048474,-1832233048472⟩,⟨-798434420328,-798434420326⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes101 := centerStep100.proposed :: centerBoxes100
theorem centerAccepted100 : StepValid centerStep100.shape centerBoxes100 centerStep100.proposed := by
  dsimp only [StepValid,centerStep100]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨932789473223,932789496618⟩,⟨-6066652582896,-6066652518331⟩,⟨-2643672562500,-2643672534360⟩,⟨30391912149127,30391912152829⟩,⟨20525041157777,20525041236917⟩,⟨5771319300595,5771319301345⟩⟩⟩
noncomputable def centerBoxes102 := centerStep101.proposed :: centerBoxes101
theorem centerAccepted101 : StepValid centerStep101.shape centerBoxes101 centerStep101.proposed := by
  dsimp only [StepValid,centerStep101]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-932789496618,-932789473223⟩,⟨6066652518331,6066652582896⟩,⟨2643672534360,2643672562500⟩,⟨-30391912152829,-30391912149127⟩,⟨-20525041236917,-20525041157777⟩,⟨-5771319301345,-5771319300595⟩⟩⟩
noncomputable def centerBoxes103 := centerStep102.proposed :: centerBoxes102
theorem centerAccepted102 : StepValid centerStep102.shape centerBoxes102 centerStep102.proposed := by
  dsimp only [StepValid,centerStep102]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨166722131158,166722154553⟩,⟨6066652518331,6066652582896⟩,⟨2643672534360,2643672562500⟩,⟨-30391912152829,-30391912149127⟩,⟨-20525041236917,-20525041157777⟩,⟨-5771319301345,-5771319300595⟩⟩⟩
noncomputable def centerBoxes104 := centerStep103.proposed :: centerBoxes103
theorem centerAccepted103 : StepValid centerStep103.shape centerBoxes103 centerStep103.proposed := by
  dsimp only [StepValid,centerStep103]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨10096958973,10096960391⟩,⟨339597447143,339597454974⟩,⟨220639499136,220639509344⟩,⟨-3864380204001,-3864380182142⟩,⟨352008408708,352008465100⟩,⟨1570240311702,1570240332204⟩⟩⟩
noncomputable def centerBoxes105 := centerStep104.proposed :: centerBoxes104
theorem centerAccepted104 : StepValid centerStep104.shape centerBoxes104 centerStep104.proposed := by
  dsimp only [StepValid,centerStep104]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨445530041189,445530242663⟩,⟨116258775306,116262054900⟩,⟨-269558636312,-269556009222⟩,⟨-12833476023646,-12833395443636⟩,⟨-2953371871346,-2953297347817⟩,⟨-812638413267,-812566839982⟩⟩⟩
noncomputable def centerBoxes106 := centerStep105.proposed :: centerBoxes105
theorem centerAccepted105 : StepValid centerStep105.shape centerBoxes105 centerStep105.proposed := by
  dsimp only [StepValid,centerStep105]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-129927751927,-129927751925⟩,⟨-798434420328,-798434420326⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes107 := centerStep106.proposed :: centerBoxes106
theorem centerAccepted106 : StepValid centerStep106.shape centerBoxes106 centerStep106.proposed := by
  dsimp only [StepValid,centerStep106]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨7868632505,7868632507⟩,⟨26682922776,26682922781⟩,⟨47174939614,47174939616⟩,⟨-399529098614,-399529098605⟩,⟨159972558109,159972558113⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes108 := centerStep107.proposed :: centerBoxes107
theorem centerAccepted107 : StepValid centerStep107.shape centerBoxes107 centerStep107.proposed := by
  dsimp only [StepValid,centerStep107]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨14487417842,14487418124⟩,⟨-17460631241,-17460630274⟩,⟨86856650310,86856651973⟩,⟨-778006060671,-778006046338⟩,⟨-104682004565,-104681998904⟩,⟨0,0⟩⟩⟩
noncomputable def centerBoxes109 := centerStep108.proposed :: centerBoxes108
theorem centerAccepted108 : StepValid centerStep108.shape centerBoxes108 centerStep108.proposed := by
  dsimp only [StepValid,centerStep108]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1226853085200,1226853101752⟩,⟨-4119743031361,-4119742829432⟩,⟨-696928522418,-696928486114⟩,⟨45249390756793,45249393570852⟩,⟨9213203633774,9213204214461⟩,⟨1930557437327,1930557539933⟩⟩⟩
noncomputable def centerBoxes110 := centerStep109.proposed :: centerBoxes109
theorem centerAccepted109 : StepValid centerStep109.shape centerBoxes109 centerStep109.proposed := by
  dsimp only [StepValid,centerStep109]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨16165298144,16165298677⟩,⟨-73765540452,-73765535391⟩,⟨87733182677,87733186499⟩,⟨-141049627010,-141049536957⟩,⟨-309784979768,-309784938484⟩,⟨-84671195493,-84671185800⟩⟩⟩
noncomputable def centerBoxes111 := centerStep110.proposed :: centerBoxes110
theorem centerAccepted110 : StepValid centerStep110.shape centerBoxes110 centerStep110.proposed := by
  dsimp only [StepValid,centerStep110]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-16165298677,-16165298144⟩,⟨73765535391,73765540452⟩,⟨-87733186499,-87733182677⟩,⟨141049536957,141049627010⟩,⟨309784938484,309784979768⟩,⟨84671185800,84671195493⟩⟩⟩
noncomputable def centerBoxes112 := centerStep111.proposed :: centerBoxes111
theorem centerAccepted111 : StepValid centerStep111.shape centerBoxes111 centerStep111.proposed := by
  dsimp only [StepValid,centerStep111]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-146093050604,-146093050069⟩,⟨-724668884937,-724668879874⟩,⟨-87733186499,-87733182677⟩,⟨2340072792509,2340072882562⟩,⟨309784938484,309784979768⟩,⟨84671185800,84671195493⟩⟩⟩
noncomputable def centerBoxes113 := centerStep112.proposed :: centerBoxes112
theorem centerAccepted112 : StepValid centerStep112.shape centerBoxes112 centerStep112.proposed := by
  dsimp only [StepValid,centerStep112]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨93366409999,93366412345⟩,⟨-607234095859,-607234089380⟩,⟨407203211076,407203225126⟩,⟨3042040901917,3042040902342⟩,⟨-2314926529671,-2314926490728⟩,⟨-1617789299906,-1617789299764⟩⟩⟩
noncomputable def centerBoxes114 := centerStep113.proposed :: centerBoxes113
theorem centerAccepted113 : StepValid centerStep113.shape centerBoxes113 centerStep113.proposed := by
  dsimp only [StepValid,centerStep113]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨104179769697,104179773721⟩,⟨-1027394919781,-1027394877471⟩,⟨395183451484,395183477863⟩,⟨11787239606240,11787240259612⟩,⟨-2941528655187,-2941528356328⟩,⟨-2157433925617,-2157433843568⟩⟩⟩
noncomputable def centerBoxes115 := centerStep114.proposed :: centerBoxes114
theorem centerAccepted114 : StepValid centerStep114.shape centerBoxes114 centerStep114.proposed := by
  dsimp only [StepValid,centerStep114]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-104179773721,-104179769697⟩,⟨1027394877471,1027394919781⟩,⟨-395183477863,-395183451484⟩,⟨-11787240259612,-11787239606240⟩,⟨2941528356328,2941528655187⟩,⟨2157433843568,2157433925617⟩⟩⟩
noncomputable def centerBoxes116 := centerStep115.proposed :: centerBoxes115
theorem centerAccepted115 : StepValid centerStep115.shape centerBoxes115 centerStep115.proposed := by
  dsimp only [StepValid,centerStep115]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨995331854055,995331858079⟩,⟨1027394877471,1027394919781⟩,⟨-395183477863,-395183451484⟩,⟨-11787240259612,-11787239606240⟩,⟨2941528356328,2941528655187⟩,⟨2157433843568,2157433925617⟩⟩⟩
noncomputable def centerBoxes117 := centerStep116.proposed :: centerBoxes116
theorem centerAccepted116 : StepValid centerStep116.shape centerBoxes116 centerStep116.proposed := by
  dsimp only [StepValid,centerStep116]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨157739221838,157739222479⟩,⟨664595640594,664595649339⟩,⟨156030853215,156030858288⟩,⟨-2214125766455,-2214125614609⟩,⟨-711798231806,-711798156953⟩,⟨-94155468884,-94155443216⟩⟩⟩
noncomputable def centerBoxes118 := centerStep117.proposed :: centerBoxes117
theorem centerAccepted117 : StepValid centerStep117.shape centerBoxes117 centerStep117.proposed := by
  dsimp only [StepValid,centerStep117]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨19411508472,19411508615⟩,⟨192574747326,192574749378⟩,⟨23314365988,23314367092⟩,⟨333378192241,333378231799⟩,⟨33324021372,33324038494⟩,⟨-8499704392,-8499700511⟩⟩⟩
noncomputable def centerBoxes119 := centerStep118.proposed :: centerBoxes118
theorem centerAccepted118 : StepValid centerStep118.shape centerBoxes118 centerStep118.proposed := by
  dsimp only [StepValid,centerStep118]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨235413965087,235414177688⟩,⟨1602317083421,1602322702155⟩,⟨98069692731,98072339292⟩,⟨-3045684436919,-3045515807699⟩,⟨140470201754,140571543096⟩,⟨-321299409362,-321229105934⟩⟩⟩
noncomputable def centerBoxes120 := centerStep119.proposed :: centerBoxes119
theorem centerAccepted119 : StepValid centerStep119.shape centerBoxes119 centerStep119.proposed := by
  dsimp only [StepValid,centerStep119]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-235414177688,-235413965087⟩,⟨-1602322702155,-1602317083421⟩,⟨-98072339292,-98069692731⟩,⟨3045515807699,3045684436919⟩,⟨-140571543096,-140470201754⟩,⟨321229105934,321299409362⟩⟩⟩
noncomputable def centerBoxes121 := centerStep120.proposed :: centerBoxes120
theorem centerAccepted120 : StepValid centerStep120.shape centerBoxes120 centerStep120.proposed := by
  dsimp only [StepValid,centerStep120]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨58180059218,58180359372⟩,⟨-197564315373,-197556697085⟩,⟨94615794274,94619397534⟩,⟨-698708545503,-698483497072⟩,⟨-1252823960774,-1252687268171⟩,⟨212982532660,213079054311⟩⟩⟩
noncomputable def centerBoxes122 := centerStep121.proposed :: centerBoxes121
theorem centerAccepted121 : StepValid centerStep121.shape centerBoxes121 centerStep121.proposed := by
  dsimp only [StepValid,centerStep121]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨18696755904575,18696773120472⟩,⟨-128332225695424,-128331883741340⟩,⟨-45217106930600,-45216890291444⟩,⟨1251960445882832,1251970283473045⟩,⟨525956323307009,525963442171876⟩,⟨108180335938729,108186108572928⟩⟩⟩
noncomputable def centerBoxes123 := centerStep122.proposed :: centerBoxes122
theorem centerAccepted122 : StepValid centerStep122.shape centerBoxes122 centerStep122.proposed := by
  dsimp only [StepValid,centerStep122]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨22629739856,22629740041⟩,⟨190689750860,190689754146⟩,⟨44769304384,44769306022⟩,⟨168134444948,168134512244⟩,⟨-15608884138,-15608853212⟩,⟨17268788179,17268798536⟩⟩⟩
noncomputable def centerBoxes124 := centerStep123.proposed :: centerBoxes123
theorem centerAccepted123 : StepValid centerStep123.shape centerBoxes123 centerStep123.proposed := by
  dsimp only [StepValid,centerStep123]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨384809684211,384810041689⟩,⟨601316804898,601326906117⟩,⟨-169357571541,-169352376304⟩,⟨-15887211026953,-15886885187557⟩,⟨-2507808568925,-2507609370479⟩,⟨-1162073947884,-1161936896247⟩⟩⟩
noncomputable def centerBoxes125 := centerStep124.proposed :: centerBoxes124
theorem centerAccepted124 : StepValid centerStep124.shape centerBoxes124 centerStep124.proposed := by
  dsimp only [StepValid,centerStep124]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-384810041689,-384809684211⟩,⟨-601326906117,-601316804898⟩,⟨169352376304,169357571541⟩,⟨15886885187557,15887211026953⟩,⟨2507609370479,2507808568925⟩,⟨1161936896247,1162073947884⟩⟩⟩
noncomputable def centerBoxes126 := centerStep125.proposed :: centerBoxes125
theorem centerAccepted125 : StepValid centerStep125.shape centerBoxes125 centerStep125.proposed := by
  dsimp only [StepValid,centerStep125]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨60719999500,60720558452⟩,⟨-485068130811,-485054749998⟩,⟨-100206260008,-100198437681⟩,⟨3053409163911,3053815583317⟩,⟨-445762500867,-445488778892⟩,⟨349298482980,349507107902⟩⟩⟩
noncomputable def centerBoxes127 := centerStep126.proposed :: centerBoxes126
theorem centerAccepted126 : StepValid centerStep126.shape centerBoxes126 centerStep126.proposed := by
  dsimp only [StepValid,centerStep126]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨304177282733,304177282738⟩,⟨1352729509950,1352729509959⟩,⟨241545844259,241545844264⟩,⟨-3725645557270,-3725645557265⟩,⟨-1330516108252,-1330516108244⟩,⟨-289900310038,-289900310036⟩⟩⟩
noncomputable def centerBoxes128 := centerStep127.proposed :: centerBoxes127
theorem centerAccepted127 : StepValid centerStep127.shape centerBoxes127 centerStep127.proposed := by
  dsimp only [StepValid,centerStep127]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1771751802290,-1771750208805⟩,⟨-3270785533953,-3270751265120⟩,⟨325886511839,325905417514⟩,⟨26989793509539,26990796220795⟩,⟨-4467193329180,-4466535980272⟩,⟨999340256605,999847763714⟩⟩⟩
noncomputable def centerBoxes129 := centerStep128.proposed :: centerBoxes128
theorem centerAccepted128 : StepValid centerStep128.shape centerBoxes128 centerStep128.proposed := by
  dsimp only [StepValid,centerStep128]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-254180805968,-254180576328⟩,⟨-1540165345917,-1540159450431⟩,⟨-204675297573,-204672350812⟩,⟨3485844785421,3486033586014⟩,⟨238939002661,239050770921⟩,⟨387582787509,387661143185⟩⟩⟩
noncomputable def centerBoxes130 := centerStep129.proposed :: centerBoxes129
theorem centerAccepted129 : StepValid centerStep129.shape centerBoxes129 centerStep129.proposed := by
  dsimp only [StepValid,centerStep129]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨49996476765,49996706410⟩,⟨-187435835967,-187429940472⟩,⟨36870546686,36873493452⟩,⟨-239800771849,-239611971251⟩,⟨-1091577105591,-1091465337323⟩,⟨97682477471,97760833149⟩⟩⟩
noncomputable def centerBoxes131 := centerStep130.proposed :: centerBoxes130
theorem centerAccepted130 : StepValid centerStep130.shape centerBoxes130 centerStep130.proposed := by
  dsimp only [StepValid,centerStep130]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨3212965718,3213011871⟩,⟨-36577742986,-36576381377⟩,⟨-77275434,-76587074⟩,⟨297289426747,297336079573⟩,⟨-116514252055,-116486619949⟩,⟨12998128838,13016705255⟩⟩⟩
noncomputable def centerBoxes132 := centerStep131.proposed :: centerBoxes131
theorem centerAccepted131 : StepValid centerStep131.shape centerBoxes131 centerStep131.proposed := by
  dsimp only [StepValid,centerStep131]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨2273416329,2273437215⟩,⟨-17046067046,-17045452592⟩,⟨3353120392,3353403784⟩,⟨42092749567,42114039848⟩,⟨-111843608726,-111831588122⟩,⟨11356345435,11363907458⟩⟩⟩
noncomputable def centerBoxes133 := centerStep132.proposed :: centerBoxes132
theorem centerAccepted132 : StepValid centerStep132.shape centerBoxes132 centerStep132.proposed := by
  dsimp only [StepValid,centerStep132]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨3187663504,3187692870⟩,⟨-35853680660,-35852708695⟩,⟨-507028024,-506582695⟩,⟨276274420417,276311084302⟩,⟨-104485591153,-104465550864⟩,⟨7777646147,7789614490⟩⟩⟩
noncomputable def centerBoxes134 := centerStep133.proposed :: centerBoxes133
theorem centerAccepted133 : StepValid centerStep133.shape centerBoxes133 centerStep133.proposed := by
  dsimp only [StepValid,centerStep133]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-3187692870,-3187663504⟩,⟨35852708695,35853680660⟩,⟨506582695,507028024⟩,⟨-276311084302,-276274420417⟩,⟨104465550864,104485591153⟩,⟨-7789614490,-7777646147⟩⟩⟩
noncomputable def centerBoxes135 := centerStep134.proposed :: centerBoxes134
theorem centerAccepted134 : StepValid centerStep134.shape centerBoxes134 centerStep134.proposed := by
  dsimp only [StepValid,centerStep134]
  exact ⟨by decide,by decide⟩
noncomputable def centerStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨25272848,25348367⟩,⟨-725034291,-722700717⟩,⟨429307261,430440950⟩,⟨20978342445,21061659156⟩,⟨-12048701191,-12001028796⟩,⟨5208514348,5239059108⟩⟩⟩
noncomputable def centerBoxes136 := centerStep135.proposed :: centerBoxes135
theorem centerAccepted135 : StepValid centerStep135.shape centerBoxes135 centerStep135.proposed := by
  dsimp only [StepValid,centerStep135]
  exact ⟨by decide,by decide⟩
noncomputable def centerProgram : List (Instruction 40) := [centerStep0,centerStep1,centerStep2,centerStep3,centerStep4,centerStep5,centerStep6,centerStep7,centerStep8,centerStep9,centerStep10,centerStep11,centerStep12,centerStep13,centerStep14,centerStep15,centerStep16,centerStep17,centerStep18,centerStep19,centerStep20,centerStep21,centerStep22,centerStep23,centerStep24,centerStep25,centerStep26,centerStep27,centerStep28,centerStep29,centerStep30,centerStep31,centerStep32,centerStep33,centerStep34,centerStep35,centerStep36,centerStep37,centerStep38,centerStep39,centerStep40,centerStep41,centerStep42,centerStep43,centerStep44,centerStep45,centerStep46,centerStep47,centerStep48,centerStep49,centerStep50,centerStep51,centerStep52,centerStep53,centerStep54,centerStep55,centerStep56,centerStep57,centerStep58,centerStep59,centerStep60,centerStep61,centerStep62,centerStep63,centerStep64,centerStep65,centerStep66,centerStep67,centerStep68,centerStep69,centerStep70,centerStep71,centerStep72,centerStep73,centerStep74,centerStep75,centerStep76,centerStep77,centerStep78,centerStep79,centerStep80,centerStep81,centerStep82,centerStep83,centerStep84,centerStep85,centerStep86,centerStep87,centerStep88,centerStep89,centerStep90,centerStep91,centerStep92,centerStep93,centerStep94,centerStep95,centerStep96,centerStep97,centerStep98,centerStep99,centerStep100,centerStep101,centerStep102,centerStep103,centerStep104,centerStep105,centerStep106,centerStep107,centerStep108,centerStep109,centerStep110,centerStep111,centerStep112,centerStep113,centerStep114,centerStep115,centerStep116,centerStep117,centerStep118,centerStep119,centerStep120,centerStep121,centerStep122,centerStep123,centerStep124,centerStep125,centerStep126,centerStep127,centerStep128,centerStep129,centerStep130,centerStep131,centerStep132,centerStep133,centerStep134,centerStep135]
theorem centerAccepted : Accepted centerProgram centerInitial :=
  ⟨centerAccepted0,⟨centerAccepted1,⟨centerAccepted2,⟨centerAccepted3,⟨centerAccepted4,⟨centerAccepted5,⟨centerAccepted6,⟨centerAccepted7,⟨centerAccepted8,⟨centerAccepted9,⟨centerAccepted10,⟨centerAccepted11,⟨centerAccepted12,⟨centerAccepted13,⟨centerAccepted14,⟨centerAccepted15,⟨centerAccepted16,⟨centerAccepted17,⟨centerAccepted18,⟨centerAccepted19,⟨centerAccepted20,⟨centerAccepted21,⟨centerAccepted22,⟨centerAccepted23,⟨centerAccepted24,⟨centerAccepted25,⟨centerAccepted26,⟨centerAccepted27,⟨centerAccepted28,⟨centerAccepted29,⟨centerAccepted30,⟨centerAccepted31,⟨centerAccepted32,⟨centerAccepted33,⟨centerAccepted34,⟨centerAccepted35,⟨centerAccepted36,⟨centerAccepted37,⟨centerAccepted38,⟨centerAccepted39,⟨centerAccepted40,⟨centerAccepted41,⟨centerAccepted42,⟨centerAccepted43,⟨centerAccepted44,⟨centerAccepted45,⟨centerAccepted46,⟨centerAccepted47,⟨centerAccepted48,⟨centerAccepted49,⟨centerAccepted50,⟨centerAccepted51,⟨centerAccepted52,⟨centerAccepted53,⟨centerAccepted54,⟨centerAccepted55,⟨centerAccepted56,⟨centerAccepted57,⟨centerAccepted58,⟨centerAccepted59,⟨centerAccepted60,⟨centerAccepted61,⟨centerAccepted62,⟨centerAccepted63,⟨centerAccepted64,⟨centerAccepted65,⟨centerAccepted66,⟨centerAccepted67,⟨centerAccepted68,⟨centerAccepted69,⟨centerAccepted70,⟨centerAccepted71,⟨centerAccepted72,⟨centerAccepted73,⟨centerAccepted74,⟨centerAccepted75,⟨centerAccepted76,⟨centerAccepted77,⟨centerAccepted78,⟨centerAccepted79,⟨centerAccepted80,⟨centerAccepted81,⟨centerAccepted82,⟨centerAccepted83,⟨centerAccepted84,⟨centerAccepted85,⟨centerAccepted86,⟨centerAccepted87,⟨centerAccepted88,⟨centerAccepted89,⟨centerAccepted90,⟨centerAccepted91,⟨centerAccepted92,⟨centerAccepted93,⟨centerAccepted94,⟨centerAccepted95,⟨centerAccepted96,⟨centerAccepted97,⟨centerAccepted98,⟨centerAccepted99,⟨centerAccepted100,⟨centerAccepted101,⟨centerAccepted102,⟨centerAccepted103,⟨centerAccepted104,⟨centerAccepted105,⟨centerAccepted106,⟨centerAccepted107,⟨centerAccepted108,⟨centerAccepted109,⟨centerAccepted110,⟨centerAccepted111,⟨centerAccepted112,⟨centerAccepted113,⟨centerAccepted114,⟨centerAccepted115,⟨centerAccepted116,⟨centerAccepted117,⟨centerAccepted118,⟨centerAccepted119,⟨centerAccepted120,⟨centerAccepted121,⟨centerAccepted122,⟨centerAccepted123,⟨centerAccepted124,⟨centerAccepted125,⟨centerAccepted126,⟨centerAccepted127,⟨centerAccepted128,⟨centerAccepted129,⟨centerAccepted130,⟨centerAccepted131,⟨centerAccepted132,⟨centerAccepted133,⟨centerAccepted134,⟨centerAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def center_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨58180059218,58180359372⟩,⟨-197564315373,-197556697085⟩,⟨94615794274,94619397534⟩,⟨-698708545503,-698483497072⟩,⟨-1252823960774,-1252687268171⟩,⟨212982532660,213079054311⟩⟩
theorem center_m11_eq : (finalBoxes centerProgram centerInitial).getD 14 (zeroBox 40)=center_m11 := rfl
noncomputable def center_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨25272848,25348367⟩,⟨-725034291,-722700717⟩,⟨429307261,430440950⟩,⟨20978342445,21061659156⟩,⟨-12048701191,-12001028796⟩,⟨5208514348,5239059108⟩⟩
theorem center_kdet_eq : (finalBoxes centerProgram centerInitial).getD 0 (zeroBox 40)=center_kdet := rfl
noncomputable def wholeInitial : List (DyadicBivariateJetEnclosure 40) := [⟨⟨150323855360,150753352090⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨179529632972,187260574106⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩]
noncomputable def wholeBoxes0 := wholeInitial
noncomputable def wholeStep0 : Instruction 40 := ⟨.inv 3,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes1 := wholeStep0.proposed :: wholeBoxes0
theorem wholeAccepted0 : StepValid wholeStep0.shape wholeBoxes0 wholeStep0.proposed := by
  dsimp only [StepValid,wholeStep0]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep1 : Instruction 40 := ⟨.mul 3 0,⟨⟨549755813888,549755813888⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes2 := wholeStep1.proposed :: wholeBoxes1
theorem wholeAccepted1 : StepValid wholeStep1.shape wholeBoxes1 wholeStep1.proposed := by
  dsimp only [StepValid,wholeStep1]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep2 : Instruction 40 := ⟨.neg 2,⟨⟨-150753352090,-150323855360⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes3 := wholeStep2.proposed :: wholeBoxes2
theorem wholeAccepted2 : StepValid wholeStep2.shape wholeBoxes2 wholeStep2.proposed := by
  dsimp only [StepValid,wholeStep2]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep3 : Instruction 40 := ⟨.add 1 0,⟨⟨399002461798,399431958528⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes4 := wholeStep3.proposed :: wholeBoxes3
theorem wholeAccepted3 : StepValid wholeStep3.shape wholeBoxes3 wholeStep3.proposed := by
  dsimp only [StepValid,wholeStep3]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep4 : Instruction 40 := ⟨.mul 5 0,⟨⟨65149620715,68028255437⟩,⟨-187260574106,-179529632972⟩,⟨399002461798,399431958528⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes5 := wholeStep4.proposed :: wholeBoxes4
theorem wholeAccepted4 : StepValid wholeStep4.shape wholeBoxes4 wholeStep4.proposed := by
  dsimp only [StepValid,wholeStep4]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep5 : Instruction 40 := ⟨.add 5 0,⟨⟨215473476075,218781607527⟩,⟨912251053670,919981994804⟩,⟨399002461798,399431958528⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes6 := wholeStep5.proposed :: wholeBoxes5
theorem wholeAccepted5 : StepValid wholeStep5.shape wholeBoxes5 wholeStep5.proposed := by
  dsimp only [StepValid,wholeStep5]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep6 : Instruction 40 := ⟨.add 0 3,⟨⟨64720123985,68457752167⟩,⟨-187260574106,-179529632972⟩,⟨399002461798,399431958528⟩,⟨0,0⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes7 := wholeStep6.proposed :: wholeBoxes6
theorem wholeAccepted6 : StepValid wholeStep6.shape wholeBoxes6 wholeStep6.proposed := by
  dsimp only [StepValid,wholeStep6]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep7 : Instruction 40 := ⟨.log 7,⟨⟨-2187840582080,-2184703558912⟩,⟨8019230105695,8042142191734⟩,⟨0,0⟩,⟨-58822525745262,-58487832109754⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes8 := wholeStep7.proposed :: wholeBoxes7
theorem wholeAccepted7 : StepValid wholeStep7.shape wholeBoxes7 wholeStep7.proposed := by
  dsimp only [StepValid,wholeStep7]
  exact ⟨by decide,by decide,lc19,by decide⟩
noncomputable def wholeStep8 : Instruction 40 := ⟨.mul 8 0,⟨⟨-299973454810,-298689939695⟩,⟨-1091461466068,-1082050469339⟩,⟨0,0⟩,⟨7973340470514,8087901087213⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes9 := wholeStep8.proposed :: wholeBoxes8
theorem wholeAccepted8 : StepValid wholeStep8.shape wholeBoxes8 wholeStep8.proposed := by
  dsimp only [StepValid,wholeStep8]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep9 : Instruction 40 := ⟨.neg 0,⟨⟨298689939695,299973454810⟩,⟨1082050469339,1091461466068⟩,⟨0,0⟩,⟨-8087901087213,-7973340470514⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes10 := wholeStep9.proposed :: wholeBoxes9
theorem wholeAccepted9 : StepValid wholeStep9.shape wholeBoxes9 wholeStep9.proposed := by
  dsimp only [StepValid,wholeStep9]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep10 : Instruction 40 := ⟨.add 12 7,⟨⟨948758275686,949187772416⟩,⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes11 := wholeStep10.proposed :: wholeBoxes10
theorem wholeAccepted10 : StepValid wholeStep10.shape wholeBoxes10 wholeStep10.proposed := by
  dsimp only [StepValid,wholeStep10]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep11 : Instruction 40 := ⟨.log 0,⟨⟨-162142048512,-161644419328⟩,⟨-1274218998239,-1273642428555⟩,⟨0,0⟩,⟨-1476686571071,-1475350505475⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes12 := wholeStep11.proposed :: wholeBoxes11
theorem wholeAccepted11 : StepValid wholeStep11.shape wholeBoxes11 wholeStep11.proposed := by
  dsimp only [StepValid,wholeStep11]
  exact ⟨by decide,by decide,lc20,by decide⟩
noncomputable def wholeStep12 : Instruction 40 := ⟨.mul 1 0,⟨⟨-139974190317,-139481454021⟩,⟨-938364950246,-936872062689⟩,⟨0,0⟩,⟨1272489028177,1275371876716⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes13 := wholeStep12.proposed :: wholeBoxes12
theorem wholeAccepted12 : StepValid wholeStep12.shape wholeBoxes12 wholeStep12.proposed := by
  dsimp only [StepValid,wholeStep12]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep13 : Instruction 40 := ⟨.neg 0,⟨⟨139481454021,139974190317⟩,⟨936872062689,938364950246⟩,⟨0,0⟩,⟨-1275371876716,-1272489028177⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes14 := wholeStep13.proposed :: wholeBoxes13
theorem wholeAccepted13 : StepValid wholeStep13.shape wholeBoxes13 wholeStep13.proposed := by
  dsimp only [StepValid,wholeStep13]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep14 : Instruction 40 := ⟨.add 4 0,⟨⟨438171393716,439947645127⟩,⟨2018922532028,2029826416314⟩,⟨0,0⟩,⟨-9363272963929,-9245829498691⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes15 := wholeStep14.proposed :: wholeBoxes14
theorem wholeAccepted14 : StepValid wholeStep14.shape wholeBoxes14 wholeStep14.proposed := by
  dsimp only [StepValid,wholeStep14]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep15 : Instruction 40 := ⟨.log 9,⟨⟨-1791966016000,-1775213614528⟩,⟨4584620491177,4694456687001⟩,⟨2005231843833,2038209485951⟩,⟨-20043374739660,-19116437259183⟩,⟨-14312860703352,-13886910862142⟩,⟨-3778311937477,-3657037038939⟩⟩⟩
noncomputable def wholeBoxes16 := wholeStep15.proposed :: wholeBoxes15
theorem wholeAccepted15 : StepValid wholeStep15.shape wholeBoxes15 wholeStep15.proposed := by
  dsimp only [StepValid,wholeStep15]
  exact ⟨by decide,by decide,lc21,by decide⟩
noncomputable def wholeStep16 : Instruction 40 := ⟨.mul 10 0,⟨⟨-356566675341,-347892135594⟩,⟨-600914387454,-538766207586⟩,⟨-258018389704,-238644001546⟩,⟨3619359633100,4109593708974⟩,⟨2254661979120,2481336717384⟩,⟨703548471310,764209772400⟩⟩⟩
noncomputable def wholeBoxes17 := wholeStep16.proposed :: wholeBoxes16
theorem wholeAccepted16 : StepValid wholeStep16.shape wholeBoxes16 wholeStep16.proposed := by
  dsimp only [StepValid,wholeStep16]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep17 : Instruction 40 := ⟨.neg 0,⟨⟨347892135594,356566675341⟩,⟨538766207586,600914387454⟩,⟨238644001546,258018389704⟩,⟨-4109593708974,-3619359633100⟩,⟨-2481336717384,-2254661979120⟩,⟨-764209772400,-703548471310⟩⟩⟩
noncomputable def wholeBoxes18 := wholeStep17.proposed :: wholeBoxes17
theorem wholeAccepted17 : StepValid wholeStep17.shape wholeBoxes17 wholeStep17.proposed := by
  dsimp only [StepValid,wholeStep17]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep18 : Instruction 40 := ⟨.neg 12,⟨⟨-218781607527,-215473476075⟩,⟨-919981994804,-912251053670⟩,⟨-399431958528,-399002461798⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes19 := wholeStep18.proposed :: wholeBoxes18
theorem wholeAccepted18 : StepValid wholeStep18.shape wholeBoxes18 wholeStep18.proposed := by
  dsimp only [StepValid,wholeStep18]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep19 : Instruction 40 := ⟨.add 21 0,⟨⟨880730020249,884038151701⟩,⟨-919981994804,-912251053670⟩,⟨-399431958528,-399002461798⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes20 := wholeStep19.proposed :: wholeBoxes19
theorem wholeAccepted19 : StepValid wholeStep19.shape wholeBoxes19 wholeStep19.proposed := by
  dsimp only [StepValid,wholeStep19]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep20 : Instruction 40 := ⟨.log 0,⟨⟨-243948923520,-239826757952⟩,⟨-1148514161407,-1134601079185⟩,⟨-498654607894,-496254426818⟩,⟨-1199700617646,-1170810363771⟩,⟨846625706146,860548914179⟩,⟨-226151694709,-223979856070⟩⟩⟩
noncomputable def wholeBoxes21 := wholeStep20.proposed :: wholeBoxes20
theorem wholeAccepted20 : StepValid wholeStep20.shape wholeBoxes20 wholeStep20.proposed := by
  dsimp only [StepValid,wholeStep20]
  exact ⟨by decide,by decide,lc22,by decide⟩
noncomputable def wholeStep21 : Instruction 40 := ⟨.mul 1 0,⟨⟨-196141768773,-192105858684⟩,⟨-724456298316,-704720709249⟩,⟨-313901392541,-308887297321⟩,⟨918135759406,984124984055⟩,⟨1257686785565,1286545997843⟩,⟨178339859996,182891553913⟩⟩⟩
noncomputable def wholeBoxes22 := wholeStep21.proposed :: wholeBoxes21
theorem wholeAccepted21 : StepValid wholeStep21.shape wholeBoxes21 wholeStep21.proposed := by
  dsimp only [StepValid,wholeStep21]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep22 : Instruction 40 := ⟨.neg 0,⟨⟨192105858684,196141768773⟩,⟨704720709249,724456298316⟩,⟨308887297321,313901392541⟩,⟨-984124984055,-918135759406⟩,⟨-1286545997843,-1257686785565⟩,⟨-182891553913,-178339859996⟩⟩⟩
noncomputable def wholeBoxes23 := wholeStep22.proposed :: wholeBoxes22
theorem wholeAccepted22 : StepValid wholeStep22.shape wholeBoxes22 wholeStep22.proposed := by
  dsimp only [StepValid,wholeStep22]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep23 : Instruction 40 := ⟨.add 5 0,⟨⟨539997994278,552708444114⟩,⟨1243486916835,1325370685770⟩,⟨547531298867,571919782245⟩,⟨-5093718693029,-4537495392506⟩,⟨-3767882715227,-3512348764685⟩,⟨-947101326313,-881888331306⟩⟩⟩
noncomputable def wholeBoxes24 := wholeStep23.proposed :: wholeBoxes23
theorem wholeAccepted23 : StepValid wholeStep23.shape wholeBoxes23 wholeStep23.proposed := by
  dsimp only [StepValid,wholeStep23]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep24 : Instruction 40 := ⟨.add 9 0,⟨⟨978169387994,992656089241⟩,⟨3262409448863,3355197102084⟩,⟨547531298867,571919782245⟩,⟨-14456991656958,-13783324891197⟩,⟨-3767882715227,-3512348764685⟩,⟨-947101326313,-881888331306⟩⟩⟩
noncomputable def wholeBoxes25 := wholeStep24.proposed :: wholeBoxes24
theorem wholeAccepted24 : StepValid wholeStep24.shape wholeBoxes24 wholeStep24.proposed := by
  dsimp only [StepValid,wholeStep24]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep25 : Instruction 40 := ⟨.mul 28 18,⟨⟨129440247970,136915504334⟩,⟨-374521148212,-359059265944⟩,⟨798004923596,798863917056⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes26 := wholeStep25.proposed :: wholeBoxes25
theorem wholeAccepted25 : StepValid wholeStep25.shape wholeBoxes25 wholeStep25.proposed := by
  dsimp only [StepValid,wholeStep25]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep26 : Instruction 40 := ⟨.inv 0,⟨⟨8829721845566,9339643878733⟩,⟨23155839506857,27023234304721⟩,⟨-57641302530589,-51463576320442⟩,⟨121451822072198,156377523976193⟩,⟨-191741894815230,-111256690086298⟩,⟨599905576645087,711487461526970⟩⟩⟩
noncomputable def wholeBoxes27 := wholeStep26.proposed :: wholeBoxes26
theorem wholeAccepted26 : StepValid wholeStep26.shape wholeBoxes26 wholeStep26.proposed := by
  dsimp only [StepValid,wholeStep26]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep27 : Instruction 40 := ⟨.mul 2 0,⟨⟨7855272646188,8431974827151⟩,⟨46799415339333,52897234272669⟩,⟨-47642461939209,-40925959056019⟩,⟨122658966611530,195416515776140⟩,⟨-369476607845567,-265828099554452⟩,⟨465689735640850,584004460383715⟩⟩⟩
noncomputable def wholeBoxes28 := wholeStep27.proposed :: wholeBoxes27
theorem wholeAccepted27 : StepValid wholeStep27.shape wholeBoxes27 wholeStep27.proposed := by
  dsimp only [StepValid,wholeStep27]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep28 : Instruction 40 := ⟨.contact 0,⟨⟨98799593472,105959608576⟩,⟨-704621912317,-541517347176⟩,⟨473555419827,634625289973⟩,⟨3283703111768,7907821845830⟩,⟨-5324659331676,-226316215475⟩,⟨-3277402666697,2177548916507⟩⟩⟩
noncomputable def wholeBoxes29 := wholeStep28.proposed :: wholeBoxes28
theorem wholeAccepted28 : StepValid wholeStep28.shape wholeBoxes28 wholeStep28.proposed := by
  dsimp only [StepValid,wholeStep28]
  exact ⟨by decide,by decide,(⟨⟨98799593472,105959608576⟩,⟨-14646134083,-12722479876⟩,⟨3249342385,4029776153⟩⟩ : DyadicJetEnclosure 40),brwhole28_jet,by decide⟩
noncomputable def wholeStep29 : Instruction 40 := ⟨.log 32,⟨⟨762123383616,762123402880⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes30 := wholeStep29.proposed :: wholeBoxes29
theorem wholeAccepted29 : StepValid wholeStep29.shape wholeBoxes29 wholeStep29.proposed := by
  dsimp only [StepValid,wholeStep29]
  exact ⟨by decide,by decide,lc4,by decide⟩
noncomputable def wholeStep30 : Instruction 40 := ⟨.add 32 1,⟨⟨1198311221248,1205471236352⟩,⟨-704621912317,-541517347176⟩,⟨473555419827,634625289973⟩,⟨3283703111768,7907821845830⟩,⟨-5324659331676,-226316215475⟩,⟨-3277402666697,2177548916507⟩⟩⟩
noncomputable def wholeBoxes31 := wholeStep30.proposed :: wholeBoxes30
theorem wholeAccepted30 : StepValid wholeStep30.shape wholeBoxes30 wholeStep30.proposed := by
  dsimp only [StepValid,wholeStep30]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep31 : Instruction 40 := ⟨.log 0,⟨⟨94609834752,101159964288⟩,⟨-646526521693,-493918562224⟩,⟨431930414259,582301052710⟩,⟨2614903543675,7033953357335⟩,⟨-4691616164841,135976999677⟩,⟨-3315570483626,1828333265570⟩⟩⟩
noncomputable def wholeBoxes32 := wholeStep31.proposed :: wholeBoxes31
theorem wholeAccepted31 : StepValid wholeStep31.shape wholeBoxes31 wholeStep31.proposed := by
  dsimp only [StepValid,wholeStep31]
  exact ⟨by decide,by decide,lc32,by decide⟩
noncomputable def wholeStep32 : Instruction 40 := ⟨.mul 1 0,⟨⟨103111257543,110908719962⟩,⟨-773660442907,-584896972420⟩,⟨511490781918,696805583730⟩,⟨3618942907195,9268021070774⟩,⟨-6379973319026,-295850442870⟩,⟨-3564565131010,2877068147059⟩⟩⟩
noncomputable def wholeBoxes33 := wholeStep32.proposed :: wholeBoxes32
theorem wholeAccepted32 : StepValid wholeStep32.shape wholeBoxes32 wholeStep32.proposed := by
  dsimp only [StepValid,wholeStep32]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep33 : Instruction 40 := ⟨.neg 4,⟨⟨-105959608576,-98799593472⟩,⟨541517347176,704621912317⟩,⟨-634625289973,-473555419827⟩,⟨-7907821845830,-3283703111768⟩,⟨226316215475,5324659331676⟩,⟨-2177548916507,3277402666697⟩⟩⟩
noncomputable def wholeBoxes34 := wholeStep33.proposed :: wholeBoxes33
theorem wholeAccepted33 : StepValid wholeStep33.shape wholeBoxes33 wholeStep33.proposed := by
  dsimp only [StepValid,wholeStep33]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep34 : Instruction 40 := ⟨.add 36 0,⟨⟨993552019200,1000712034304⟩,⟨541517347176,704621912317⟩,⟨-634625289973,-473555419827⟩,⟨-7907821845830,-3283703111768⟩,⟨226316215475,5324659331676⟩,⟨-2177548916507,3277402666697⟩⟩⟩
noncomputable def wholeBoxes35 := wholeStep34.proposed :: wholeBoxes34
theorem wholeAccepted34 : StepValid wholeStep34.shape wholeBoxes34 wholeStep34.proposed := by
  dsimp only [StepValid,wholeStep34]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep35 : Instruction 40 := ⟨.log 0,⟨⟨-111418972672,-103523775680⟩,⟨594980972999,779767914319⟩,⟨-702306343425,-520309212487⟩,⟨-9304176782074,-3929864073637⟩,⟨530216242772,6390591700446⟩,⟨-2858372451283,3380708777086⟩⟩⟩
noncomputable def wholeBoxes36 := wholeStep35.proposed :: wholeBoxes35
theorem wholeAccepted35 : StepValid wholeStep35.shape wholeBoxes35 wholeStep35.proposed := by
  dsimp only [StepValid,wholeStep35]
  exact ⟨by decide,by decide,lc33,by decide⟩
noncomputable def wholeStep36 : Instruction 40 := ⟨.mul 1 0,⟨⟨-101407119294,-93547220205⟩,⟨466239996527,658713557139⟩,⟨-594611414799,-405857436666⟩,⟨-7572885164824,-1750377015473⟩,⟨-960600601883,5282527111306⟩,⟨-2485450798814,4108313946400⟩⟩⟩
noncomputable def wholeBoxes37 := wholeStep36.proposed :: wholeBoxes36
theorem wholeAccepted36 : StepValid wholeStep36.shape wholeBoxes36 wholeStep36.proposed := by
  dsimp only [StepValid,wholeStep36]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep37 : Instruction 40 := ⟨.add 4 0,⟨⟨1704138249,17361499757⟩,⟨-307420446380,73816584719⟩,⟨-83120632881,290948147064⟩,⟨-3953942257629,7517644055301⟩,⟨-7340573920909,4986676668436⟩,⟨-6050015929824,6985382093459⟩⟩⟩
noncomputable def wholeBoxes38 := wholeStep37.proposed :: wholeBoxes37
theorem wholeAccepted37 : StepValid wholeStep37.shape wholeBoxes37 wholeStep37.proposed := by
  dsimp only [StepValid,wholeStep37]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep38 : Instruction 40 := ⟨.mul 0 37,⟨⟨852069124,8680749879⟩,⟨-153710223190,36908292360⟩,⟨-41560316441,145474073532⟩,⟨-1976971128815,3758822027651⟩,⟨-3670286960455,2493338334218⟩,⟨-3025007964912,3492691046730⟩⟩⟩
noncomputable def wholeBoxes39 := wholeStep38.proposed :: wholeBoxes38
theorem wholeAccepted38 : StepValid wholeStep38.shape wholeBoxes38 wholeStep38.proposed := by
  dsimp only [StepValid,wholeStep38]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep39 : Instruction 40 := ⟨.neg 0,⟨⟨-8680749879,-852069124⟩,⟨-36908292360,153710223190⟩,⟨-145474073532,41560316441⟩,⟨-3758822027651,1976971128815⟩,⟨-2493338334218,3670286960455⟩,⟨-3492691046730,3025007964912⟩⟩⟩
noncomputable def wholeBoxes40 := wholeStep39.proposed :: wholeBoxes39
theorem wholeAccepted39 : StepValid wholeStep39.shape wholeBoxes39 wholeStep39.proposed := by
  dsimp only [StepValid,wholeStep39]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep40 : Instruction 40 := ⟨.add 10 0,⟨⟨753442633737,761271333756⟩,⟨-36908292360,153710223190⟩,⟨-145474073532,41560316441⟩,⟨-3758822027651,1976971128815⟩,⟨-2493338334218,3670286960455⟩,⟨-3492691046730,3025007964912⟩⟩⟩
noncomputable def wholeBoxes41 := wholeStep40.proposed :: wholeBoxes40
theorem wholeAccepted40 : StepValid wholeStep40.shape wholeBoxes40 wholeStep40.proposed := by
  dsimp only [StepValid,wholeStep40]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep41 : Instruction 40 := ⟨.mul 12 12,⟨⟨8877904902,10211295967⟩,⟨-135808408274,-97319014018⟩,⟨85105208136,122317300918⟩,⟨1123534402389,2427262637485⟩,⟨-1839670774664,-507131380382⟩,⟨-223767652755,1152296116783⟩⟩⟩
noncomputable def wholeBoxes42 := wholeStep41.proposed :: wholeBoxes41
theorem wholeAccepted41 : StepValid wholeStep41.shape wholeBoxes41 wholeStep41.proposed := by
  dsimp only [StepValid,wholeStep41]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep42 : Instruction 40 := ⟨.neg 0,⟨⟨-10211295967,-8877904902⟩,⟨97319014018,135808408274⟩,⟨-122317300918,-85105208136⟩,⟨-2427262637485,-1123534402389⟩,⟨507131380382,1839670774664⟩,⟨-1152296116783,223767652755⟩⟩⟩
noncomputable def wholeBoxes43 := wholeStep42.proposed :: wholeBoxes42
theorem wholeAccepted42 : StepValid wholeStep42.shape wholeBoxes42 wholeStep42.proposed := by
  dsimp only [StepValid,wholeStep42]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep43 : Instruction 40 := ⟨.add 45 0,⟨⟨1089300331809,1090633722874⟩,⟨97319014018,135808408274⟩,⟨-122317300918,-85105208136⟩,⟨-2427262637485,-1123534402389⟩,⟨507131380382,1839670774664⟩,⟨-1152296116783,223767652755⟩⟩⟩
noncomputable def wholeBoxes44 := wholeStep43.proposed :: wholeBoxes43
theorem wholeAccepted43 : StepValid wholeStep43.shape wholeBoxes43 wholeStep43.proposed := by
  dsimp only [StepValid,wholeStep43]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep44 : Instruction 40 := ⟨.log 0,⟨⟨-10259008384,-8913940864⟩,⟨98111203855,137081500563⟩,⟨-123463925155,-85797975954⟩,⟨-2467106853366,-1141434744906⟩,⟨518915390285,1872309029589⟩,⟨-1176961684206,219170234032⟩⟩⟩
noncomputable def wholeBoxes45 := wholeStep44.proposed :: wholeBoxes44
theorem wholeAccepted44 : StepValid wholeStep44.shape wholeBoxes44 wholeStep44.proposed := by
  dsimp only [StepValid,wholeStep44]
  exact ⟨by decide,by decide,lc30,by decide⟩
noncomputable def wholeStep45 : Instruction 40 := ⟨.mul 0 44,⟨⟨-5129504192,-4456970432⟩,⟨49055601927,68540750282⟩,⟨-61731962578,-42898987977⟩,⟨-1233553426683,-570717372453⟩,⟨259457695142,936154514795⟩,⟨-588480842103,109585117016⟩⟩⟩
noncomputable def wholeBoxes46 := wholeStep45.proposed :: wholeBoxes45
theorem wholeAccepted45 : StepValid wholeStep45.shape wholeBoxes45 wholeStep45.proposed := by
  dsimp only [StepValid,wholeStep45]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep46 : Instruction 40 := ⟨.neg 0,⟨⟨4456970432,5129504192⟩,⟨-68540750282,-49055601927⟩,⟨42898987977,61731962578⟩,⟨570717372453,1233553426683⟩,⟨-936154514795,-259457695142⟩,⟨-109585117016,588480842103⟩⟩⟩
noncomputable def wholeBoxes47 := wholeStep46.proposed :: wholeBoxes46
theorem wholeAccepted46 : StepValid wholeStep46.shape wholeBoxes46 wholeStep46.proposed := by
  dsimp only [StepValid,wholeStep46]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep47 : Instruction 40 := ⟨.add 17 0,⟨⟨766580354048,767252907072⟩,⟨-68540750282,-49055601927⟩,⟨42898987977,61731962578⟩,⟨570717372453,1233553426683⟩,⟨-936154514795,-259457695142⟩,⟨-109585117016,588480842103⟩⟩⟩
noncomputable def wholeBoxes48 := wholeStep47.proposed :: wholeBoxes47
theorem wholeAccepted47 : StepValid wholeStep47.shape wholeBoxes47 wholeStep47.proposed := by
  dsimp only [StepValid,wholeStep47]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep48 : Instruction 40 := ⟨.mul 51 51,⟨⟨4398046511104,4398046511104⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes49 := wholeStep48.proposed :: wholeBoxes48
theorem wholeAccepted48 : StepValid wholeStep48.shape wholeBoxes48 wholeStep48.proposed := by
  dsimp only [StepValid,wholeStep48]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep49 : Instruction 40 := ⟨.inv 0,⟨⟨274877906944,274877906944⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes50 := wholeStep49.proposed :: wholeBoxes49
theorem wholeAccepted49 : StepValid wholeStep49.shape wholeBoxes49 wholeStep49.proposed := by
  dsimp only [StepValid,wholeStep49]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep50 : Instruction 40 := ⟨.mul 6 0,⟨⟨272325082952,272658430719⟩,⟨24329753504,33952102069⟩,⟨-30579325230,-21276302034⟩,⟨-606815659372,-280883600597⟩,⟨126782845095,459917693666⟩,⟨-288074029196,55941913189⟩⟩⟩
noncomputable def wholeBoxes51 := wholeStep50.proposed :: wholeBoxes50
theorem wholeAccepted50 : StepValid wholeStep50.shape wholeBoxes50 wholeStep50.proposed := by
  dsimp only [StepValid,wholeStep50]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep51 : Instruction 40 := ⟨.mul 54 3,⟨⟨1533160708096,1534505814144⟩,⟨-137081500564,-98111203854⟩,⟨85797975954,123463925156⟩,⟨1141434744906,2467106853366⟩,⟨-1872309029590,-518915390284⟩,⟨-219170234032,1176961684206⟩⟩⟩
noncomputable def wholeBoxes52 := wholeStep51.proposed :: wholeBoxes51
theorem wholeAccepted51 : StepValid wholeStep51.shape wholeBoxes51 wholeStep51.proposed := by
  dsimp only [StepValid,wholeStep51]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep52 : Instruction 40 := ⟨.inv 17,⟨⟨1208065635440,1216771539137⟩,⟨-862928032143,-653723024898⟩,⟨571678974128,777205396330⟩,⟨4671607258149,10908425879606⟩,⟨-7623320862188,-891917929506⟩,⟨-3472672644646,3659645269145⟩⟩⟩
noncomputable def wholeBoxes53 := wholeStep52.proposed :: wholeBoxes52
theorem wholeAccepted52 : StepValid wholeStep52.shape wholeBoxes52 wholeStep52.proposed := by
  dsimp only [StepValid,wholeStep52]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep53 : Instruction 40 := ⟨.mul 22 0,⟨⟨1316619643104,1334031450498⟩,⟨-1725856064287,-1307446049796⟩,⟨1143357948255,1554410792660⟩,⟨9343214516299,21816851759211⟩,⟨-15246641724375,-1783835859013⟩,⟨-6941821921208,7319290538290⟩⟩⟩
noncomputable def wholeBoxes54 := wholeStep53.proposed :: wholeBoxes53
theorem wholeAccepted53 : StepValid wholeStep53.shape wholeBoxes53 wholeStep53.proposed := by
  dsimp only [StepValid,wholeStep53]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep54 : Instruction 40 := ⟨.log 0,⟨⟨198133610496,212578936960⟩,⟨-1441265760003,-1077599882598⟩,⟨942358111831,1298091479816⟩,⟨5811452626587,17163170579344⟩,⟨-11808921974679,231327509894⟩,⟨-7329665311433,5304687187683⟩⟩⟩
noncomputable def wholeBoxes55 := wholeStep54.proposed :: wholeBoxes54
theorem wholeAccepted54 : StepValid wholeStep54.shape wholeBoxes54 wholeStep54.proposed := by
  dsimp only [StepValid,wholeStep54]
  exact ⟨by decide,by decide,lc35,by decide⟩
noncomputable def wholeStep55 : Instruction 40 := ⟨.mul 14 26,⟨⟨67702627273,73363492034⟩,⟨-491417496229,-356262881893⟩,⟨310485544873,443402091875⟩,⟨1690917476816,5712981832169⟩,⟨-3974865567719,380567597947⟩,⟨-2773704116152,1847169809149⟩⟩⟩
noncomputable def wholeBoxes56 := wholeStep55.proposed :: wholeBoxes55
theorem wholeAccepted55 : StepValid wholeStep55.shape wholeBoxes55 wholeStep55.proposed := by
  dsimp only [StepValid,wholeStep55]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep56 : Instruction 40 := ⟨.mul 5 4,⟨⟨379730515315,380528897235⟩,⟨-68216391,23084390978⟩,⟨-21426977983,949048438⟩,⟨-572644472439,215790114690⟩,⟨-283714578525,520973497108⟩,⟨-463260923263,366618032399⟩⟩⟩
noncomputable def wholeBoxes57 := wholeStep56.proposed :: wholeBoxes56
theorem wholeAccepted56 : StepValid wholeStep56.shape wholeBoxes56 wholeStep56.proposed := by
  dsimp only [StepValid,wholeStep56]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep57 : Instruction 40 := ⟨.inv 0,⟨⟨3176961929564,3183641479569⟩,⟨-193538369144,571922781⟩,⟨-7956774217,179642702226⟩,⟨-1809242969101,4824553340805⟩,⟨-4389657013781,2379616119015⟩,⟨-3074605035067,3904229530738⟩⟩⟩
noncomputable def wholeBoxes58 := wholeStep57.proposed :: wholeBoxes57
theorem wholeAccepted57 : StepValid wholeStep57.shape wholeBoxes57 wholeStep57.proposed := by
  dsimp only [StepValid,wholeStep57]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep58 : Instruction 40 := ⟨.mul 2 0,⟨⟨195622005210,212424362258⟩,⟨-1435815443423,-1029358513221⟩,⟨896595355697,1295859426842⟩,⟨4764557126694,17036880576674⟩,⟨-11960475921248,1264499068037⟩,⟨-8242840830368,5753883884797⟩⟩⟩
noncomputable def wholeBoxes59 := wholeStep58.proposed :: wholeBoxes58
theorem wholeAccepted58 : StepValid wholeStep58.shape wholeBoxes58 wholeStep58.proposed := by
  dsimp only [StepValid,wholeStep58]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep59 : Instruction 40 := ⟨.add 4 0,⟨⟨393755615706,425003299218⟩,⟨-2877081203426,-2106958395819⟩,⟨1838953467528,2593950906658⟩,⟨10576009753281,34200051156018⟩,⟨-23769397895927,1495826577931⟩,⟨-15572506141801,11058571072480⟩⟩⟩
noncomputable def wholeBoxes60 := wholeStep59.proposed :: wholeBoxes59
theorem wholeAccepted59 : StepValid wholeStep59.shape wholeBoxes59 wholeStep59.proposed := by
  dsimp only [StepValid,wholeStep59]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep60 : Instruction 40 := ⟨.mul 19 19,⟨⟨516298134546,527083142151⟩,⟨-51108554456,212849384516⟩,⟨-201444421664,57550419168⟩,⟨-5215327546827,2780576834527⟩,⟨-3493310671742,5094029793636⟩,⟨-4847482196187,4227357847670⟩⟩⟩
noncomputable def wholeBoxes61 := wholeStep60.proposed :: wholeBoxes60
theorem wholeAccepted60 : StepValid wholeStep60.shape wholeBoxes60 wholeStep60.proposed := by
  dsimp only [StepValid,wholeStep60]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep61 : Instruction 40 := ⟨.mul 20 0,⟨⟨353794372391,364937738255⟩,⟨-53079216857,221056509200⟩,⟨-209211789604,59769469351⟩,⟨-5427139419493,2932425416247⟩,⟨-3670249508993,5302515468846⟩,⟨-5045814756290,4430336895310⟩⟩⟩
noncomputable def wholeBoxes62 := wholeStep61.proposed :: wholeBoxes61
theorem wholeAccepted61 : StepValid wholeStep61.shape wholeBoxes61 wholeStep61.proposed := by
  dsimp only [StepValid,wholeStep61]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep62 : Instruction 40 := ⟨.mul 65 0,⟨⟨707588744782,729875476510⟩,⟨-106158433714,442113018400⟩,⟨-418423579208,119538938702⟩,⟨-10854278838986,5864850832494⟩,⟨-7340499017986,10605030937692⟩,⟨-10091629512580,8860673790620⟩⟩⟩
noncomputable def wholeBoxes63 := wholeStep62.proposed :: wholeBoxes62
theorem wholeAccepted62 : StepValid wholeStep62.shape wholeBoxes62 wholeStep62.proposed := by
  dsimp only [StepValid,wholeStep62]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep63 : Instruction 40 := ⟨.add 11 20,⟨⟨1522949412129,1525627909242⟩,⟨-39762486546,37697204420⟩,⟨-36519324964,38358717020⟩,⟨-1285827892579,1343572450977⟩,⟨-1365177649208,1320755384380⟩,⟨-1371466350815,1400729336961⟩⟩⟩
noncomputable def wholeBoxes64 := wholeStep63.proposed :: wholeBoxes63
theorem wholeAccepted63 : StepValid wholeStep63.shape wholeBoxes63 wholeStep63.proposed := by
  dsimp only [StepValid,wholeStep63]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep64 : Instruction 40 := ⟨.mul 1 0,⟨⟨980091374817,1012739082612⟩,⟨-173695237292,638478218162⟩,⟨-604826027516,191329516374⟩,⟨-15946392525758,9059980171643⟩,⟨-11120572639838,15622312814730⟩,⟨-14942244591822,13252256681208⟩⟩⟩
noncomputable def wholeBoxes65 := wholeStep64.proposed :: wholeBoxes64
theorem wholeAccepted64 : StepValid wholeStep64.shape wholeBoxes64 wholeStep64.proposed := by
  dsimp only [StepValid,wholeStep64]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep65 : Instruction 40 := ⟨.mul 14 14,⟨⟨67448991835,67614218863⟩,⟨12051900086,16838979482⟩,⟨-15166207650,-10539353236⟩,⟨-299881264282,-137040669136⟩,⟨60914165140,227160470662⟩,⟨-142050579059,29446035830⟩⟩⟩
noncomputable def wholeBoxes66 := wholeStep65.proposed :: wholeBoxes65
theorem wholeAccepted65 : StepValid wholeStep65.shape wholeBoxes65 wholeStep65.proposed := by
  dsimp only [StepValid,wholeStep65]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep66 : Instruction 40 := ⟨.mul 41 0,⟨⟨60005312720,61043161690⟩,⟨210852729659,221529577820⟩,⟨19895747511,25793848749⟩,⟨-1088247423105,-864678591082⟩,⟨-217792056331,-32892147661⟩,⟨-202264888686,-38011370288⟩⟩⟩
noncomputable def wholeBoxes67 := wholeStep66.proposed :: wholeBoxes66
theorem wholeAccepted66 : StepValid wholeStep66.shape wholeBoxes66 wholeStep66.proposed := by
  dsimp only [StepValid,wholeStep66]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep67 : Instruction 40 := ⟨.mul 15 15,⟨⟨2137841653938,2141594535389⟩,⟨-382628713174,-273612827682⟩,⟨239273659766,344618658326⟩,⟨3200745977785,6920492793873⟩,⟨-5256867938274,-1462464624488⟩,⟨-598368761953,3312921559435⟩⟩⟩
noncomputable def wholeBoxes68 := wholeStep67.proposed :: wholeBoxes67
theorem wholeAccepted67 : StepValid wholeStep67.shape wholeBoxes67 wholeStep67.proposed := by
  dsimp only [StepValid,wholeStep67]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep68 : Instruction 40 := ⟨.mul 16 0,⟨⟨2981009696621,2988862676006⟩,⟨-801009243820,-572289222827⟩,⟨500465339840,721437574881⟩,⟨6731310059399,14559174470062⟩,⟨-11069371691894,-3090920553479⟩,⟨-1224648920770,6993439501905⟩⟩⟩
noncomputable def wholeBoxes69 := wholeStep68.proposed :: wholeBoxes68
theorem wholeAccepted68 : StepValid wholeStep68.shape wholeBoxes68 wholeStep68.proposed := by
  dsimp only [StepValid,wholeStep68]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep69 : Instruction 40 := ⟨.mul 2 0,⟨⟨162687155413,165936969644⟩,⟨527195784240,570963577954⟩,⟨81254252540,110169914778⟩,⟨-2913659245021,-1755520054576⟩,⟨-1129407448909,-122863481025⟩,⟨-599706394920,319056833407⟩⟩⟩
noncomputable def wholeBoxes70 := wholeStep69.proposed :: wholeBoxes69
theorem wholeAccepted69 : StepValid wholeStep69.shape wholeBoxes69 wholeStep69.proposed := by
  dsimp only [StepValid,wholeStep69]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep70 : Instruction 40 := ⟨.inv 0,⟨⟨7285451953282,7430985049469⟩,⟨-26079636101552,-23146496915625⟩,⟨-5032179630521,-3567462718826⟩,⟨224152750759019,316142985222111⟩,⟨28062574659569,86909088828844⟩,⟨-11079655146166,34207979374143⟩⟩⟩
noncomputable def wholeBoxes71 := wholeStep70.proposed :: wholeBoxes70
theorem wholeAccepted70 : StepValid wholeStep70.shape wholeBoxes70 wholeStep70.proposed := by
  dsimp only [StepValid,wholeStep70]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep71 : Instruction 40 := ⟨.mul 6 0,⟨⟨6494163809343,6844537876444⟩,⟨-25195361969802,-16317389864214⟩,⟨-8722725534021,-1886903796734⟩,⟨61745789964044,360664445174118⟩,⟨-57603449836876,200773785939364⟩,⟨-112942875553704,126609179779292⟩⟩⟩
noncomputable def wholeBoxes72 := wholeStep71.proposed :: wholeBoxes71
theorem wholeAccepted71 : StepValid wholeStep71.shape wholeBoxes71 wholeStep71.proposed := by
  dsimp only [StepValid,wholeStep71]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep72 : Instruction 40 := ⟨.mul 75 0,⟨⟨12988327618686,13689075752888⟩,⟨-50390723939604,-32634779728428⟩,⟨-17445451068042,-3773807593468⟩,⟨123491579928088,721328890348236⟩,⟨-115206899673752,401547571878728⟩,⟨-225885751107408,253218359558584⟩⟩⟩
noncomputable def wholeBoxes73 := wholeStep72.proposed :: wholeBoxes72
theorem wholeAccepted72 : StepValid wholeStep72.shape wholeBoxes72 wholeStep72.proposed := by
  dsimp only [StepValid,wholeStep72]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep73 : Instruction 40 := ⟨.inv 73,⟨⟨8019230105695,8042142191734⟩,⟨-58822525745262,-58487832109754⟩,⟨0,0⟩,⟨853155841598660,860489519473652⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes74 := wholeStep73.proposed :: wholeBoxes73
theorem wholeAccepted73 : StepValid wholeStep73.shape wholeBoxes73 wholeStep73.proposed := by
  dsimp only [StepValid,wholeStep73]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep74 : Instruction 40 := ⟨.mul 63 0,⟨⟨6919718477919,6942630563958⟩,⟨-58822525745261,-58487832109754⟩,⟨0,0⟩,⟨853155841598666,860489519473638⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes75 := wholeStep74.proposed :: wholeBoxes74
theorem wholeAccepted74 : StepValid wholeStep74.shape wholeBoxes74 wholeStep74.proposed := by
  dsimp only [StepValid,wholeStep74]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep75 : Instruction 40 := ⟨.log 0,⟨⟨2022561510464,2026196160768⟩,⟨-9346630392381,-9262778840857⟩,⟨0,0⟩,⟨55662176413623,58694049043016⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes76 := wholeStep75.proposed :: wholeBoxes75
theorem wholeAccepted75 : StepValid wholeStep75.shape wholeBoxes75 wholeStep75.proposed := by
  dsimp only [StepValid,wholeStep75]
  exact ⟨by decide,by decide,lc36,by decide⟩
noncomputable def wholeStep76 : Instruction 40 := ⟨.inv 70,⟨⟨5525719612721,5610555144123⟩,⟨-23954733582392,-23040527016729⟩,⟨-10400514580581,-10077518643375⟩,⟨192143620167233,204553469759373⟩,⟨111810344773122,117441104036844⟩,⟨36757703656836,38559714952337⟩⟩⟩
noncomputable def wholeBoxes77 := wholeStep76.proposed :: wholeBoxes76
theorem wholeAccepted76 : StepValid wholeStep76.shape wholeBoxes76 wholeStep76.proposed := by
  dsimp only [StepValid,wholeStep76]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep77 : Instruction 40 := ⟨.mul 57 0,⟨⟨4426207984945,4511043516347⟩,⟨-23954733582392,-23040527016728⟩,⟨-10400514580581,-10077518643375⟩,⟨192143620167233,204553469759374⟩,⟨111810344773121,117441104036846⟩,⟨36757703656835,38559714952338⟩⟩⟩
noncomputable def wholeBoxes78 := wholeStep77.proposed :: wholeBoxes77
theorem wholeAccepted77 : StepValid wholeStep77.shape wholeBoxes77 wholeStep77.proposed := by
  dsimp only [StepValid,wholeStep77]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep78 : Instruction 40 := ⟨.log 0,⟨⟨1531264691072,1552139257984⟩,⟨-5950580768847,-5615846371937⟩,⟨-2583585487873,-2456271788854⟩,⟨14627982834567,22129603976823⟩,⟨13269981951755,16627862217561⟩,⟨2888441343269,4091367188811⟩⟩⟩
noncomputable def wholeBoxes79 := wholeStep78.proposed :: wholeBoxes78
theorem wholeAccepted78 : StepValid wholeStep78.shape wholeBoxes78 wholeStep78.proposed := by
  dsimp only [StepValid,wholeStep78]
  exact ⟨by decide,by decide,lc37,by decide⟩
noncomputable def wholeStep79 : Instruction 40 := ⟨.mul 79 68,⟨⟨129713045503,130142542234⟩,⟨798004923596,798863917056⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes80 := wholeStep79.proposed :: wholeBoxes79
theorem wholeAccepted79 : StepValid wholeStep79.shape wholeBoxes79 wholeStep79.proposed := by
  dsimp only [StepValid,wholeStep79]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep80 : Instruction 40 := ⟨.mul 74 60,⟨⟨172598410196,175906541649⟩,⟨547672015501,560915647565⟩,⟨240129411644,242961180395⟩,⟨-1539532369432,-1513766592182⟩,⟨-1336989093726,-1324043122766⟩,⟨-290212282368,-289588505476⟩⟩⟩
noncomputable def wholeBoxes81 := wholeStep80.proposed :: wholeBoxes80
theorem wholeAccepted80 : StepValid wholeStep80.shape wholeBoxes80 wholeStep80.proposed := by
  dsimp only [StepValid,wholeStep80]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep81 : Instruction 40 := ⟨.add 5 2,⟨⟨3553826201536,3578335418752⟩,⟨-15297211161228,-14878625212794⟩,⟨-2583585487873,-2456271788854⟩,⟨70290159248190,80823653019839⟩,⟨13269981951755,16627862217561⟩,⟨2888441343269,4091367188811⟩⟩⟩
noncomputable def wholeBoxes82 := wholeStep81.proposed :: wholeBoxes81
theorem wholeAccepted81 : StepValid wholeStep81.shape wholeBoxes81 wholeStep81.proposed := by
  dsimp only [StepValid,wholeStep81]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep82 : Instruction 40 := ⟨.mul 85 22,⟨⟨787511231412,850006598436⟩,⟨-5754162406852,-4213916791638⟩,⟨3677906935056,5187901813316⟩,⟨21152019506562,68400102312036⟩,⟨-47538795791854,2991653155862⟩,⟨-31145012283602,22117142144960⟩⟩⟩
noncomputable def wholeBoxes83 := wholeStep82.proposed :: wholeBoxes82
theorem wholeAccepted82 : StepValid wholeStep82.shape wholeBoxes82 wholeStep82.proposed := by
  dsimp only [StepValid,wholeStep82]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep83 : Instruction 40 := ⟨.add 1 0,⟨⟨4341337432948,4428342017188⟩,⟨-21051373568080,-19092542004432⟩,⟨1094321447183,2731630024462⟩,⟨91442178754752,149223755331875⟩,⟨-34268813840099,19619515373423⟩,⟨-28256570940333,26208509333771⟩⟩⟩
noncomputable def wholeBoxes84 := wholeStep83.proposed :: wholeBoxes83
theorem wholeAccepted83 : StepValid wholeStep83.shape wholeBoxes83 wholeStep83.proposed := by
  dsimp only [StepValid,wholeStep83]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep84 : Instruction 40 := ⟨.mul 4 0,⟨⟨512162023354,524156064784⟩,⟨659137524795,965056533575⟩,⟨129100742627,323326526838⟩,⟨-28659223136527,-18733979360746⟩,⟨-3261954270462,4306943328072⟩,⟨-3344559424468,3102142757472⟩⟩⟩
noncomputable def wholeBoxes85 := wholeStep84.proposed :: wholeBoxes84
theorem wholeAccepted84 : StepValid wholeStep84.shape wholeBoxes84 wholeStep84.proposed := by
  dsimp only [StepValid,wholeStep84]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep85 : Instruction 40 := ⟨.mul 88 85,⟨⟨300647710720,301506704180⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes86 := wholeStep85.proposed :: wholeBoxes85
theorem wholeAccepted85 : StepValid wholeStep85.shape wholeBoxes85 wholeStep85.proposed := by
  dsimp only [StepValid,wholeStep85]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep86 : Instruction 40 := ⟨.neg 0,⟨⟨-301506704180,-300647710720⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes87 := wholeStep86.proposed :: wholeBoxes86
theorem wholeAccepted86 : StepValid wholeStep86.shape wholeBoxes86 wholeStep86.proposed := by
  dsimp only [StepValid,wholeStep86]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep87 : Instruction 40 := ⟨.add 89 0,⟨⟨798004923596,798863917056⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes88 := wholeStep87.proposed :: wholeBoxes87
theorem wholeAccepted87 : StepValid wholeStep87.shape wholeBoxes87 wholeStep87.proposed := by
  dsimp only [StepValid,wholeStep87]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep88 : Instruction 40 := ⟨.mul 12 0,⟨⟨1467937221264,1472158148058⟩,⟨-10843303466001,-10767874226512⟩,⟨0,0⟩,⟨77449679338587,80031416577341⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes89 := wholeStep88.proposed :: wholeBoxes88
theorem wholeAccepted88 : StepValid wholeStep88.shape wholeBoxes88 wholeStep88.proposed := by
  dsimp only [StepValid,wholeStep88]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep89 : Instruction 40 := ⟨.neg 91,⟨⟨-1099511627776,-1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes90 := wholeStep89.proposed :: wholeBoxes89
theorem wholeAccepted89 : StepValid wholeStep89.shape wholeBoxes89 wholeStep89.proposed := by
  dsimp only [StepValid,wholeStep89]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep90 : Instruction 40 := ⟨.add 1 0,⟨⟨368425593488,372646520282⟩,⟨-10843303466001,-10767874226512⟩,⟨0,0⟩,⟨77449679338587,80031416577341⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes91 := wholeStep90.proposed :: wholeBoxes90
theorem wholeAccepted90 : StepValid wholeStep90.shape wholeBoxes90 wholeStep90.proposed := by
  dsimp only [StepValid,wholeStep90]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep91 : Instruction 40 := ⟨.mul 84 0,⟨⟨21686491972,23201703818⟩,⟨-738591718504,-693982171079⟩,⟨133698193886,135375493697⟩,⟨8075274185957,8676413332182⟩,⟨-4311815357541,-4275986201464⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes92 := wholeStep91.proposed :: wholeBoxes91
theorem wholeAccepted91 : StepValid wholeStep91.shape wholeBoxes91 wholeStep91.proposed := by
  dsimp only [StepValid,wholeStep91]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep92 : Instruction 40 := ⟨.add 7 0,⟨⟨533848515326,547357768602⟩,⟨-79454193709,271074362496⟩,⟨262798936513,458702020535⟩,⟨-20583948950570,-10057566028564⟩,⟨-7573769628003,30957126608⟩,⟨-3344559424468,3102142757472⟩⟩⟩
noncomputable def wholeBoxes93 := wholeStep92.proposed :: wholeBoxes92
theorem wholeAccepted92 : StepValid wholeStep92.shape wholeBoxes92 wholeStep92.proposed := by
  dsimp only [StepValid,wholeStep92]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep93 : Instruction 40 := ⟨.inv 17,⟨⟨596647966777,597720174818⟩,⟨2727582979922,2762175351996⟩,⟨0,0⟩,⟨7592716611177,9138369381562⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes94 := wholeStep93.proposed :: wholeBoxes93
theorem wholeAccepted93 : StepValid wholeStep93.shape wholeBoxes93 wholeStep93.proposed := by
  dsimp only [StepValid,wholeStep93]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep94 : Instruction 40 := ⟨.mul 1 0,⟨⟨289691917019,297556454041⟩,⟨1281136746643,1522425693562⟩,⟨142607360559,249361120863⟩,⟨-7902612111106,453511344836⟩,⟨-3465346707987,1169172823358⟩,⟨-1818180538869,1686397182591⟩⟩⟩
noncomputable def wholeBoxes95 := wholeStep94.proposed :: wholeBoxes94
theorem wholeAccepted94 : StepValid wholeStep94.shape wholeBoxes94 wholeStep94.proposed := by
  dsimp only [StepValid,wholeStep94]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep95 : Instruction 40 := ⟨.neg 12,⟨⟨-850006598436,-787511231412⟩,⟨4213916791638,5754162406852⟩,⟨-5187901813316,-3677906935056⟩,⟨-68400102312036,-21152019506562⟩,⟨-2991653155862,47538795791854⟩,⟨-22117142144960,31145012283602⟩⟩⟩
noncomputable def wholeBoxes96 := wholeStep95.proposed :: wholeBoxes95
theorem wholeAccepted95 : StepValid wholeStep95.shape wholeBoxes95 wholeStep95.proposed := by
  dsimp only [StepValid,wholeStep95]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep96 : Instruction 40 := ⟨.add 14 0,⟨⟨2703819603100,2790824187340⟩,⟨-11083294369590,-9124462805942⟩,⟨-7771487301189,-6134178723910⟩,⟨1890056936154,59671633513277⟩,⟨10278328795893,64166658009415⟩,⟨-19228700801691,35236379472413⟩⟩⟩
noncomputable def wholeBoxes97 := wholeStep96.proposed :: wholeBoxes96
theorem wholeAccepted96 : StepValid wholeStep96.shape wholeBoxes96 wholeStep96.proposed := by
  dsimp only [StepValid,wholeStep96]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep97 : Instruction 40 := ⟨.mul 16 0,⟨⟨424438408073,446492987199⟩,⟨-426387169730,-8595468822⟩,⟨-652825150735,-346233315916⟩,⟨-14919287267175,-3265765345695⟩,⟨-8193853687890,1961590204339⟩,⟨-7247513323609,2245834475165⟩⟩⟩
noncomputable def wholeBoxes98 := wholeStep97.proposed :: wholeBoxes97
theorem wholeAccepted97 : StepValid wholeStep97.shape wholeBoxes97 wholeStep97.proposed := by
  dsimp only [StepValid,wholeStep97]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep98 : Instruction 40 := ⟨.mul 101 92,⟨⟨430946952150,437563215054⟩,⟨1824502107340,1839963989608⟩,⟨798004923596,798863917056⟩,⟨0,0⟩,⟨-2199023255552,-2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes99 := wholeStep98.proposed :: wholeBoxes98
theorem wholeAccepted98 : StepValid wholeStep98.shape wholeBoxes98 wholeStep98.proposed := by
  dsimp only [StepValid,wholeStep98]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep99 : Instruction 40 := ⟨.neg 0,⟨⟨-437563215054,-430946952150⟩,⟨-1839963989608,-1824502107340⟩,⟨-798863917056,-798004923596⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes100 := wholeStep99.proposed :: wholeBoxes99
theorem wholeAccepted99 : StepValid wholeStep99.shape wholeBoxes99 wholeStep99.proposed := by
  dsimp only [StepValid,wholeStep99]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep100 : Instruction 40 := ⟨.add 102 0,⟨⟨661948412722,668564675626⟩,⟨-1839963989608,-1824502107340⟩,⟨-798863917056,-798004923596⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes101 := wholeStep100.proposed :: wholeBoxes100
theorem wholeAccepted100 : StepValid wholeStep100.shape wholeBoxes100 wholeStep100.proposed := by
  dsimp only [StepValid,wholeStep100]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep101 : Instruction 40 := ⟨.mul 22 0,⟨⟨921880411362,943787635643⟩,⟨-6215694559668,-5921898489532⟩,⟨-2698690915260,-2590133567217⟩,⟨27444200076260,33371889156445⟩,⟨19203322395527,21861888087661⟩,⟨5304385126517,6242053153290⟩⟩⟩
noncomputable def wholeBoxes102 := wholeStep101.proposed :: wholeBoxes101
theorem wholeAccepted101 : StepValid wholeStep101.shape wholeBoxes101 wholeStep101.proposed := by
  dsimp only [StepValid,wholeStep101]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep102 : Instruction 40 := ⟨.neg 0,⟨⟨-943787635643,-921880411362⟩,⟨5921898489532,6215694559668⟩,⟨2590133567217,2698690915260⟩,⟨-33371889156445,-27444200076260⟩,⟨-21861888087661,-19203322395527⟩,⟨-6242053153290,-5304385126517⟩⟩⟩
noncomputable def wholeBoxes103 := wholeStep102.proposed :: wholeBoxes102
theorem wholeAccepted102 : StepValid wholeStep102.shape wholeBoxes102 wholeStep102.proposed := by
  dsimp only [StepValid,wholeStep102]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep103 : Instruction 40 := ⟨.add 105 0,⟨⟨155723992133,177631216414⟩,⟨5921898489532,6215694559668⟩,⟨2590133567217,2698690915260⟩,⟨-33371889156445,-27444200076260⟩,⟨-21861888087661,-19203322395527⟩,⟨-6242053153290,-5304385126517⟩⟩⟩
noncomputable def wholeBoxes104 := wholeStep103.proposed :: wholeBoxes103
theorem wholeAccepted103 : StepValid wholeStep103.shape wholeBoxes103 wholeStep103.proposed := by
  dsimp only [StepValid,wholeStep103]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep104 : Instruction 40 := ⟨.mul 97 0,⟨⟨9166320595,11059668205⟩,⟨318325583888,361574535927⟩,⟨208972798490,232555883959⟩,⟨-4195020283659,-3549307217554⟩,⟨150585366284,549043376372⟩,⟨1491227896284,1648537665857⟩⟩⟩
noncomputable def wholeBoxes105 := wholeStep104.proposed :: wholeBoxes104
theorem wholeAccepted104 : StepValid wholeStep104.shape wholeBoxes104 wholeStep104.proposed := by
  dsimp only [StepValid,wholeStep104]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep105 : Instruction 40 := ⟨.add 7 0,⟨⟨433604728668,457552655404⟩,⟨-108061585842,352979067105⟩,⟨-443852352245,-113677431957⟩,⟨-19114307550834,-6815072563249⟩,⟨-8043268321606,2510633580711⟩,⟨-5756285427325,3894372141022⟩⟩⟩
noncomputable def wholeBoxes106 := wholeStep105.proposed :: wholeBoxes105
theorem wholeAccepted105 : StepValid wholeStep105.shape wholeBoxes105 wholeStep105.proposed := by
  dsimp only [StepValid,wholeStep105]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep106 : Instruction 40 := ⟨.neg 26,⟨⟨-130142542234,-129713045503⟩,⟨-798863917056,-798004923596⟩,⟨0,0⟩,⟨2199023255552,2199023255552⟩,⟨0,0⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes107 := wholeStep106.proposed :: wholeBoxes106
theorem wholeAccepted106 : StepValid wholeStep106.shape wholeBoxes106 wholeStep106.proposed := by
  dsimp only [StepValid,wholeStep106]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep107 : Instruction 40 := ⟨.mul 100 27,⟨⟨7635248391,8102930136⟩,⟨24807750760,28559127349⟩,⟨47071648153,47278345421⟩,⟨-409028526082,-390038730830⟩,⟨159445963242,160499236865⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes108 := wholeStep107.proposed :: wholeBoxes107
theorem wholeAccepted107 : StepValid wholeStep107.shape wholeBoxes107 wholeStep107.proposed := by
  dsimp only [StepValid,wholeStep107]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep108 : Instruction 40 := ⟨.mul 0 32,⟨⟨14045107962,14932198549⟩,⟨-23246585651,-11693576244⟩,⟨86588719376,87125228656⟩,⟨-852779250283,-702912951446⟩,⟨-108597261681,-100782316597⟩,⟨0,0⟩⟩⟩
noncomputable def wholeBoxes109 := wholeStep108.proposed :: wholeBoxes108
theorem wholeAccepted108 : StepValid wholeStep108.shape wholeBoxes108 wholeStep108.proposed := by
  dsimp only [StepValid,wholeStep108]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep109 : Instruction 40 := ⟨.inv 84,⟨⟨1217869746347,1235906412993⟩,⟨-4239255149692,-4002584390531⟩,⟨-722614442111,-671755113674⟩,⟨43219835273357,47348202117536⟩,⟨8724737452711,9717926457339⟩,⟨1823027166997,2041654151333⟩⟩⟩
noncomputable def wholeBoxes110 := wholeStep109.proposed :: wholeBoxes109
theorem wholeAccepted109 : StepValid wholeStep109.shape wholeBoxes109 wholeStep109.proposed := by
  dsimp only [StepValid,wholeStep109]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep110 : Instruction 40 := ⟨.mul 1 0,⟨⟨15557008801,16784542774⟩,⟨-83702619925,-64081161895⟩,⟨86096005705,89352175323⟩,⟨-321341795181,43703724209⟩,⟨-339393434200,-279587825436⟩,⟨-91232580981,-78076886800⟩⟩⟩
noncomputable def wholeBoxes111 := wholeStep110.proposed :: wholeBoxes110
theorem wholeAccepted110 : StepValid wholeStep110.shape wholeBoxes110 wholeStep110.proposed := by
  dsimp only [StepValid,wholeStep110]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep111 : Instruction 40 := ⟨.neg 0,⟨⟨-16784542774,-15557008801⟩,⟨64081161895,83702619925⟩,⟨-89352175323,-86096005705⟩,⟨-43703724209,321341795181⟩,⟨279587825436,339393434200⟩,⟨78076886800,91232580981⟩⟩⟩
noncomputable def wholeBoxes112 := wholeStep111.proposed :: wholeBoxes111
theorem wholeAccepted111 : StepValid wholeStep111.shape wholeBoxes111 wholeStep111.proposed := by
  dsimp only [StepValid,wholeStep111]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep112 : Instruction 40 := ⟨.add 5 0,⟨⟨-146927085008,-145270054304⟩,⟨-734782755161,-714302303671⟩,⟨-89352175323,-86096005705⟩,⟨2155319531343,2520365050733⟩,⟨279587825436,339393434200⟩,⟨78076886800,91232580981⟩⟩⟩
noncomputable def wholeBoxes113 := wholeStep112.proposed :: wholeBoxes112
theorem wholeAccepted112 : StepValid wholeStep112.shape wholeBoxes112 wholeStep112.proposed := by
  dsimp only [StepValid,wholeStep112]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep113 : Instruction 40 := ⟨.mul 106 34,⟨⟨90134236106,96639236883⟩,⟨-634843556387,-580590186875⟩,⟨394822497009,419280521792⟩,⟨2694966077492,3404749155995⟩,⟨-2531704779388,-2093902447131⟩,⟨-1707115135134,-1527979457168⟩⟩⟩
noncomputable def wholeBoxes114 := wholeStep113.proposed :: wholeBoxes113
theorem wholeAccepted113 : StepValid wholeStep113.shape wholeBoxes113 wholeStep113.proposed := by
  dsimp only [StepValid,wholeStep113]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep114 : Instruction 40 := ⟨.mul 0 4,⟨⟨99836833454,108627366545⟩,⟨-1086196430338,-971206745917⟩,⟨373810931739,416224203678⟩,⟨10755163137910,12884059349994⟩,⟨-3392392783387,-2485222181776⟩,⟨-2320551814427,-1995453310408⟩⟩⟩
noncomputable def wholeBoxes115 := wholeStep114.proposed :: wholeBoxes114
theorem wholeAccepted114 : StepValid wholeStep114.shape wholeBoxes114 wholeStep114.proposed := by
  dsimp only [StepValid,wholeStep114]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep115 : Instruction 40 := ⟨.neg 0,⟨⟨-108627366545,-99836833454⟩,⟨971206745917,1086196430338⟩,⟨-416224203678,-373810931739⟩,⟨-12884059349994,-10755163137910⟩,⟨2485222181776,3392392783387⟩,⟨1995453310408,2320551814427⟩⟩⟩
noncomputable def wholeBoxes116 := wholeStep115.proposed :: wholeBoxes115
theorem wholeAccepted115 : StepValid wholeStep115.shape wholeBoxes115 wholeStep115.proposed := by
  dsimp only [StepValid,wholeStep115]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep116 : Instruction 40 := ⟨.add 118 0,⟨⟨990884261231,999674794322⟩,⟨971206745917,1086196430338⟩,⟨-416224203678,-373810931739⟩,⟨-12884059349994,-10755163137910⟩,⟨2485222181776,3392392783387⟩,⟨1995453310408,2320551814427⟩⟩⟩
noncomputable def wholeBoxes117 := wholeStep116.proposed :: wholeBoxes116
theorem wholeAccepted116 : StepValid wholeStep116.shape wholeBoxes116 wholeStep116.proposed := by
  dsimp only [StepValid,wholeStep116]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep117 : Instruction 40 := ⟨.mul 36 0,⟨⟨155546375187,159934039260⟩,⟨646021654386,683760201560⟩,⟨149815509245,162220199408⟩,⟨-2493485695062,-1944283578413⟩,⟨-825694100042,-596675480340⟩,⟨-134567455788,-53000299999⟩⟩⟩
noncomputable def wholeBoxes118 := wholeStep117.proposed :: wholeBoxes117
theorem wholeAccepted117 : StepValid wholeStep117.shape wholeBoxes117 wholeStep117.proposed := by
  dsimp only [StepValid,wholeStep117]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep118 : Instruction 40 := ⟨.mul 5 5,⟨⟨19193420191,19633779002⟩,⟨188750590392,196377165286⟩,⟨22750412288,23880156114⟩,⟨254509161039,412551002086⟩,⟨21159371050,45545128124⟩,⟨-10899411762,-6108934667⟩⟩⟩
noncomputable def wholeBoxes119 := wholeStep118.proposed :: wholeBoxes118
theorem wholeAccepted118 : StepValid wholeStep118.shape wholeBoxes118 wholeStep118.proposed := by
  dsimp only [StepValid,wholeStep118]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep119 : Instruction 40 := ⟨.mul 46 0,⟨⟨226728324890,244443334008⟩,⟨1329857849350,1875240606360⟩,⟨-42773829231,231434561261⟩,⟨-12837791381386,6812284535258⟩,⟨-6017533948173,6414305870822⟩,⟨-4927091122396,4293339869649⟩⟩⟩
noncomputable def wholeBoxes120 := wholeStep119.proposed :: wholeBoxes119
theorem wholeAccepted119 : StepValid wholeStep119.shape wholeBoxes119 wholeStep119.proposed := by
  dsimp only [StepValid,wholeStep119]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep120 : Instruction 40 := ⟨.neg 0,⟨⟨-244443334008,-226728324890⟩,⟨-1875240606360,-1329857849350⟩,⟨-231434561261,42773829231⟩,⟨-6812284535258,12837791381386⟩,⟨-6414305870822,6017533948173⟩,⟨-4293339869649,4927091122396⟩⟩⟩
noncomputable def wholeBoxes121 := wholeStep120.proposed :: wholeBoxes120
theorem wholeAccepted120 : StepValid wholeStep120.shape wholeBoxes120 wholeStep120.proposed := by
  dsimp only [StepValid,wholeStep120]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep121 : Instruction 40 := ⟨.add 26 0,⟨⟨45248583011,70828129151⟩,⟨-594103859717,192567844212⟩,⟨-88827200702,292134950094⟩,⟨-14714896646364,13291302726222⟩,⟨-9879652578809,7186706771531⟩,⟨-6111520408518,6613488304987⟩⟩⟩
noncomputable def wholeBoxes122 := wholeStep121.proposed :: wholeBoxes121
theorem wholeAccepted121 : StepValid wholeStep121.shape wholeBoxes121 wholeStep121.proposed := by
  dsimp only [StepValid,wholeStep121]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep122 : Instruction 40 := ⟨.mul 49 43,⟨⟨18088546747612,19324353962997⟩,⟨-145220266661744,-111788666285047⟩,⟨-56793093729997,-34271180113999⟩,⟨678151216669137,1839220985361179⟩,⟨86302619614574,986689996797424⟩,⟨-267892687936619,490382099552594⟩⟩⟩
noncomputable def wholeBoxes123 := wholeStep122.proposed :: wholeBoxes122
theorem wholeAccepted122 : StepValid wholeStep122.shape wholeBoxes122 wholeStep122.proposed := by
  dsimp only [StepValid,wholeStep122]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep123 : Instruction 40 := ⟨.mul 5 5,⟨⟨22004928572,23263871221⟩,⟨182783563344,198918370954⟩,⟨42388381934,47192828318⟩,⟨33743597462,300318334266⟩,⟨-64160357358,32940093872⟩,⟨1678508947,32871664276⟩⟩⟩
noncomputable def wholeBoxes124 := wholeStep123.proposed :: wholeBoxes123
theorem wholeAccepted123 : StepValid wholeStep123.shape wholeBoxes123 wholeStep123.proposed := by
  dsimp only [StepValid,wholeStep123]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep124 : Instruction 40 := ⟨.mul 1 0,⟨⟨362012705547,408871785134⟩,⟨-65571432111,1258801961100⟩,⟨-504299342182,143551049811⟩,⟨-38417889321661,7025479511167⟩,⟨-15908262207500,11448742907742⟩,⟨-10515862095189,8310971629632⟩⟩⟩
noncomputable def wholeBoxes125 := wholeStep124.proposed :: wholeBoxes124
theorem wholeAccepted124 : StepValid wholeStep124.shape wholeBoxes124 wholeStep124.proposed := by
  dsimp only [StepValid,wholeStep124]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep125 : Instruction 40 := ⟨.neg 0,⟨⟨-408871785134,-362012705547⟩,⟨-1258801961100,65571432111⟩,⟨-143551049811,504299342182⟩,⟨-7025479511167,38417889321661⟩,⟨-11448742907742,15908262207500⟩,⟨-8310971629632,10515862095189⟩⟩⟩
noncomputable def wholeBoxes126 := wholeStep125.proposed :: wholeBoxes125
theorem wholeAccepted125 : StepValid wholeStep125.shape wholeBoxes125 wholeStep125.proposed := by
  dsimp only [StepValid,wholeStep125]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep126 : Instruction 40 := ⟨.add 20 0,⟨⟨24732943534,95539949857⟩,⟨-1366863546942,418550499216⟩,⟨-587403402056,390621910225⟩,⟨-26139787062001,31602816758412⟩,⟨-19492011229348,18418895788211⟩,⟨-14067257056957,14410234236211⟩⟩⟩
noncomputable def wholeBoxes127 := wholeStep126.proposed :: wholeBoxes126
theorem wholeAccepted126 : StepValid wholeStep126.shape wholeBoxes126 wholeStep126.proposed := by
  dsimp only [StepValid,wholeStep126]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep127 : Instruction 40 := ⟨.add 47 46,⟨⟨302311455699,306049083883⟩,⟨1345676939097,1359779564621⟩,⟨240129411644,242961180395⟩,⟨-3738555624984,-3712789847734⟩,⟨-1336989093726,-1324043122766⟩,⟨-290212282368,-289588505476⟩⟩⟩
noncomputable def wholeBoxes128 := wholeStep127.proposed :: wholeBoxes127
theorem wholeAccepted127 : StepValid wholeStep127.shape wholeBoxes127 wholeStep127.proposed := by
  dsimp only [StepValid,wholeStep127]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep128 : Instruction 40 := ⟨.mul 55 15,⟨⟨-1829263052810,-1716048298917⟩,⟨-4836365927956,-1704238601607⟩,⟨-613842951358,1314189051592⟩,⟨-28527718600584,82413234416869⟩,⟨-45348744892107,35374008597118⟩,⟨-32324103572185,34156257854262⟩⟩⟩
noncomputable def wholeBoxes129 := wholeStep128.proposed :: wholeBoxes128
theorem wholeAccepted128 : StepValid wholeStep128.shape wholeBoxes128 wholeStep128.proposed := by
  dsimp only [StepValid,wholeStep128]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep129 : Instruction 40 := ⟨.mul 0 11,⟨⟨-266083069533,-242766957437⟩,⟨-1841069035340,-1249366048801⟩,⟨-359175646627,-42661746573⟩,⟨-7130345532234,14133522783325⟩,⟨-6760421118374,7104234634168⟩,⟨-4800248304539,5580007909558⟩⟩⟩
noncomputable def wholeBoxes130 := wholeStep129.proposed :: wholeBoxes129
theorem wholeAccepted129 : StepValid wholeStep129.shape wholeBoxes129 wholeStep129.proposed := by
  dsimp only [StepValid,wholeStep129]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep130 : Instruction 40 := ⟨.add 2 0,⟨⟨36228386166,63282126446⟩,⟨-495392096243,110413515820⟩,⟨-119046234983,200299433822⟩,⟨-10868901157218,10420732935591⟩,⟨-8097410212100,5780191511402⟩,⟨-5090460586907,5290419404082⟩⟩⟩
noncomputable def wholeBoxes131 := wholeStep130.proposed :: wholeBoxes130
theorem wholeAccepted130 : StepValid wholeStep130.shape wholeBoxes130 wholeStep130.proposed := by
  dsimp only [StepValid,wholeStep130]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep131 : Instruction 40 := ⟨.mul 9 4,⟨⟨1017843395,6154474166⟩,⟨-139673866945,43694918528⟩,⟨-45557708588,50547512357⟩,⟨-3441273870418,4667832946132⟩,⟨-2688341555202,2239581037311⟩,⟨-1749371204006,1710514786389⟩⟩⟩
noncomputable def wholeBoxes132 := wholeStep131.proposed :: wholeBoxes131
theorem wholeAccepted131 : StepValid wholeStep131.shape wholeBoxes131 wholeStep131.proposed := by
  dsimp only [StepValid,wholeStep131]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep132 : Instruction 40 := ⟨.mul 1 1,⟨⟨1193708125,3642187519⟩,⟨-57024345142,12709646526⟩,⟨-13703354662,23056371172⟩,⟨-1350609018876,1645929784555⟩,⟨-1112581400458,772629162394⟩,⟨-629334070245,681955230670⟩⟩⟩
noncomputable def wholeBoxes133 := wholeStep132.proposed :: wholeBoxes132
theorem wholeAccepted132 : StepValid wholeStep132.shape wholeBoxes132 wholeStep132.proposed := by
  dsimp only [StepValid,wholeStep132]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep133 : Instruction 40 := ⟨.mul 54 0,⟨⟨1662449997,5141539290⟩,⟨-100210723543,11844767766⟩,⟨-27902767721,29881109415⟩,⟨-2028292596894,3014036651634⟩,⟨-1710828693193,1353928415790⟩,⟨-993625119773,1040642554200⟩⟩⟩
noncomputable def wholeBoxes134 := wholeStep133.proposed :: wholeBoxes133
theorem wholeAccepted133 : StepValid wholeStep133.shape wholeBoxes133 wholeStep133.proposed := by
  dsimp only [StepValid,wholeStep133]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep134 : Instruction 40 := ⟨.neg 0,⟨⟨-5141539290,-1662449997⟩,⟨-11844767766,100210723543⟩,⟨-29881109415,27902767721⟩,⟨-3014036651634,2028292596894⟩,⟨-1353928415790,1710828693193⟩,⟨-1040642554200,993625119773⟩⟩⟩
noncomputable def wholeBoxes135 := wholeStep134.proposed :: wholeBoxes134
theorem wholeAccepted134 : StepValid wholeStep134.shape wholeBoxes134 wholeStep134.proposed := by
  dsimp only [StepValid,wholeStep134]
  exact ⟨by decide,by decide⟩
noncomputable def wholeStep135 : Instruction 40 := ⟨.add 3 0,⟨⟨-4123695895,4492024169⟩,⟨-151518634711,143905642071⟩,⟨-75438818003,78450280078⟩,⟨-6455310522052,6696125543026⟩,⟨-4042269970992,3950409730504⟩,⟨-2790013758206,2704139906162⟩⟩⟩
noncomputable def wholeBoxes136 := wholeStep135.proposed :: wholeBoxes135
theorem wholeAccepted135 : StepValid wholeStep135.shape wholeBoxes135 wholeStep135.proposed := by
  dsimp only [StepValid,wholeStep135]
  exact ⟨by decide,by decide⟩
noncomputable def wholeProgram : List (Instruction 40) := [wholeStep0,wholeStep1,wholeStep2,wholeStep3,wholeStep4,wholeStep5,wholeStep6,wholeStep7,wholeStep8,wholeStep9,wholeStep10,wholeStep11,wholeStep12,wholeStep13,wholeStep14,wholeStep15,wholeStep16,wholeStep17,wholeStep18,wholeStep19,wholeStep20,wholeStep21,wholeStep22,wholeStep23,wholeStep24,wholeStep25,wholeStep26,wholeStep27,wholeStep28,wholeStep29,wholeStep30,wholeStep31,wholeStep32,wholeStep33,wholeStep34,wholeStep35,wholeStep36,wholeStep37,wholeStep38,wholeStep39,wholeStep40,wholeStep41,wholeStep42,wholeStep43,wholeStep44,wholeStep45,wholeStep46,wholeStep47,wholeStep48,wholeStep49,wholeStep50,wholeStep51,wholeStep52,wholeStep53,wholeStep54,wholeStep55,wholeStep56,wholeStep57,wholeStep58,wholeStep59,wholeStep60,wholeStep61,wholeStep62,wholeStep63,wholeStep64,wholeStep65,wholeStep66,wholeStep67,wholeStep68,wholeStep69,wholeStep70,wholeStep71,wholeStep72,wholeStep73,wholeStep74,wholeStep75,wholeStep76,wholeStep77,wholeStep78,wholeStep79,wholeStep80,wholeStep81,wholeStep82,wholeStep83,wholeStep84,wholeStep85,wholeStep86,wholeStep87,wholeStep88,wholeStep89,wholeStep90,wholeStep91,wholeStep92,wholeStep93,wholeStep94,wholeStep95,wholeStep96,wholeStep97,wholeStep98,wholeStep99,wholeStep100,wholeStep101,wholeStep102,wholeStep103,wholeStep104,wholeStep105,wholeStep106,wholeStep107,wholeStep108,wholeStep109,wholeStep110,wholeStep111,wholeStep112,wholeStep113,wholeStep114,wholeStep115,wholeStep116,wholeStep117,wholeStep118,wholeStep119,wholeStep120,wholeStep121,wholeStep122,wholeStep123,wholeStep124,wholeStep125,wholeStep126,wholeStep127,wholeStep128,wholeStep129,wholeStep130,wholeStep131,wholeStep132,wholeStep133,wholeStep134,wholeStep135]
theorem wholeAccepted : Accepted wholeProgram wholeInitial :=
  ⟨wholeAccepted0,⟨wholeAccepted1,⟨wholeAccepted2,⟨wholeAccepted3,⟨wholeAccepted4,⟨wholeAccepted5,⟨wholeAccepted6,⟨wholeAccepted7,⟨wholeAccepted8,⟨wholeAccepted9,⟨wholeAccepted10,⟨wholeAccepted11,⟨wholeAccepted12,⟨wholeAccepted13,⟨wholeAccepted14,⟨wholeAccepted15,⟨wholeAccepted16,⟨wholeAccepted17,⟨wholeAccepted18,⟨wholeAccepted19,⟨wholeAccepted20,⟨wholeAccepted21,⟨wholeAccepted22,⟨wholeAccepted23,⟨wholeAccepted24,⟨wholeAccepted25,⟨wholeAccepted26,⟨wholeAccepted27,⟨wholeAccepted28,⟨wholeAccepted29,⟨wholeAccepted30,⟨wholeAccepted31,⟨wholeAccepted32,⟨wholeAccepted33,⟨wholeAccepted34,⟨wholeAccepted35,⟨wholeAccepted36,⟨wholeAccepted37,⟨wholeAccepted38,⟨wholeAccepted39,⟨wholeAccepted40,⟨wholeAccepted41,⟨wholeAccepted42,⟨wholeAccepted43,⟨wholeAccepted44,⟨wholeAccepted45,⟨wholeAccepted46,⟨wholeAccepted47,⟨wholeAccepted48,⟨wholeAccepted49,⟨wholeAccepted50,⟨wholeAccepted51,⟨wholeAccepted52,⟨wholeAccepted53,⟨wholeAccepted54,⟨wholeAccepted55,⟨wholeAccepted56,⟨wholeAccepted57,⟨wholeAccepted58,⟨wholeAccepted59,⟨wholeAccepted60,⟨wholeAccepted61,⟨wholeAccepted62,⟨wholeAccepted63,⟨wholeAccepted64,⟨wholeAccepted65,⟨wholeAccepted66,⟨wholeAccepted67,⟨wholeAccepted68,⟨wholeAccepted69,⟨wholeAccepted70,⟨wholeAccepted71,⟨wholeAccepted72,⟨wholeAccepted73,⟨wholeAccepted74,⟨wholeAccepted75,⟨wholeAccepted76,⟨wholeAccepted77,⟨wholeAccepted78,⟨wholeAccepted79,⟨wholeAccepted80,⟨wholeAccepted81,⟨wholeAccepted82,⟨wholeAccepted83,⟨wholeAccepted84,⟨wholeAccepted85,⟨wholeAccepted86,⟨wholeAccepted87,⟨wholeAccepted88,⟨wholeAccepted89,⟨wholeAccepted90,⟨wholeAccepted91,⟨wholeAccepted92,⟨wholeAccepted93,⟨wholeAccepted94,⟨wholeAccepted95,⟨wholeAccepted96,⟨wholeAccepted97,⟨wholeAccepted98,⟨wholeAccepted99,⟨wholeAccepted100,⟨wholeAccepted101,⟨wholeAccepted102,⟨wholeAccepted103,⟨wholeAccepted104,⟨wholeAccepted105,⟨wholeAccepted106,⟨wholeAccepted107,⟨wholeAccepted108,⟨wholeAccepted109,⟨wholeAccepted110,⟨wholeAccepted111,⟨wholeAccepted112,⟨wholeAccepted113,⟨wholeAccepted114,⟨wholeAccepted115,⟨wholeAccepted116,⟨wholeAccepted117,⟨wholeAccepted118,⟨wholeAccepted119,⟨wholeAccepted120,⟨wholeAccepted121,⟨wholeAccepted122,⟨wholeAccepted123,⟨wholeAccepted124,⟨wholeAccepted125,⟨wholeAccepted126,⟨wholeAccepted127,⟨wholeAccepted128,⟨wholeAccepted129,⟨wholeAccepted130,⟨wholeAccepted131,⟨wholeAccepted132,⟨wholeAccepted133,⟨wholeAccepted134,⟨wholeAccepted135,True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
noncomputable def whole_m11 : DyadicBivariateJetEnclosure 40 := ⟨⟨45248583011,70828129151⟩,⟨-594103859717,192567844212⟩,⟨-88827200702,292134950094⟩,⟨-14714896646364,13291302726222⟩,⟨-9879652578809,7186706771531⟩,⟨-6111520408518,6613488304987⟩⟩
theorem whole_m11_eq : (finalBoxes wholeProgram wholeInitial).getD 14 (zeroBox 40)=whole_m11 := rfl
noncomputable def whole_kdet : DyadicBivariateJetEnclosure 40 := ⟨⟨-4123695895,4492024169⟩,⟨-151518634711,143905642071⟩,⟨-75438818003,78450280078⟩,⟨-6455310522052,6696125543026⟩,⟨-4042269970992,3950409730504⟩,⟨-2790013758206,2704139906162⟩⟩
theorem whole_kdet_eq : (finalBoxes wholeProgram wholeInitial).getD 0 (zeroBox 40)=whole_kdet := rfl
theorem sameShape : shapes centerProgram=shapes wholeProgram := by decide
theorem kernelShape : shapes wholeProgram =
    shapes CorrectionFactorizedProgramKernel.kernelProgram := by decide
attribute [local irreducible] wholeProgram centerProgram
noncomputable def inputJets (u rho : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA (701/5120) u, BivariateJet2.affineZ (427/2560) rho,
    BivariateJet2.const 1, BivariateJet2.const 2]
noncomputable def outputJet_m11 (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 14 zeroJet
theorem output_value_m11 (u rho t : ℝ) : (outputJet_m11 u rho).value t =
    Correction.Natural.m11 (701/5120+t*(u-(701/5120))) ((701/5120+t*(u-(701/5120)))+(427/2560+t*(rho-(427/2560)))*(1/2-(701/5120+t*(u-(701/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_m11_of_shapes wholeProgram kernelShape (701/5120) (427/2560) u rho t
theorem output_value_one_m11 (u rho : ℝ) : (outputJet_m11 u rho).value 1 =
    Correction.Natural.m11 u (u+rho*(1/2-u)) := by simp [output_value_m11]
noncomputable def outputJet_kdet (u rho : ℝ) : BivariateJet2 :=
  (finalJets wholeProgram (inputJets u rho)).getD 0 zeroJet
theorem output_value_kdet (u rho t : ℝ) : (outputJet_kdet u rho).value t =
    Correction.Natural.kdet (701/5120+t*(u-(701/5120))) ((701/5120+t*(u-(701/5120)))+(427/2560+t*(rho-(427/2560)))*(1/2-(701/5120+t*(u-(701/5120))))) := by
  exact CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes wholeProgram kernelShape (701/5120) (427/2560) u rho t
theorem output_value_one_kdet (u rho : ℝ) : (outputJet_kdet u rho).value 1 =
    Correction.Natural.kdet u (u+rho*(1/2-u)) := by simp [output_value_kdet]

private theorem center_A (x : ℝ) :
    (⟨⟨150538603724,150538603725⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (701/5120) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_A {x t : ℝ} (hx : x∈Icc (35/256:ℝ) (351/2560)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨150323855360,150753352090⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineA (701/5120) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateA
  change (⟨150323855360,150753352090⟩ : DyadicInterval 40).Contains ((Jet2.segment (701/5120) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
private theorem center_Z (x : ℝ) :
    (⟨⟨183395103539,183395103540⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (427/2560) x) 0 := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  norm_num [DyadicInterval.Contains,DyadicInterval.scale]
private theorem whole_Z {x t : ℝ} (hx : x∈Icc (209/1280:ℝ) (109/640)) (ht : t∈Icc (0:ℝ) 1) :
    (⟨⟨179529632972,187260574106⟩,⟨0,0⟩,⟨1099511627776,1099511627776⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩ : DyadicBivariateJetEnclosure 40).Contains (BivariateJet2.affineZ (427/2560) x) t := by
  apply DyadicBivariateJetEnclosure.contains_coordinateZ
  change (⟨179529632972,187260574106⟩ : DyadicInterval 40).Contains ((Jet2.segment (427/2560) x).value t)
  apply DyadicInterval.contains_segment _ _ ht
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
  · norm_num [DyadicInterval.Contains,DyadicInterval.scale]
    constructor <;> linarith [hx.1,hx.2]
theorem initial_center (a z : ℝ) : RegistersContain centerInitial (inputJets a z) 0 := by
  simpa [centerInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 0).cons (DyadicBivariateJetEnclosure.contains_const 40 2 0)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 0)).cons (center_Z z)).cons (center_A a)

theorem initial_whole {a z : ℝ} (ha : a ∈ Icc (35/256:ℝ) (351/2560))
    (hz : z ∈ Icc (209/1280:ℝ) (109/640)) :
    ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInitial (inputJets a z) t := by
  intro t ht
  simpa [wholeInitial,inputJets,DyadicBivariateJetEnclosure.const,DyadicInterval.ofInt,DyadicInterval.scale] using
    ((((RegistersContain.nil 40 t).cons (DyadicBivariateJetEnclosure.contains_const 40 2 t)).cons
      (DyadicBivariateJetEnclosure.contains_const 40 1 t)).cons (whole_Z hz ht)).cons (whole_A ha ht)

theorem initial_sound (a z : ℝ) : ∀ i, ((inputJets a z).getD i zeroJet).DirectionalSoundOn
    (a-701/5120) (z-427/2560) (Icc (0:ℝ) 1) := by
  intro i t ht
  have hconst (c : ℝ) : (BivariateJet2.const c).DirectionalSoundAt (a-701/5120) (z-427/2560) t := by
    simpa only [BivariateJet2.DirectionalSoundAt,BivariateJet2.projection_const] using Jet2.soundAt_const c t
  have h : RegistersSound (inputJets a z) (a-701/5120) (z-427/2560) t :=
    ((((RegistersSound.nil _ _ t).cons (hconst 2)).cons (hconst 1)).cons
      (BivariateJet2.soundOn_affineZ (427/2560) z (a-701/5120) _ t ht)).cons
      (BivariateJet2.soundOn_affineA (701/5120) a (z-427/2560) _ t ht)
  exact h i

theorem taylor_positive_m11 : 0 < BivariateJetEnclosure.taylorLower
    center_m11.toReal whole_m11.toReal (1/5120) (9/2560) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_m11,whole_m11]
theorem positive_m11 {a z : ℝ} (ha : a∈Icc (35/256:ℝ) (351/2560))
    (hz : z∈Icc (209/1280:ℝ) (109/640)) : 0 < Correction.Natural.m11 a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 14 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/2560 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_m11_eq,whole_m11_eq]; exact taylor_positive_m11)
  change 0 < (outputJet_m11 a z).value 1 at hp
  simpa only [output_value_one_m11] using hp
theorem taylor_positive_kdet : 0 < BivariateJetEnclosure.taylorLower
    center_kdet.toReal whole_kdet.toReal (1/5120) (9/2560) := by
  norm_num [BivariateJetEnclosure.taylorLower,JetBounds.Interval.magnitude,
    DyadicBivariateJetEnclosure.toReal,DyadicInterval.toReal,DyadicInterval.scale,center_kdet,whole_kdet]
theorem positive_kdet {a z : ℝ} (ha : a∈Icc (35/256:ℝ) (351/2560))
    (hz : z∈Icc (209/1280:ℝ) (109/640)) : 0 < Correction.Natural.kdet a (a+z*(1/2-a)) := by
  have hp := value_pos_of_accepted_taylor centerProgram wholeProgram 0 sameShape
    (initial_center a z) (initial_whole ha hz) (initial_sound a z) centerAccepted wholeAccepted
    (show (0:ℝ)≤1/5120 by norm_num) (show (0:ℝ)≤9/2560 by norm_num)
    (by rw [abs_le]; constructor <;> linarith [ha.1,ha.2])
    (by rw [abs_le]; constructor <;> linarith [hz.1,hz.2])
    (by rw [center_kdet_eq,whole_kdet_eq]; exact taylor_positive_kdet)
  change 0 < (outputJet_kdet a z).value 1 at hp
  simpa only [output_value_one_kdet] using hp

theorem actual_minors_positive {u rho : ℝ} (hu : u∈Icc (35/256:ℝ) (351/2560))
    (hr : rho∈Icc (209/1280:ℝ) (109/640)) (hr1 : rho < 1) :
    0 < Correction.Mleft (H u) (H (u+rho*(1/2-u))) ∧
    0 < Correction.Mdet (H u) (H (u+rho*(1/2-u))) := by
  let w := u+rho*(1/2-u)
  have hu0 : 0<u := by linarith [hu.1]
  have hgap : 0<1/2-u := by linarith [hu.2]
  have huw : u<w := by dsimp [w]; nlinarith [mul_pos (show 0<rho by linarith [hr.1]) hgap]
  have hw : w<1/2 := by dsimp [w]; nlinarith [mul_pos (show 0<1-rho by linarith [hr1]) hgap]
  have heq := Correction.Natural.kernel_eq_actual_ratio hu0 hgap (show 0<rho by linarith [hr.1]) hr1
  have hm := positive_m11 hu hr
  have hk := positive_kdet hu hr
  rw [heq.1] at hm
  rw [heq.2] at hk
  have hf0 := H_pos (hu0.trans huw) (show w<1 by linarith)
  have hf1 : H w<1 := by
    have h := H_strictMonoOn ⟨(hu0.trans huw).le,hw.le⟩
      (by norm_num : (1/2:ℝ)∈Icc 0 (1/2)) hw
    simpa only [H_half] using h
  exact ⟨hm,(Correction.Mdet_pos_iff_Kfactored_pos hf0 hf1).mpr hk⟩

#print axioms centerAccepted
#print axioms wholeAccepted
#print axioms actual_minors_positive
end GeneralCK.Certificates.LaneCB.RB2Cell002433

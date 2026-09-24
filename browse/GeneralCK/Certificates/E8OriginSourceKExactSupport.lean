import GeneralCK.Certificates.E8OriginSourceKExactReplay

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

def kSupport : Finset (Nat × Nat) :=
  ((Finset.range 28).product (Finset.range 28)).filter
    (fun e => 1 ≤ e.1 + e.2 ∧ e.1 + e.2 ≤ 27 ∧ (e.1 + e.2) % 2 = 1)

theorem coeffAt_degree_1 (i j : Nat) (h : i + j = 1) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 1 := by omega
  interval_cases i
  · have hj : j = 1 := by omega
    subst j
    exact coeff_0_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_1_0

theorem coeffAt_degree_3 (i j : Nat) (h : i + j = 3) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 3 := by omega
  interval_cases i
  · have hj : j = 3 := by omega
    subst j
    exact coeff_0_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_1_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_2_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_3_0

theorem coeffAt_degree_5 (i j : Nat) (h : i + j = 5) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 5 := by omega
  interval_cases i
  · have hj : j = 5 := by omega
    subst j
    exact coeff_0_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_1_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_2_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_3_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_4_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_5_0

theorem coeffAt_degree_7 (i j : Nat) (h : i + j = 7) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 7 := by omega
  interval_cases i
  · have hj : j = 7 := by omega
    subst j
    exact coeff_0_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_1_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_2_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_3_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_4_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_5_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_6_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_7_0

theorem coeffAt_degree_9 (i j : Nat) (h : i + j = 9) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 9 := by omega
  interval_cases i
  · have hj : j = 9 := by omega
    subst j
    exact coeff_0_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_1_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_2_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_3_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_4_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_5_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_6_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_7_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_8_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_9_0

theorem coeffAt_degree_11 (i j : Nat) (h : i + j = 11) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 11 := by omega
  interval_cases i
  · have hj : j = 11 := by omega
    subst j
    exact coeff_0_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_1_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_2_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_3_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_4_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_5_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_6_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_7_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_8_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_9_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_10_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_11_0

theorem coeffAt_degree_13 (i j : Nat) (h : i + j = 13) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 13 := by omega
  interval_cases i
  · have hj : j = 13 := by omega
    subst j
    exact coeff_0_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_1_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_2_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_3_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_4_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_5_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_6_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_7_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_8_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_9_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_10_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_11_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_12_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_13_0

theorem coeffAt_degree_15 (i j : Nat) (h : i + j = 15) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 15 := by omega
  interval_cases i
  · have hj : j = 15 := by omega
    subst j
    exact coeff_0_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_1_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_2_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_3_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_4_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_5_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_6_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_7_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_8_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_9_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_10_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_11_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_12_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_13_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_14_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_15_0

theorem coeffAt_degree_17 (i j : Nat) (h : i + j = 17) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 17 := by omega
  interval_cases i
  · have hj : j = 17 := by omega
    subst j
    exact coeff_0_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_1_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_2_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_3_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_4_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_5_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_6_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_7_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_8_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_9_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_10_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_11_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_12_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_13_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_14_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_15_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_16_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_17_0

theorem coeffAt_degree_19 (i j : Nat) (h : i + j = 19) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 19 := by omega
  interval_cases i
  · have hj : j = 19 := by omega
    subst j
    exact coeff_0_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_1_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_2_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_3_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_4_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_5_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_6_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_7_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_8_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_9_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_10_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_11_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_12_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_13_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_14_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_15_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_16_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_17_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_18_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_19_0

theorem coeffAt_degree_21 (i j : Nat) (h : i + j = 21) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 21 := by omega
  interval_cases i
  · have hj : j = 21 := by omega
    subst j
    exact coeff_0_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_1_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_2_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_3_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_4_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_5_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_6_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_7_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_8_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_9_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_10_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_11_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_12_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_13_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_14_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_15_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_16_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_17_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_18_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_19_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_20_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_21_0

theorem coeffAt_degree_23 (i j : Nat) (h : i + j = 23) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 23 := by omega
  interval_cases i
  · have hj : j = 23 := by omega
    subst j
    exact coeff_0_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_1_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_2_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_3_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_4_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_5_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_6_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_7_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_8_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_9_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_10_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_11_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_12_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_13_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_14_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_15_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_16_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_17_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_18_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_19_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_20_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_21_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_22_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_23_0

theorem coeffAt_degree_25 (i j : Nat) (h : i + j = 25) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 25 := by omega
  interval_cases i
  · have hj : j = 25 := by omega
    subst j
    exact coeff_0_25
  · have hj : j = 24 := by omega
    subst j
    exact coeff_1_24
  · have hj : j = 23 := by omega
    subst j
    exact coeff_2_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_3_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_4_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_5_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_6_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_7_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_8_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_9_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_10_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_11_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_12_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_13_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_14_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_15_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_16_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_17_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_18_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_19_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_20_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_21_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_22_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_23_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_24_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_25_0

theorem coeffAt_degree_27 (i j : Nat) (h : i + j = 27) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 27 := by omega
  interval_cases i
  · have hj : j = 27 := by omega
    subst j
    exact coeff_0_27
  · have hj : j = 26 := by omega
    subst j
    exact coeff_1_26
  · have hj : j = 25 := by omega
    subst j
    exact coeff_2_25
  · have hj : j = 24 := by omega
    subst j
    exact coeff_3_24
  · have hj : j = 23 := by omega
    subst j
    exact coeff_4_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_5_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_6_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_7_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_8_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_9_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_10_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_11_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_12_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_13_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_14_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_15_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_16_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_17_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_18_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_19_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_20_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_21_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_22_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_23_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_24_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_25_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_26_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_27_0

theorem coeffAt_productData_eq_kData_on_support
    (e : Nat × Nat) (he : e ∈ kSupport) :
    coeffAt productData e.1 e.2 = coeffAt kData e.1 e.2 := by
  rcases e with ⟨i, j⟩
  simp [kSupport] at he
  have hd : i + j = 1 ∨ i + j = 3 ∨ i + j = 5 ∨ i + j = 7 ∨
      i + j = 9 ∨ i + j = 11 ∨ i + j = 13 ∨ i + j = 15 ∨
      i + j = 17 ∨ i + j = 19 ∨ i + j = 21 ∨ i + j = 23 ∨
      i + j = 25 ∨ i + j = 27 := by omega
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact coeffAt_degree_1 i j h
  · exact coeffAt_degree_3 i j h
  · exact coeffAt_degree_5 i j h
  · exact coeffAt_degree_7 i j h
  · exact coeffAt_degree_9 i j h
  · exact coeffAt_degree_11 i j h
  · exact coeffAt_degree_13 i j h
  · exact coeffAt_degree_15 i j h
  · exact coeffAt_degree_17 i j h
  · exact coeffAt_degree_19 i j h
  · exact coeffAt_degree_21 i j h
  · exact coeffAt_degree_23 i j h
  · exact coeffAt_degree_25 i j h
  · exact coeffAt_degree_27 i j h

theorem p0Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p0Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p0Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p1Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p1Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p1Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p2Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p2Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p2Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p3Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p3Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p3Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p4Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p4Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p4Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p5Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p5Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p5Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p6Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p6Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p6Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p7Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p7Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p7Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p8Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p8Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p8Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p9Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p9Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p9Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p10Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p10Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p10Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

theorem p11Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p11Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p11Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

end GeneralCK.Certificates.E8OriginSourceKExactReplay

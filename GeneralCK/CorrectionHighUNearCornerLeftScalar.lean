import GeneralCK.CorrectionHighUNearCornerLogitBounds

namespace GeneralCK.Correction.HighU

/-- The remaining left-minor calculation is an exact rational polynomial
estimate once the three analytic component bounds have been supplied. -/
theorem nearCorner_left_minor_scalar_bound
    {T rho A W eta : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1 / 10000)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1 / 100)
    (hA : 2 * (1 / 4 - T) - T * (1 / 6000 + rho ^ 3) ≤ A)
    (hW : W ≤ 8 + (117 / 5 : ℝ) * T)
    (heta0 : 0 ≤ eta) (heta : eta ≤ 3 * rho * T) :
    T / 2 ≤ A - W * (1 / 4 - T) ^ 2 * (1 + eta) ^ 2 := by
  let p : ℝ := 1 / 4 - T
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 / 4 := by dsimp [p]; linarith
  have hp2 : p ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hr3 : rho ^ 3 ≤ (1 / 1000000 : ℝ) := by
    calc
      rho ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := by gcongr
      _ = _ := by norm_num
  have hprod : 0 ≤ 3 * rho * T := by positivity
  have hprod1 : 3 * rho * T ≤ (3 / 1000000 : ℝ) := by
    calc
      3 * rho * T ≤ 3 * (1 / 100 : ℝ) * (1 / 10000 : ℝ) := by gcongr
      _ = _ := by norm_num
  have hsq : (1 + 3 * rho * T) ^ 2 ≤ (1 + (3 / 1000000 : ℝ)) ^ 2 := by gcongr
  have hb2 : 24 * rho * (2 + 3 * rho * T) ≤
      (6 / 25 : ℝ) * (2 + 3 / 1000000) := by
    apply mul_le_mul (by linarith : 24 * rho ≤ (6 / 25 : ℝ))
      (by linarith : 2 + 3 * rho * T ≤ (2 + 3 / 1000000 : ℝ))
      (by positivity) (by norm_num)
  let B : ℝ := (117 / 5 : ℝ) * (1 + 3 * rho * T) ^ 2 +
    24 * rho * (2 + 3 * rho * T)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ (239 / 10 : ℝ) := by dsimp [B]; nlinarith only [hsq, hb2]
  have hpB : p ^ 2 * B ≤ (239 / 160 : ℝ) := by
    have h := mul_le_mul hp2 hB1 hB0 (by norm_num : (0 : ℝ) ≤ 1 / 16)
    norm_num at h ⊢
    exact h
  have hRank : W * p ^ 2 * (1 + eta) ^ 2 ≤
      8 * p ^ 2 + (239 / 160 : ℝ) * T := by
    calc
      W * p ^ 2 * (1 + eta) ^ 2 ≤
          (8 + (117 / 5 : ℝ) * T) * p ^ 2 * (1 + eta) ^ 2 := by gcongr
      _ ≤ (8 + (117 / 5 : ℝ) * T) * p ^ 2 * (1 + 3 * rho * T) ^ 2 := by gcongr
      _ = 8 * p ^ 2 + T * (p ^ 2 * B) := by dsimp [B]; ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hpB hT]
  have hid : 2 * p - 8 * p ^ 2 = 8 * p * T := by dsimp [p]; ring
  have hcoef : (1 / 2 : ℝ) ≤ 8 * p - 1 / 6000 - rho ^ 3 - 239 / 160 := by
    dsimp [p]
    linarith only [hT1, hr3]
  have hfinal := mul_le_mul_of_nonneg_left hcoef hT
  change T / 2 ≤ A - W * p ^ 2 * (1 + eta) ^ 2
  change 2 * p - T * (1 / 6000 + rho ^ 3) ≤ A at hA
  nlinarith only [hA, hRank, hid, hfinal]

#print axioms nearCorner_left_minor_scalar_bound

end GeneralCK.Correction.HighU

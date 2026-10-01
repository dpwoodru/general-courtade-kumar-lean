import GeneralCK.PureGapDoubleCapLowTailRatioIncrement

/-! The implicit low-cap contact equation turns the regular-ratio
mean-value bound into a concrete separation inequality. It remains a
precursor to the sign of the low-cap residual. -/

namespace GeneralCK.Reflection

open Set Certificates.Reflection

theorem coupled_regular_contact_separation {k c y : ℝ}
    (hk : 0 < k) (hkc : k < c) (hcy : c < y) (hy : y < 1)
    (hEy : 0 < biasE y)
    (hEq : biasE c = c * biasE y / k) :
    (y - c) * k ^ 2 * biasB c ≤
      (y - k) * c ^ 2 * biasE y := by
  have hc : 0 < c := hk.trans hkc
  have hc1 : c < 1 := hcy.trans hy
  have hEc : 0 < biasE c := biasE_pos_wide (by linarith [hc]) hc1
  have hRc : regularRatio c = k / biasE y := by
    unfold regularRatio
    rw [hEq]
    field_simp [hk.ne', hEy.ne', hc.ne']
  have hinc := regularRatio_increment_lower hc hcy.le hy
  have hgap : regularRatio y - regularRatio c = (y - k) / biasE y := by
    rw [hRc]
    change y / biasE y - k / biasE y = (y - k) / biasE y
    ring
  have hinc' : (y - c) * (biasB c / (biasE c) ^ 2) ≤
      (y - k) / biasE y := by simpa only [hgap] using hinc
  have hmul := mul_le_mul_of_nonneg_right hinc' hEy.le
  have hpoly0 : (y - c) * biasB c * biasE y ≤
      (y - k) * (biasE c) ^ 2 := by
    have hmul' : ((y - c) * biasB c * biasE y) /
        (biasE c) ^ 2 ≤ y - k := by
      have hrhs : (y - k) / biasE y * biasE y = y - k := by
        field_simp [hEy.ne']
      rw [hrhs] at hmul
      have hleft : (y - c) * (biasB c / (biasE c) ^ 2) * biasE y =
          ((y - c) * biasB c * biasE y) / (biasE c) ^ 2 := by ring
      simpa only [hleft] using hmul
    exact (div_le_iff₀ (sq_pos_of_pos hEc)).mp hmul'
  have hEcSquare : (biasE c) ^ 2 * k ^ 2 =
      c ^ 2 * (biasE y) ^ 2 := by
    rw [hEq]
    field_simp [hk.ne']
  have hmulK := mul_le_mul_of_nonneg_right hpoly0 (sq_nonneg k)
  have hfactored : biasE y * ((y - c) * k ^ 2 * biasB c) ≤
      biasE y * ((y - k) * c ^ 2 * biasE y) := by
    calc
      biasE y * ((y - c) * k ^ 2 * biasB c) =
          ((y - c) * biasB c * biasE y) * k ^ 2 := by ring
      _ ≤ ((y - k) * (biasE c) ^ 2) * k ^ 2 := hmulK
      _ = biasE y * ((y - k) * c ^ 2 * biasE y) := by
        calc
          ((y - k) * (biasE c) ^ 2) * k ^ 2 =
              (y - k) * ((biasE c) ^ 2 * k ^ 2) := by ring
          _ = (y - k) * (c ^ 2 * (biasE y) ^ 2) := by rw [hEcSquare]
          _ = biasE y * ((y - k) * c ^ 2 * biasE y) := by ring
  exact (mul_le_mul_iff_right₀ hEy).mp hfactored

#print axioms coupled_regular_contact_separation

end GeneralCK.Reflection

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_bias_separation {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    (doubleCapLowTailY m - doubleCapLowTailC m) *
        (1 - 2 * m) ^ 2 * biasB (doubleCapLowTailC m) ≤
      (doubleCapLowTailY m - (1 - 2 * m)) *
        (doubleCapLowTailC m) ^ 2 * biasE (doubleCapLowTailY m) := by
  have hk : 0 < 1 - 2 * m := by linarith
  have hbetween := doubleCapLowTailC_between hm hmq
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hEy : 0 < biasE (doubleCapLowTailY m) := by
    rw [doubleCapLowTailY_entropy hm hmq]
    exact mul_pos log_two_pos hh
  exact coupled_regular_contact_separation hk hbetween.1 hbetween.2
    hy1 hEy (doubleCapLowTailC_entropy_equation hm hmq)

#print axioms doubleCapLowTail_bias_separation

end GeneralCK

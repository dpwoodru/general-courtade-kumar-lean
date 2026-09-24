import GeneralCK.Certificates.E8TAxisOneCellArithmetic
import GeneralCK.Certificates.E8TAxisDeltaDirectionalJet
import GeneralCK.Certificates.E8TAxisStableScalar

/-! Exact geometry for the first positive-t historical bridge leaf.
The saved displacement radii do not cover the t=0 axis. -/

namespace GeneralCK.Certificates.E8TAxisOneCellGeometry

open GeneralCK DyadicInterval E8TAxisOneCellArithmetic E8TAxisDeltaDirectionalJet Set

noncomputable def sLower : ℝ :=
  13500000000000000000000000000000000000000000000000000000000637236764453 /
  200000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def tLower : ℝ :=
  24999999999999999999999999999999999999999999999999999999997261873277741 /
  2500000000000000000000000000000000000000000000000000000000000000000000000

noncomputable def centerS : ℝ := 57 / 800
noncomputable def centerT : ℝ := 3 / 200

def InFirstCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ 3 / 40 ∧ tLower ≤ t ∧ t ≤ 1 / 50

theorem center_mem : InFirstCell centerS centerT := by
  norm_num [InFirstCell, sLower, tLower, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InFirstCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, tLower] at hs0 ht0
  norm_num [Contains, ds, dt, centerS, centerT, scale, precision]
  constructor <;> constructor <;> linarith

theorem segment_mem {s t u : ℝ} (h : InFirstCell s t) (hu : u ∈ Icc (0 : ℝ) 1) :
    InFirstCell (centerS + (s - centerS) * u) (centerT + (t - centerT) * u) := by
  have segment {a b c x : ℝ} (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
      c + (x - c) * u ∈ Icc a b := by
    have hh := (convex_Icc a b) hc hx (sub_nonneg.mpr hu.2) hu.1
      (show (1 - u) + u = 1 by ring)
    convert hh using 1 <;> simp only [smul_eq_mul] <;> ring
  have hc := center_mem
  have hs := segment ⟨hc.1, hc.2.1⟩ ⟨h.1, h.2.1⟩
  have ht := segment hc.2.2 h.2.2
  exact ⟨hs.1, hs.2, ht⟩

theorem inputsInRange_of_cell {s t : ℝ} (h : InFirstCell s t)
    (hmax : (17 / 100 : ℝ) ∈ e8SlopeRange) : InputsInRange s t := by
  have hs : 0 < s := lt_of_lt_of_le (by norm_num [sLower]) h.1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num [tLower]) h.2.2.1
  have hB : 2 * s + t ≤ 17 / 100 := by linarith [h.2.1, h.2.2.2]
  exact ⟨e8SlopeRange_downward hmax ht (by linarith),
    e8SlopeRange_downward hmax (by positivity) hB,
    e8SlopeRange_downward hmax (by positivity) (by linarith),
    e8SlopeRange_downward hmax hs (by linarith)⟩

/-- A coarse analytic range bound suffices for all Taylor segments.  This
does not assert coverage by any of the numerical inverse-parameter boxes. -/
theorem upperSlope_mem : (17 / 100 : ℝ) ∈ e8SlopeRange := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hc : 2 ≤ 2 / Real.log 2 := (le_div_iff₀ hL).mpr (by linarith)
  have hf : 0 ≤ E8TAxisStableScalar.r 1 * E8TAxisStableScalar.h 1 /
      (E8TAxisStableScalar.q 1 * E8TAxisStableScalar.ell 1) := by
    exact (div_pos
      (mul_pos (E8TAxisStableScalar.r_pos (by norm_num))
        (E8TAxisStableScalar.h_pos (by norm_num)))
      (mul_pos (E8TAxisStableScalar.q_pos 1)
        (E8TAxisStableScalar.ell_pos (by norm_num)))).le
  have hY : 2 ≤ E8TAxisStableScalar.Y 1 := by
    unfold E8TAxisStableScalar.Y
    nlinarith [mul_nonneg (div_pos (by norm_num : (0 : ℝ) < 2) hL).le hf]
  apply e8SlopeRange_downward
    (show E8TAxisStableScalar.Y 1 ∈ e8SlopeRange from
      ⟨E8TAxisStableScalar.X 1, E8TAxisStableScalar.X_pos (by norm_num),
        E8TAxisStableScalar.e8Theta_X (by norm_num)⟩) (by norm_num)
  linarith

theorem segment_inputsInRange {s t : ℝ} (h : InFirstCell s t)
    :
    ∀ u ∈ Icc (0 : ℝ) 1,
      InputsInRange (centerS + (s - centerS) * u) (centerT + (t - centerT) * u) :=
  fun _ hu => inputsInRange_of_cell (segment_mem h hu) upperSlope_mem

#print axioms displacement_mem
#print axioms segment_inputsInRange

end GeneralCK.Certificates.E8TAxisOneCellGeometry

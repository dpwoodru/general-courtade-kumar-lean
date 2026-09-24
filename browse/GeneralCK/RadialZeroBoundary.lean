import GeneralCK.RadialConvexity
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_tendsto_zero_right {h : ℝ} (hh : 0 < h) :
    Tendsto (fun z => radialContact z h) (𝓝[>] 0) (𝓝 (1/2)) := by
  have hlim : Tendsto (fun z : ℝ => (1/2:ℝ)-z/(2*h)) (𝓝[>] 0) (𝓝 (1/2)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_id.div_const (2*h))).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hc := radialContact_equation hz hh
    have hb := mul_le_mul_of_nonneg_left (H_le_one (radialContact z h)) (le_of_lt hz)
    have hp : 0 < 2*h := by positivity
    have hb' : (1/2:ℝ)-radialContact z h ≤ z/(2*h) :=
      (le_div_iff₀ hp).mpr (by nlinarith)
    linarith
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (radialContact_lt_half hz hh).le

theorem J_radialContact_tendsto_zero_right {h : ℝ} (hh : 0 < h) :
    Tendsto (fun z => J (radialContact z h)) (𝓝[>] 0) (𝓝 0) := by
  have hj := (hasDerivAt_J (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).continuousAt
  have ht := hj.tendsto.comp (radialContact_tendsto_zero_right hh)
  have hjhalf : J (1/2) = 0 := by norm_num [J]
  simpa only [hjhalf,Function.comp_def] using ht

theorem hasDerivWithinAt_F_zero {h : ℝ} (hh : 0 < h) :
    HasDerivWithinAt (fun z => F z h) 0 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by
    ext z
    simp only [Set.mem_sdiff,mem_Ici,mem_singleton_iff,mem_Ioi]
    constructor
    · rintro ⟨hz,hn⟩; exact lt_of_le_of_ne hz (Ne.symm hn)
    · intro hz; exact ⟨hz.le,hz.ne'⟩
  rw [hset]
  apply (J_radialContact_tendsto_zero_right hh).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : 0 < z := hz
  simp [slope_def_field,F,hz0.ne',mul_div_cancel_left₀]

theorem radialContact_nonpos_radius {z h : ℝ} (hz : z ≤ 0) (hh : 0 < h) :
    radialContact z h = 0 := by
  have he : {v : ℝ | 0 < v ∧ v < 1/2 ∧ z*H v=h*(1-2*v)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hH : 0 ≤ H v := H_nonneg hv.1.le (by linarith [hv.2.1])
    have hl : z*H v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hz hH
    have hr : 0 < h*(1-2*v) := mul_pos hh (by linarith [hv.2.1])
    linarith [hv.2.2]
  simp only [radialContact,he,Real.sInf_empty]

/-- The total real-valued definition is zero on the nonpositive-radius side. -/
theorem F_nonpos_radius {z h : ℝ} (hz : z ≤ 0) (hh : 0 < h) : F z h = 0 := by
  simp [F,radialContact_nonpos_radius hz hh,J]

/-- The raw extension has first derivative zero at radius zero from both sides. -/
theorem hasDerivAt_F_zero {h : ℝ} (hh : 0 < h) :
    HasDerivAt (fun z => F z h) 0 0 := by
  have hl : HasDerivWithinAt (fun z => F z h) 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const (0:ℝ) (Iic (0:ℝ)) (0:ℝ)).congr
      (fun z hz => F_nonpos_radius hz hh) (by simp [F])
  have hu := (hasDerivWithinAt_F_zero hh).union hl
  have hs : Ici (0:ℝ) ∪ Iic 0 = univ := by
    ext z
    simp only [mem_union,mem_Ici,mem_Iic,mem_univ,iff_true]
    exact le_total 0 z
  rw [hs] at hu
  exact hasDerivWithinAt_univ.mp hu

end GeneralCK

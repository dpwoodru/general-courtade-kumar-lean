import GeneralCK.ReflectionSmallBiasPartialCauchy

/-! Mixed Cauchy and mean-value estimates for an order-24 remainder. -/

namespace GeneralCK.Reflection.SmallBiasRemainder

open Set Filter Asymptotics SmallBiasPartialCauchy
open scoped Topology

theorem norm_in_auxiliary_disc {a : ℝ} {c z : ℂ}
    (hc : ‖c‖ ≤ a) (hz : z ∈ Metric.closedBall c (a/7)) :
    ‖z‖ ≤ 8*a/7 := by
  have hh := norm_le_of_mem_closedBall hz
  calc
    ‖z‖ ≤ ‖c‖ + a/7 := hh
    _ ≤ a + a/7 := add_le_add hc le_rfl
    _ = 8*a/7 := by ring

theorem remainder_curvature_bound {f : ℂ × ℂ → ℂ}
    (hf : ∀ z, ‖z‖ ≤ (21/50:ℝ) → AnalyticAt ℂ f z)
    (hbnd : ∀ z, ‖z‖ ≤ (21/50:ℝ) → ‖f z‖ ≤ 4)
    (haxis : ∀ a : ℂ, f (a, 0) = 0)
    (horder : f =O[𝓝 0] (fun z : ℂ × ℂ => ‖z‖ ^ 24))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (ha1 : a ≤ 3/20) :
    ‖partialAA f ((a:ℂ), (b:ℂ))‖ < (1/8:ℝ) * a^3 * b := by
  have haR : a < (21/50:ℝ) := by linarith
  have hr : 0 < a/7 := by positivity
  have hsmall : 8*a/7 < (21/50:ℝ) := by linarith
  have hanorm : ‖(a:ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hbnorm : ‖(b:ℂ)‖ = b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hd : DifferentiableOn ℂ f (Metric.ball 0 (21/50:ℝ)) := by
    intro z hz
    exact (hf z (by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (Metric.ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt
  have hzero : f 0 = 0 := haxis 0
  let M : ℝ := 4 * ((8*a/7)/(21/50:ℝ))^24
  let C : ℝ := 2*M/(a/7)^3
  have hlocal : ∀ v : ℂ, ‖v‖ ≤ a →
      ‖deriv (fun w : ℂ => partialAA f ((a:ℂ), w)) v‖ ≤ C := by
    intro v hv
    have hgeom : ∀ z ∈ Metric.closedBall (a:ℂ) (a/7),
        ∀ w ∈ Metric.closedBall v (a/7), ‖(z,w)‖ ≤ 8*a/7 := by
      intro z hz w hw
      rw [Prod.norm_def]
      exact max_le (norm_in_auxiliary_disc hanorm.le hz) (norm_in_auxiliary_disc hv hw)
    apply norm_deriv_partialAA_le hr
    · intro z hz w hw
      exact hf (z,w) ((hgeom z hz w hw).trans hsmall.le)
    · intro z hz w hw
      have hz' := hgeom z hz w hw
      have hh := norm_le_of_order hd hzero
        (fun u hu => hbnd u (by simpa only [Metric.mem_closedBall, dist_zero_right] using
          (Metric.ball_subset_closedBall hu))) horder (hz'.trans_lt hsmall)
      calc
        ‖f (z,w)‖ ≤ 4 * (‖(z,w)‖ / (21/50:ℝ))^24 := hh
        _ ≤ M := by dsimp [M]; gcongr; exact hz'
  have hbase : partialAA f ((a:ℂ), 0) = 0 := by
    have hz : ‖((a:ℂ), (0:ℂ))‖ ≤ (21/50:ℝ) := by
      simp only [Prod.norm_def, norm_zero, hanorm, max_eq_left ha.le]
      exact haR.le
    rw [partialAA_eq_deriv2 (hf _ hz)]
    have hh : (fun z : ℂ => f (z,0)) = fun _ => (0:ℂ) := funext haxis
    rw [hh]
    simp
  have hmean : ‖partialAA f ((a:ℂ), (b:ℂ))‖ ≤ C*b := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℂ) (f := fun w : ℂ => partialAA f ((a:ℂ), w))
      (s := Metric.closedBall (0:ℂ) a) (C := C)
      (fun v hv => by
        have hv' : ‖v‖ ≤ a := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
        have hz : ‖((a:ℂ),v)‖ ≤ (21/50:ℝ) := by
          rw [Prod.norm_def, hanorm]
          exact (max_le le_rfl hv').trans haR.le
        exact ((analyticAt_partialAA (hf _ hz)).comp
          (analyticAt_const.prod analyticAt_id)).differentiableAt)
      (fun v hv => hlocal v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
      (convex_closedBall (0:ℂ) a)
      (show (0:ℂ) ∈ Metric.closedBall (0:ℂ) a from Metric.mem_closedBall_self ha.le)
      (show (b:ℂ) ∈ Metric.closedBall (0:ℂ) a from by
        simpa only [Metric.mem_closedBall, dist_zero_right, hbnorm] using hba)
    simpa only [hbase, sub_zero, hbnorm] using hh
  have hid : C*b =
      (8*7^3*((8/7:ℝ)/(21/50:ℝ))^24*a^18) * (a^3*b) := by
    dsimp [C, M]
    field_simp [ha.ne']
    <;> ring
  calc
    _ ≤ C*b := hmean
    _ = (8*7^3*((8/7:ℝ)/(21/50:ℝ))^24*a^18) * (a^3*b) := hid
    _ < (1/8:ℝ) * (a^3*b) :=
      mul_lt_mul_of_pos_right (normalized_remainder_bound ha.le ha1) (by positivity)
    _ = _ := by ring

end GeneralCK.Reflection.SmallBiasRemainder

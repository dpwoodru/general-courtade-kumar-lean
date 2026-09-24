import E8BoundedArgumentJets

namespace GeneralCK.E8LargeTSAxis

open Set Certificates
open E8CompactAnchorRegularJetDerivatives E8TAxisDeltaDirectionalJet
open E8TAxisStableInterval E8TAxisReparamInterval DyadicInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem endpoint_jets_tight : e8RegularQ (63/20) ≤ 1/2 ∧
    deriv e8RegularQ (63/20) ≤ 1/5 ∧ deriv (deriv e8RegularQ) (63/20) ≤ 1/10 := by
  obtain ⟨a, ha, hapos, hay⟩ := E8LargeSShift.covers
  have hc := checked_stable_contains_canonical E8LargeSShift.whole_primitive_checks.1
    E8LargeSShift.whole_primitive_checks.2 E8LargeSShift.logTwo_checked
    E8LargeSShift.whole_denominators E8LargeSShift.whole_y_derivative_positive ha hapos
  rw [hay] at hc
  have h0 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d0.hi*2 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h1 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d1.hi*5 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have h2 : (eval (xBox E8LargeSShift.wholeInput) (yBox E8LargeSShift.wholeInput)).d2.hi*10 ≤
      scale E8LargeSShift.precision := by decide +kernel
  have upper {b : DyadicInterval E8LargeSShift.precision} {x : ℝ} {n : ℤ}
      (hn : 0 < n) (hx : b.Contains x) (hb : b.hi*n ≤ scale E8LargeSShift.precision) :
      x ≤ 1/(n : ℝ) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').2
    apply (mul_le_mul_iff_right₀ (scale_cast_pos E8LargeSShift.precision)).mp
    have hh : (b.hi : ℝ)*(n : ℝ) ≤ (scale E8LargeSShift.precision : ℝ) := by exact_mod_cast hb
    have hm := (mul_le_mul_of_nonneg_right hx.2 hn'.le).trans hh
    nlinarith only [hm]
  have hv : qJet.d0 (63/20) ≤ 1/2 := upper (by norm_num : (0:ℤ)<2) hc.1 h0
  have hd : qJet.d1 (63/20) ≤ 1/5 := upper (by norm_num : (0:ℤ)<5) hc.2.1 h1
  have hdd : qJet.d2 (63/20) ≤ 1/10 := upper (by norm_num : (0:ℤ)<10) hc.2.2.1 h2
  rw [qJet_d0, ← e8RegularQ_eq_e8Q (by norm_num : (0 : ℝ) ≤ 63/20)] at hv
  rw [qJet_d1_eq_deriv_regular endpoint_mem] at hd
  rw [qJet_d2_eq_deriv2_regular endpoint_mem] at hdd
  exact ⟨hv, hd, hdd⟩

theorem bounded_argument_jets_tight {s : ℝ} (hs : s ∈ e8SlopeRange) (hstop : s ≤ 63/20) :
    e8RegularQ s ≤ 1/2 ∧ deriv e8RegularQ s ≤ 1/5 ∧ deriv (deriv e8RegularQ) s ≤ 1/10 := by
  have hs0 : 0 ≤ s := le_of_lt (e8SlopeRange_subset_pos hs)
  have hmem : s ∈ Icc (0 : ℝ) (63/20) := ⟨hs0, hstop⟩
  have htop : (63/20 : ℝ) ∈ Icc (0 : ℝ) (63/20) := by constructor <;> norm_num
  refine ⟨(e8RegularQ_mono_of_mem hs endpoint_mem hstop).trans endpoint_jets_tight.1, ?_, ?_⟩
  · exact (E8RatioMonotonicity.e8LargeSStructureCertified.derivative_mono
      _ endpoint_mem hmem htop hstop).trans endpoint_jets_tight.2.1
  · exact (second_monotone endpoint_mem hmem htop hstop).trans endpoint_jets_tight.2.2

#print axioms endpoint_jets_tight
#print axioms bounded_argument_jets_tight

end GeneralCK.E8LargeTSAxis

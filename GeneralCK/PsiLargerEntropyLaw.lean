import GeneralCK.PsiLargerEntropyRedesign
import GeneralCK.PsiParentDominance

/-!
# The larger retained-child estimate for actual finite laws

This transfers the analytic margin through the true hybrid child maximum.
The small-bias active-parent condition supplies the factor-eight entropy bound.
The endpoint expression remains a comparison target until the separate cost
supporting-plane theorem is applied.
-/

namespace GeneralCK.PsiLargerEntropyLaw
open PsiChildEntropyCoupling PsiSignedSplit

/-- The margin now applies to the actual hybrid Bellman gap. Child maxima
are retained by the branch comparison, not assumed to choose either branch. -/
theorem canonical_hybrid_gap_margin {d q E t : ℝ}
    (hE : 0 < E) (hEi : E ≤ 1 / 80)
    (hd : 8 * E ≤ d) (hd1 : d ≤ 1)
    (hq : 0 ≤ q) (hqE : q ≤ 8 * E) (ht : |t| < 1)
    (hactive : phi ((1 - q) / 2) E ≤ psi ((1 - q) / 2) E) :
    candidateGap B ((1 - d - q) / 2) ((1 + d - q) / 2)
      (E * (1 + t)) (E * (1 - t)) + (9 / 100) * (q ^ 2 / E) ≤
      F d E + d / (2 * Real.log 2) * barrier t := by
  have h := PsiLargerEntropyRedesign.retained_child_margin hE hEi hd hd1 hq hqE ht
  have hb := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (t := t) hq (hqE.trans hd) hactive
  linarith

/-- The same result in original means and child entropies, with the chart
identities and signed split derived rather than assumed. -/
theorem opposite_hybrid_gap_margin {a b e f : ℝ}
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hsum : a + b ≤ 1)
    (he : 0 < e) (hf : 0 < f) (hEi : (e + f) / 2 ≤ 1 / 80)
    (hd : 8 * ((e + f) / 2) ≤ b - a)
    (hqE : 1 - a - b ≤ 8 * ((e + f) / 2))
    (hactive : phi ((a + b) / 2) ((e + f) / 2) ≤
      psi ((a + b) / 2) ((e + f) / 2)) :
    candidateGap B a b e f + (9 / 100) * ((1 - a - b) ^ 2 / ((e + f) / 2)) ≤
      F (b - a) ((e + f) / 2) + (b - a) / (2 * Real.log 2) *
        barrier ((e - f) / (e + f)) := by
  have hmean : (1 - (1 - a - b)) / 2 = (a + b) / 2 := by ring
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split he hf
  have h := canonical_hybrid_gap_margin
    (d := b - a) (q := 1 - a - b) (E := (e + f) / 2)
    (t := (e - f) / (e + f)) (by linarith) hEi hd (by linarith)
    (by linarith) hqE ht (by rwa [hmean])
  have hca : (1 - (b - a) - (1 - a - b)) / 2 = a := by ring
  have hcb : (1 + (b - a) - (1 - a - b)) / 2 = b := by ring
  rwa [hca, hcb, hce, hcf] at h

/-- A theorem for actual finite laws, still comparing with the explicit
endpoint expression. This is unconditional on any endpoint supporting plane. -/
theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqE : 1 - μ.a - μ.b ≤ 8 * μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤
      F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
        barrier ((μ.e - μ.f) / (μ.e + μ.f)) :=
  opposite_hybrid_gap_margin μ.a_interior.1.le μ.b_interior.2.le hsum
    μ.e_pos μ.f_pos hEi hd hqE hactive


/-- Even a weakly active psi parent has bias strictly below `8E` in the
small-bias region. No separate positivity assumption on the bias is needed. -/
theorem active_bias_lt_eight_entropy {m E : ℝ} (hE : 0 < E)
    (hqsmall : 1 - 2 * m ≤ 1 / 10)
    (hactive : phi m E ≤ psi m E) : 1 - 2 * m < 8 * E := by
  by_contra hn
  have hratio : 8 * E ≤ 1 - 2 * m := le_of_not_gt hn
  have hq : 0 < 1 - 2 * m := by linarith
  have hp := PsiParentDominance.parent_dominance_ratio8_small_bias_of_mean
    hE hq hqsmall hratio
  exact (not_lt_of_ge hactive) hp

/-- Active-parent version for a finite law. The bound `q≤8E` is discharged
analytically from `q≤1/10`; the child maxima are still retained. -/
theorem law_gap_margin_of_active {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤
      F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
        barrier ((μ.e - μ.f) / (μ.e + μ.f)) := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hqeq : 1 - 2 * μ.midpoint = 1 - μ.a - μ.b := by
    unfold InteriorLaw.midpoint
    ring
  have hqE := active_bias_lt_eight_entropy hE (by rwa [hqeq]) hactive
  rw [hqeq] at hqE
  exact law_gap_margin μ hsum hEi hd hqE.le hactive

/-- The same actual-law estimate written as an upper bound with an explicit
subtracted margin. It is strict relative to the endpoint expression when
the parent bias is nonzero. -/
theorem law_gap_le_endpoint_sub_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
      barrier ((μ.e - μ.f) / (μ.e + μ.f)) -
        (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by
  have h := law_gap_margin_of_active μ hsum hEi hd hqsmall hactive
  linarith only [h]

end GeneralCK.PsiLargerEntropyLaw

#print axioms GeneralCK.PsiLargerEntropyLaw.law_gap_margin
#print axioms GeneralCK.PsiLargerEntropyLaw.active_bias_lt_eight_entropy
#print axioms GeneralCK.PsiLargerEntropyLaw.law_gap_margin_of_active
#print axioms GeneralCK.PsiLargerEntropyLaw.law_gap_le_endpoint_sub_margin

import GeneralCK.Certificates.ReflectionContactJet
import GeneralCK.Certificates.Jet2Bounds

namespace GeneralCK.Certificates.ReflectionContactBounds
open JetBounds
open GeneralCK.Reflection
open GeneralCK.Certificates.Reflection

theorem first_eq {y : ℝ} (_hy : 0 < y) :
    reflectionContactJet.first y = -(biasContact y)^2/biasB (biasContact y) := by
  simp only [reflectionContactJet,biasRprime,neg_div,inv_neg,inv_div]

/-- Inverse-ratio second derivative expressed using positive denominators only. -/
theorem second_eq {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.second y =
      2*(biasContact y)^3/(biasB (biasContact y))^2 -
      (biasContact y)^5/((1-(biasContact y)^2)*(biasB (biasContact y))^3) := by
  have hc := biasContact_mem hy
  have hb := (biasB_pos hc.1 hc.2).ne'
  have hg : 1-(biasContact y)^2 ≠ 0 := by nlinarith [hc.1,hc.2]
  simp only [reflectionContactJet,biasRsecond,biasRprime]
  field_simp [hc.1.ne',hb,hg]

/-- Arithmetic enclosure of the contact jet; soundness checks both reciprocal domains. -/
noncomputable def enclosure (c B : Interval) : JetEnclosure :=
  let r := B.inv
  let gap := (Interval.point 1).sub c.sq
  ⟨c,(c.sq.mul r).neg,
    (((Interval.point 2).mul c.cube).mul r.sq).sub
      (((c.cube.mul c.sq).mul gap.inv).mul r.cube)⟩

theorem contains {c B : Interval} {y : ℝ} (hy : 0 < y)
    (hc : c.Contains (biasContact y)) (hB : B.Contains (biasB (biasContact y)))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    (enclosure c B).Contains reflectionContactJet y := by
  have hr := hB.inv hBp
  have hg := ((Interval.contains_point 1).sub hc.sq).inv hgap
  refine ⟨hc,?_,?_⟩
  · rw [first_eq hy]
    simpa only [enclosure,div_eq_mul_inv,neg_mul] using (hc.sq.mul hr).neg
  · rw [second_eq hy]
    have h := (((Interval.contains_point 2).mul hc.cube).mul hr.sq).sub
      (((hc.cube.mul hc.sq).mul hg).mul hr.cube)
    have he (x b : ℝ) : 2*x^3/b^2-x^5/((1-x^2)*b^3) =
        2*x^3*(b⁻¹)^2-x^3*x^2*(1-x^2)⁻¹*(b⁻¹)^3 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
      ring
    rw [he]
    exact h

/-- Produce a contact bracket from entropy inequalities at its rational endpoints. -/
theorem contact_contains {c Y : Interval} {y : ℝ} (hy : Y.Contains y)
    (hY : 0 < Y.lo) (hc0 : 0 ≤ c.lo) (hc1 : c.hi ≤ 1) (horder : c.lo ≤ c.hi)
    (hl : Y.hi*c.lo ≤ biasE c.lo) (hu : biasE c.hi ≤ Y.lo*c.hi) :
    c.Contains (biasContact y) := by
  have hyp : 0 < y := hY.trans_le hy.1
  have hcm := biasContact_mem hyp
  have heq : biasE (biasContact y) = y*biasContact y := by
    have h := biasR_biasContact hyp
    exact (div_eq_iff hcm.1.ne').mp h
  exact contact_bracket hcm.1.le hcm.2.le hc0 hc1 horder hyp heq
    ((mul_le_mul_of_nonneg_right hy.2 hc0).trans hl)
    (hu.trans (mul_le_mul_of_nonneg_right hy.1 (hc0.trans horder)))

/-- Enclosure propagation through contact composition, without assumptions about derivatives. -/
theorem contains_comp {c B : Interval} {input : JetEnclosure} {j : Jet2} {t : ℝ}
    (hj : input.Contains j t) (hy : 0 < j.value t)
    (hc : c.Contains (biasContact (j.value t)))
    (hB : B.Contains (biasB (biasContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c B).comp input).Contains (reflectionContactJet.comp j) t :=
  (contains hy hc hB hBp hgap).comp hj

theorem containsOn_comp {c B : Interval} {input : JetEnclosure} {j : Jet2} {s : Set ℝ}
    (hj : input.ContainsOn j s) (hy : ∀ t ∈ s, 0 < j.value t)
    (hc : ∀ t ∈ s, c.Contains (biasContact (j.value t)))
    (hB : ∀ t ∈ s, B.Contains (biasB (biasContact (j.value t))))
    (hBp : 0 < B.lo) (hgap : 0 < ((Interval.point 1).sub c.sq).lo) :
    ((enclosure c B).comp input).ContainsOn (reflectionContactJet.comp j) s :=
  fun t ht => contains_comp (hj t ht) (hy t ht) (hc t ht) (hB t ht) hBp hgap

end GeneralCK.Certificates.ReflectionContactBounds

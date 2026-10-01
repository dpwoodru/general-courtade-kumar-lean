import GeneralCK.Certificates.E8LowOrderThetaCoefficients

/-! Normalized Taylor coefficient identities used by the low-order E8 germs. -/

namespace GeneralCK.Certificates.E8NormalizedCoeff5

open E8AnalyticGerm E8AnalyticInverseRecurrence

noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

@[simp] theorem coeff_zero (f : ℂ → ℂ) : coeff f 0 = f 0 := by
  simp [coeff, iteratedDeriv_zero]

theorem coeff_sub (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (f - g) n = coeff f n - coeff g n := by
  rw [coeff, iteratedDeriv_sub hf.contDiffAt hg.contDiffAt]
  simp only [Pi.sub_apply, coeff]
  ring

theorem coeff_add (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (f + g) n = coeff f n + coeff g n := by
  rw [coeff, iteratedDeriv_add hf.contDiffAt hg.contDiffAt]
  simp only [coeff]
  ring

theorem coeff_div_const (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coeff (fun z => f z / c) n = coeff f n / c := by
  simp [coeff, iteratedDeriv_div_const]
  ring

theorem coeff_const_mul (c : ℂ) (f : ℂ → ℂ) (n : ℕ) :
    coeff (fun z => c * f z) n = c * coeff f n := by
  simp [coeff, iteratedDeriv_const_mul_field]
  ring

theorem coeff_const_sub (c : ℂ) (f : ℂ → ℂ) (n : ℕ) (hn : 0 < n) :
    coeff (fun z => c - f z) n = -coeff f n := by
  rw [coeff, iteratedDeriv_const_sub hn c, iteratedDeriv_neg]
  simp [coeff]
  ring

theorem coeff_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds (0 : ℂ)] g) (n : ℕ) :
    coeff f n = coeff g n := by
  unfold coeff
  rw [h.iteratedDeriv_eq n]

theorem coeff_odd_zero_of_even {f : ℂ → ℂ} (hneg : ∀ z, f (-z) = -f z)
    {n : ℕ} (hn : Even n) : coeff f n = 0 := by
  have heq : (fun z : ℂ => f (-z)) =ᶠ[nhds 0] (fun z : ℂ => -f z) :=
    Filter.Eventually.of_forall hneg
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold coeff
  have hz : iteratedDeriv n f 0 = 0 := by linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

theorem coeff_even_zero_of_odd {f : ℂ → ℂ} (hneg : ∀ z, f (-z) = f z)
    {n : ℕ} (hn : Odd n) : coeff f n = 0 := by
  have heq : (fun z : ℂ => f (-z)) =ᶠ[nhds 0] f := Filter.Eventually.of_forall hneg
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg] at hd
  simp only [neg_zero, Odd.neg_one_pow hn, neg_smul, one_smul] at hd
  unfold coeff
  have hz : iteratedDeriv n f 0 = 0 := by linear_combination (-1 / 2 : ℂ) * hd
  simp [hz]

theorem coeff_mul_three (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 3 = coeff f 0 * coeff g 3 + coeff f 1 * coeff g 2 +
      coeff f 2 * coeff g 1 + coeff f 3 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

theorem coeff_mul_one (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 1 = coeff f 0 * coeff g 1 + coeff f 1 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]

theorem coeff_mul_two (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 2 = coeff f 0 * coeff g 2 + coeff f 1 * coeff g 1 +
      coeff f 2 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

theorem coeff_mul_four (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 4 = coeff f 0 * coeff g 4 + coeff f 1 * coeff g 3 +
      coeff f 2 * coeff g 2 + coeff f 3 * coeff g 1 + coeff f 4 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

theorem coeff_mul_five (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 5 = coeff f 0 * coeff g 5 + coeff f 1 * coeff g 4 +
      coeff f 2 * coeff g 3 + coeff f 3 * coeff g 2 +
      coeff f 4 * coeff g 1 + coeff f 5 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

/-- Analytic composition agrees with the executable ordinary coefficient convolution. -/
theorem coeff_comp (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0) (n : ℕ) :
    coeff (f ∘ g) n = composeCoeff (coeff f) (coeff g) n := by
  have hf' : AnalyticAt ℂ f (g 0) := by simpa [hg0] using hf
  have hcomp := hf'.hasFPowerSeriesAt.comp hg.hasFPowerSeriesAt
  have hcanon := (hf.comp_of_eq hg hg0).hasFPowerSeriesAt
  have hs := hcomp.eq_formalMultilinearSeries hcanon
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs
  rw [hg0] at hc
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_one] at hc
  change formalComposeCoeff (coeff f) (coeff g) n = coeff (f ∘ g) n at hc
  rw [composeCoeff_eq_formalComposeCoeff (coeff f) (coeff g) (by simp [coeff, hg0])]
  exact hc.symm

end GeneralCK.Certificates.E8NormalizedCoeff5

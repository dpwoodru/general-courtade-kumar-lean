import GeneralCK.Certificates.E8ElementaryCoeff5

/-! Normalized product identities at the two additional orders needed for q7. -/

namespace GeneralCK.Certificates.E8NormalizedCoeff7

open E8AnalyticGerm E8NormalizedCoeff5

/-- Normalized Taylor coefficients turn analytic products into finite Cauchy
convolutions.  This is the reusable product rule for all higher orders. -/
theorem coeff_mul (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (f * g) n =
      ∑ i ∈ Finset.range (n + 1), coeff f i * coeff g (n - i) := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
  rw [coeff, coeff, Nat.cast_choose ℂ hin]
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni0 : ((n-i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n-i)
  have hn0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hi0, hni0, hn0]

theorem coeff_mul_six (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 6 = coeff f 0 * coeff g 6 + coeff f 1 * coeff g 5 +
      coeff f 2 * coeff g 4 + coeff f 3 * coeff g 3 +
      coeff f 4 * coeff g 2 + coeff f 5 * coeff g 1 + coeff f 6 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

theorem coeff_mul_seven (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    coeff (f * g) 7 = coeff f 0 * coeff g 7 + coeff f 1 * coeff g 6 +
      coeff f 2 * coeff g 5 + coeff f 3 * coeff g 4 +
      coeff f 4 * coeff g 3 + coeff f 5 * coeff g 2 +
      coeff f 6 * coeff g 1 + coeff f 7 * coeff g 0 := by
  rw [coeff, iteratedDeriv_mul hf.contDiffAt hg.contDiffAt]
  simp [Finset.sum_range_succ, coeff]
  norm_num [Nat.choose]
  ring

end GeneralCK.Certificates.E8NormalizedCoeff7

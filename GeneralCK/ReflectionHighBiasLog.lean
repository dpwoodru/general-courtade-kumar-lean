import GeneralCK.SmallMeanAnalytic
import GeneralCK.Certificates.SmallMeanCertificate

namespace GeneralCK.Reflection.HighBiasLog
open SmallMean

theorem log_two_thousand_lt : Real.log 2000 < (8:ℝ) := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ)<2000)
    (by norm_num : (2000:ℝ)<2^11)
  rw [Real.log_pow] at h
  have hl := Certificates.SmallMean.fixed_log_two_lt
  norm_num at h
  linarith

/-- A tangent bound for the logarithm controls the entire punctured interval. -/
theorem mul_log_small {r : ℝ} (hr : 0<r) (hu : r≤1/1000) :
    r*Real.log (2/r)<1/125 := by
  have hy : 0<(1/1000:ℝ)/r := div_pos (by norm_num) hr
  have he : (2:ℝ)/r=2000*((1/1000)/r) := by ring
  have hlog : Real.log (2/r)=Real.log 2000+Real.log ((1/1000)/r) := by
    rw [he,Real.log_mul (by norm_num) hy.ne']
  have ht := Real.log_le_sub_one_of_pos hy
  have hl := log_two_thousand_lt
  have hm : r*Real.log (2/r)<r*(7+(1/1000)/r) := by
    apply mul_lt_mul_of_pos_left _ hr
    rw [hlog]
    linarith
  have heq : r*(7+(1/1000:ℝ)/r)=7*r+1/1000 := by
    field_simp
  rw [heq] at hm
  linarith

theorem A_nonneg {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) : 0≤A a := by
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  apply (le_div_iff₀ (sub_pos.mpr ha1)).mpr
  linarith

theorem small_ratio_log_bound {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    (1-a)*A a≤1/250 := by
  have hr : 0<1-a := sub_pos.mpr ha1
  have hup : 1-a≤(1/1000:ℝ) := by linarith
  have hratio : (1+a)/(1-a)≤2/(1-a) :=
    div_le_div_of_nonneg_right (by linarith) hr.le
  have hpos : 0<(1+a)/(1-a) := div_pos (by linarith) hr
  have hlog := Real.log_le_log hpos hratio
  have hm := mul_le_mul_of_nonneg_left hlog hr.le
  have hu := mul_log_small hr hup
  dsimp [A]
  nlinarith

theorem weighted_bounds {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    (1-a)^2*(A a)^2≤16/1000000 ∧
    (1-a)^2*A a≤4/1000000 ∧
    (1-a)^2≤1/1000000 ∧
    (1-a)^2/(1-a^2)≤1/1000 := by
  have hr : 0<1-a := sub_pos.mpr ha1
  have hu : 1-a≤(1/1000:ℝ) := by linarith
  have hA := A_nonneg ha ha1
  have hbound := small_ratio_log_bound ha ha1
  have hsquare := (sq_le_sq₀ (mul_nonneg hr.le hA) (by norm_num : (0:ℝ)≤1/250)).mpr hbound
  have hprod := mul_le_mul hu hbound (mul_nonneg hr.le hA) (by norm_num : (0:ℝ)≤1/1000)
  have hr2 : (1-a)^2≤1/1000000 := by nlinarith
  have hgap : 0<1-a^2 := by nlinarith
  refine ⟨by nlinarith,by nlinarith,hr2,?_⟩
  apply (div_le_iff₀ hgap).mpr
  have hrr : (1-a)^2≤(1/1000:ℝ)*(1-a) := by nlinarith
  have ha0 : 0≤a := by linarith
  nlinarith [mul_nonneg hr.le ha0]

noncomputable def coefficientBound (a : ℝ) : ℝ :=
  6000*(A a)^2+8000*A a+3000+210/(1-a^2)

theorem scaled_coefficient_bound {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    (1-a)^2*coefficientBound a≤341/1000 := by
  obtain ⟨h1,h2,h3,h4⟩ := weighted_bounds ha ha1
  have he : (1-a)^2*coefficientBound a =
      6000*((1-a)^2*(A a)^2)+8000*((1-a)^2*A a)+3000*(1-a)^2+
        210*((1-a)^2/(1-a^2)) := by
    dsimp [coefficientBound]
    ring
  rw [he]
  linarith

theorem scaled_base_lower {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    (999/2000:ℝ)≤(1-a)^2*(2*a/(1-a^2)^2) := by
  have hr : 1-a≠0 := (sub_pos.mpr ha1).ne'
  have hp : 0<1+a := by linarith
  have he : (1-a)^2*(2*a/(1-a^2)^2)=2*a/(1+a)^2 := by
    rw [show 1-a^2=(1-a)*(1+a) by ring,mul_pow]
    field_simp
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
  have hs : (1+a)^2≤4 := by nlinarith
  nlinarith

theorem coefficient_domination {a : ℝ} (ha : (999/1000:ℝ)≤a) (ha1 : a<1) :
    6000*(A a)^2+8000*A a+3000+210/(1-a^2)<2*a/(1-a^2)^2 := by
  have hu := scaled_coefficient_bound ha ha1
  have hl := scaled_base_lower ha ha1
  have hr : 0<(1-a)^2 := sq_pos_of_pos (sub_pos.mpr ha1)
  apply (mul_lt_mul_iff_left₀ hr).mp
  dsimp [coefficientBound] at hu
  nlinarith

end GeneralCK.Reflection.HighBiasLog

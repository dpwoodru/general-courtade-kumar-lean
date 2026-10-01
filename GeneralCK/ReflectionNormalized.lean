import GeneralCK.Certificates.ReflectionExpressionJet

namespace GeneralCK.Reflection
open Certificates.Reflection Certificates.Mixed

private theorem normalized_biasE_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasE (1-2*v) = hn v := by
  rw [biasE_eq_log_mul_E (by linarith) (by linarith),hn_eq_H_mul_log]
  unfold E
  rw [show (1-(1-2*v))/2=v by ring]
  ring

private theorem normalized_biasB_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasB (1-2*v) = kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  unfold biasB kap
  rw [show 1-(1-2*v)*(1-2*v)=2^2*(v*(1-v)) by ring,
    Real.log_mul (by norm_num : (2:ℝ)^2 ≠ 0) hp.ne',Real.log_pow]
  ring

theorem normalized_biasS_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) (a e : ℝ) :
    biasS (1-2*v) a (Real.log 2*e) =
      reflectionS v e (SmallMean.A a) (1/(1-a^2)) := by
  unfold biasS
  rw [normalized_biasE_probability hv hv',normalized_biasB_probability hv hv']
  unfold reflectionS SmallMean.A
  rw [show 1-(1-2*v)*(1-2*v)=4*v*(1-v) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev,pow_two]
  ring

/-- The natural-ratio bias contact is the bias of the bit-entropy radial contact. -/
theorem biasContact_scaled_ratio {s : ℝ} (hs : s ≠ 0) (e : ℝ) :
    biasContact (Real.log 2*e/s) = 1-2*radialContact s e := by
  unfold biasContact
  rw [radialContact_normalize_radius hs e]
  congr 2
  field_simp

/-- Exact normalization and entropy-unit conversion, independent of certificates. -/
theorem normalizedValue_eq_curvature {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1) :
    Certificates.ReflectionExpression.normalizedValue a z = curvature a (a*z)/(a^4*z) := by
  have hb : 0 < a*z := mul_pos ha hz
  have hba : a*z < a := by nlinarith
  have hb' : a*z < 1 := hba.trans ha'
  have he : 0 < meanEntropy a (a*z) :=
    meanEntropy_pos (by linarith) ha' (by linarith) hb'
  have hm : 0 < (a-a*z)/2 := by linarith
  have hp : 0 < (a+a*z)/2 := by linarith
  have hE : (biasE a+biasE (a*z))/2 = Real.log 2*meanEntropy a (a*z) := by
    rw [biasE_eq_log_mul_E (by linarith) ha',biasE_eq_log_mul_E (by linarith) hb']
    unfold meanEntropy
    ring
  have hvm := radialContact_pos hm he
  have hvm' : radialContact ((a-a*z)/2) (meanEntropy a (a*z)) < 1 :=
    (radialContact_lt_half hm he).trans (by norm_num)
  have hvp := radialContact_pos hp he
  have hvp' : radialContact ((a+a*z)/2) (meanEntropy a (a*z)) < 1 :=
    (radialContact_lt_half hp he).trans (by norm_num)
  unfold Certificates.ReflectionExpression.normalizedValue
  dsimp only
  rw [hE,show a*(1-z)/2=(a-a*z)/2 by ring,show a*(1+z)/2=(a+a*z)/2 by ring,
    biasContact_scaled_ratio hm.ne',biasContact_scaled_ratio hp.ne',
    normalized_biasS_probability hvm hvm',normalized_biasS_probability hvp hvp']
  unfold curvature
  rw [show a^3*(a*z)=a^4*z by ring]
  congr 1
  ring

theorem curvature_pos_of_normalizedValue_pos {a z : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hz : 0 < z) (hz' : z < 1)
    (hpos : 0 < Certificates.ReflectionExpression.normalizedValue a z) :
    0 < curvature a (a*z) := by
  rw [normalizedValue_eq_curvature ha ha' hz hz'] at hpos
  exact (div_pos_iff_of_pos_right (mul_pos (pow_pos ha 4) hz)).mp hpos

end GeneralCK.Reflection

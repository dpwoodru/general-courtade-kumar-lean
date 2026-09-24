import GeneralCK.ReflectionSmallBiasCandidate
import GeneralCK.ReflectionSmallBiasPolynomialCertificate

/-! The factored candidate expressed in the sparse Laurent-polynomial verifier. -/

namespace GeneralCK.Reflection.SmallBiasCandidateSparse

open SmallBiasPolynomial SmallBiasCoefficientBounds

def liftCoefficient (i j : ℕ) : List PowerTerm → List Term
  | [] => []
  | t :: ts => ⟨2*i,2*j,-(t.n:ℤ),t.c⟩ :: liftCoefficient i j ts

def rawQuotient : List CoefficientRow → List Term
  | [] => []
  | r :: rs => liftCoefficient r.i r.j r.coefficients ++ rawQuotient rs

def factor : List Term := [⟨5,1,0,1⟩,⟨3,3,0,-2⟩,⟨1,5,0,1⟩]

def rawCandidate : List Term := rawMul factor (rawQuotient SmallBiasCoefficientData.rows)

theorem eval_liftCoefficient (k : ℂ) (i j : ℕ) (ts : List PowerTerm) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval k (liftCoefficient i j ts) z =
      SmallBiasCoefficientBounds.eval ts k⁻¹*z.1^(2*i)*z.2^(2*j) := by
  induction ts with
  | nil => simp [liftCoefficient,SmallBiasPolynomial.eval,SmallBiasCoefficientBounds.eval]
  | cons t ts ih =>
    simp only [liftCoefficient,SmallBiasPolynomial.eval,evalTerm,SmallBiasCoefficientBounds.eval,
      zpow_neg,zpow_natCast,inv_pow,ih]
    ring

theorem eval_rawQuotient (rs : List CoefficientRow) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval (Real.log 2:ℂ) (rawQuotient rs) z =
      SmallBiasCandidate.quotient rs z := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hc : SmallBiasCoefficientBounds.eval r.coefficients (Real.log 2:ℂ)⁻¹ =
        (SmallBiasCandidate.coefficient r:ℂ) := by
      unfold SmallBiasCandidate.coefficient
      rw [← Complex.ofReal_inv]
      exact SmallBiasCoefficientBounds.eval_complex_ofReal r.coefficients ((Real.log 2)⁻¹)
    rw [rawQuotient,eval_append,eval_liftCoefficient,hc,ih]
    rfl

theorem eval_factor (k : ℂ) (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval k factor z = z.1*z.2*(z.1^2-z.2^2)^2 := by
  norm_num [factor,SmallBiasPolynomial.eval,evalTerm]
  <;> ring

theorem eval_rawCandidate (z : ℂ × ℂ) :
    SmallBiasPolynomial.eval (Real.log 2:ℂ) rawCandidate z = SmallBiasCandidate.polynomial z := by
  have hk : (Real.log 2:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [rawCandidate,eval_rawMul hk,eval_factor,eval_rawQuotient]
  rfl

end GeneralCK.Reflection.SmallBiasCandidateSparse


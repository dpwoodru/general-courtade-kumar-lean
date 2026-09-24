import GeneralCK.ReflectionSmallBiasPolynomial

/-! # Exact equality certificates for the reflection polynomial arithmetic -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def equalityCheck (p q : List Term) : Bool := decide (normalize (p ++ scale (-1) q) = [])

theorem equalityCheck_sound {p q : List Term} (h : equalityCheck p q = true)
    (k : ℂ) (z : ℂ × ℂ) : eval k p z = eval k q z := by
  have hh : normalize (p ++ scale (-1) q) = [] := by
    simpa only [equalityCheck, decide_eq_true_eq] using h
  have he := congrArg (fun ts => eval k ts z) hh
  rw [eval_normalize, eval_append, eval_scale] at he
  simpa only [eval, Rat.cast_neg, Rat.cast_one, neg_one_mul, ← sub_eq_add_neg,
    sub_eq_zero] using he

end GeneralCK.Reflection.SmallBiasPolynomial

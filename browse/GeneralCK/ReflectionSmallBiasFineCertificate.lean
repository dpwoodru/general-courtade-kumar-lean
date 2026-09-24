import GeneralCK.ReflectionSmallBiasExponentCertificate

/-! Exact finite coverage by first exponent and entropy-exponent parity. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def fineDegree (t : Term) : ℕ := 2*t.a + t.k.natAbs % 2

def finePart (d : ℕ) (p : List Term) : List Term := p.filter (fun t => fineDegree t=d)

def fineBound (n : ℕ) (p : List Term) : Bool := p.all (fun t => decide (fineDegree t<n))

theorem fineBound_sound {n : ℕ} {p : List Term} (h : fineBound n p = true) :
    ∀ t ∈ p, fineDegree t<n := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem eval_finePart_cons (d : ℕ) (k : ℂ) (t : Term) (ts : List Term) (z : ℂ × ℂ) :
    eval k (finePart d (t::ts)) z =
      (if fineDegree t=d then evalTerm k t z else 0)+eval k (finePart d ts) z := by
  by_cases h : fineDegree t=d
  · simp [finePart,eval,h]
  · simp [finePart,eval,h]

theorem sum_eval_fineParts (n : ℕ) (k : ℂ) (p : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, fineDegree t<n) :
    (∑ d ∈ Finset.range n, eval k (finePart d p) z) = eval k p z := by
  induction p with
  | nil => simp [finePart,eval]
  | cons t ts ih =>
    have ht := hp t (by simp)
    have hts := ih (fun r hr => hp r (by simp [hr]))
    simp_rw [eval_finePart_cons]
    rw [Finset.sum_add_distrib,hts]
    simp [eval,ht]

theorem eval_eq_of_fineParts (n : ℕ) (k : ℂ) (p q : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, fineDegree t<n) (hq : ∀ t ∈ q, fineDegree t<n)
    (he : ∀ d<n, equalityCheck (finePart d p) (finePart d q) = true) :
    eval k p z = eval k q z := by
  rw [← sum_eval_fineParts n k p z hp,← sum_eval_fineParts n k q z hq]
  apply Finset.sum_congr rfl
  intro d hd
  exact equalityCheck_sound (he d (Finset.mem_range.mp hd)) k z

end GeneralCK.Reflection.SmallBiasPolynomial


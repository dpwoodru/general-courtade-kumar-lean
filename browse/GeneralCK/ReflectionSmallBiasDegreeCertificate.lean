import GeneralCK.ReflectionSmallBiasPolynomialCertificate

/-! Degree-wise exact checks keep polynomial certificates within a fixed memory budget. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def degreePart (d : ℕ) (p : List Term) : List Term := p.filter (fun t => t.a+t.b=d)

def degreeBound (n : ℕ) (p : List Term) : Bool := p.all (fun t => decide (t.a+t.b<n))

theorem degreeBound_sound {n : ℕ} {p : List Term} (h : degreeBound n p = true) :
    ∀ t ∈ p, t.a+t.b<n := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem eval_degreePart_cons (d : ℕ) (k : ℂ) (t : Term) (ts : List Term) (z : ℂ × ℂ) :
    eval k (degreePart d (t::ts)) z =
      (if t.a+t.b=d then evalTerm k t z else 0)+eval k (degreePart d ts) z := by
  by_cases h : t.a+t.b=d
  · simp [degreePart,eval,h]
  · simp [degreePart,eval,h]

theorem sum_eval_degreeParts (n : ℕ) (k : ℂ) (p : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a+t.b<n) :
    (∑ d ∈ Finset.range n, eval k (degreePart d p) z) = eval k p z := by
  induction p with
  | nil => simp [degreePart,eval]
  | cons t ts ih =>
    have ht := hp t (by simp)
    have hts := ih (fun r hr => hp r (by simp [hr]))
    simp_rw [eval_degreePart_cons]
    rw [Finset.sum_add_distrib,hts]
    simp [eval,ht]

theorem eval_eq_of_degrees (n : ℕ) (k : ℂ) (p q : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a+t.b<n) (hq : ∀ t ∈ q, t.a+t.b<n)
    (he : ∀ d<n, equalityCheck (degreePart d p) (degreePart d q) = true) :
    eval k p z = eval k q z := by
  rw [← sum_eval_degreeParts n k p z hp,← sum_eval_degreeParts n k q z hq]
  apply Finset.sum_congr rfl
  intro d hd
  exact equalityCheck_sound (he d (Finset.mem_range.mp hd)) k z

end GeneralCK.Reflection.SmallBiasPolynomial


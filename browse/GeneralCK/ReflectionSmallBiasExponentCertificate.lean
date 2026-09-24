import GeneralCK.ReflectionSmallBiasDegreeCertificate

/-! Exact checks by the first variable's exponent reduce the largest certificate bucket. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def aPart (d : ℕ) (p : List Term) : List Term := p.filter (fun t => t.a=d)

def aBound (n : ℕ) (p : List Term) : Bool := p.all (fun t => decide (t.a<n))

theorem aBound_sound {n : ℕ} {p : List Term} (h : aBound n p = true) :
    ∀ t ∈ p, t.a<n := by
  intro t ht
  exact of_decide_eq_true (List.all_eq_true.mp h t ht)

theorem eval_aPart_cons (d : ℕ) (k : ℂ) (t : Term) (ts : List Term) (z : ℂ × ℂ) :
    eval k (aPart d (t::ts)) z =
      (if t.a=d then evalTerm k t z else 0)+eval k (aPart d ts) z := by
  by_cases h : t.a=d
  · simp [aPart,eval,h]
  · simp [aPart,eval,h]

theorem sum_eval_aParts (n : ℕ) (k : ℂ) (p : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a<n) :
    (∑ d ∈ Finset.range n, eval k (aPart d p) z) = eval k p z := by
  induction p with
  | nil => simp [aPart,eval]
  | cons t ts ih =>
    have ht := hp t (by simp)
    have hts := ih (fun r hr => hp r (by simp [hr]))
    simp_rw [eval_aPart_cons]
    rw [Finset.sum_add_distrib,hts]
    simp [eval,ht]

theorem eval_eq_of_aParts (n : ℕ) (k : ℂ) (p q : List Term) (z : ℂ × ℂ)
    (hp : ∀ t ∈ p, t.a<n) (hq : ∀ t ∈ q, t.a<n)
    (he : ∀ d<n, equalityCheck (aPart d p) (aPart d q) = true) :
    eval k p z = eval k q z := by
  rw [← sum_eval_aParts n k p z hp,← sum_eval_aParts n k q z hq]
  apply Finset.sum_congr rfl
  intro d hd
  exact equalityCheck_sound (he d (Finset.mem_range.mp hd)) k z

end GeneralCK.Reflection.SmallBiasPolynomial


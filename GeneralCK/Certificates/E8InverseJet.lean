import GeneralCK.PureGapE8InverseDerivatives

/-!
# Exact finite inverse-jet checker for E8

Taylor coefficients are factorial-normalized.  Inverse differentiation is
therefore equivalent to checking that the finite composition coefficients of
`theta(q(x))` agree with `x`.  This rational kernel is executable at order 5
and order 17 without invoking native code.
-/

namespace GeneralCK.Certificates.E8InverseJet

def powCoeff (q : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      ∑ i ∈ Finset.range (n + 1), q i * powCoeff q k (n - i)

def composeCoeff (theta q : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), theta k * powCoeff q k n

def targetCoeff (k : ℕ) : ℚ := if k = 1 then 1 else 0

def coeffMatches (theta q : ℕ → ℚ) (k : ℕ) : Bool :=
  decide (composeCoeff theta q k = targetCoeff k)

def inverseJetCheck (order : ℕ) (theta q : ℕ → ℚ) : Bool :=
  (List.range (order + 1)).all (coeffMatches theta q)

/-- Acceptance exposes every checked composition coefficient. -/
theorem inverseJetCheck_sound {order : ℕ} {theta q : ℕ → ℚ}
    (h : inverseJetCheck order theta q = true) {k : ℕ} (hk : k ≤ order) :
    composeCoeff theta q k = targetCoeff k := by
  have hall := List.all_eq_true.mp h
  have hm : k ∈ List.range (order + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hk)
  have := hall k hm
  simpa [coeffMatches, decide_eq_true_eq] using this

/-- Order-five specialization for the line-anchor jet. -/
theorem orderFiveCheck_sound {theta q : ℕ → ℚ}
    (h : inverseJetCheck 5 theta q = true) {k : ℕ} (hk : k ≤ 5) :
    composeCoeff theta q k = targetCoeff k :=
  inverseJetCheck_sound h hk

/-- The same checked kernel scales directly to the origin proof's order 17. -/
theorem orderSeventeenCheck_sound {theta q : ℕ → ℚ}
    (h : inverseJetCheck 17 theta q = true) {k : ℕ} (hk : k ≤ 17) :
    composeCoeff theta q k = targetCoeff k :=
  inverseJetCheck_sound h hk

end GeneralCK.Certificates.E8InverseJet

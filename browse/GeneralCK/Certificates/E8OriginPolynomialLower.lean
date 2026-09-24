import GeneralCK.Certificates.E8OriginRealTaylorTransfer

/-! Generic exact-rational lower bounds for bivariate polynomials on a simplex. -/

namespace GeneralCK.Certificates.E8OriginPolynomialLower

structure Term where
  i : Nat
  j : Nat
  c : Rat
  deriving DecidableEq

noncomputable def evalTerm (p : Term) (s t : Real) : Real :=
  (p.c : Real) * s ^ p.i * t ^ p.j

noncomputable def evalTerms : List Term -> Real -> Real -> Real
  | [], _, _ => 0
  | p :: ps, s, t => evalTerm p s t + evalTerms ps s t

noncomputable def negAggregate (R : Real) : List Term -> Real
  | [] => 0
  | p :: ps => (p.c : Real) * R ^ (p.i + p.j - 3) + negAggregate R ps

def coefficientsNonnegative (xs : List Term) : Bool :=
  xs.all fun p => decide (0 <= p.c)

def coefficientsNonpositive (xs : List Term) : Bool :=
  xs.all fun p => decide (p.c <= 0)

def degreesAtLeastThree (xs : List Term) : Bool :=
  xs.all fun p => decide (3 <= p.i + p.j)

theorem coefficientsNonnegative_sound {xs : List Term}
    (h : coefficientsNonnegative xs = true) :
    forall p, p ∈ xs -> 0 <= p.c := by
  simpa [coefficientsNonnegative, List.all_eq_true] using h

theorem coefficientsNonpositive_sound {xs : List Term}
    (h : coefficientsNonpositive xs = true) :
    forall p, p ∈ xs -> p.c <= 0 := by
  simpa [coefficientsNonpositive, List.all_eq_true] using h

theorem degreesAtLeastThree_sound {xs : List Term}
    (h : degreesAtLeastThree xs = true) :
    forall p, p ∈ xs -> 3 <= p.i + p.j := by
  simpa [degreesAtLeastThree, List.all_eq_true] using h

theorem monomial_le_radius_mul_cube {s t R : Real} {i j : Nat}
    (hs : 0 <= s) (ht : 0 <= t) (hR : s + t <= R)
    (hdeg : 3 <= i + j) :
    s ^ i * t ^ j <= R ^ (i + j - 3) * (s + t) ^ 3 := by
  have hsum : 0 <= s + t := add_nonneg hs ht
  have hmono : s ^ i * t ^ j <= (s + t) ^ (i + j) := by
    calc
      s ^ i * t ^ j <= (s + t) ^ i * (s + t) ^ j := by
        gcongr <;> linarith
      _ = (s + t) ^ (i + j) := by rw [pow_add]
  calc
    s ^ i * t ^ j <= (s + t) ^ (i + j) := hmono
    _ = (s + t) ^ (i + j - 3) * (s + t) ^ 3 := by
      rw [← pow_add, Nat.sub_add_cancel hdeg]
    _ <= R ^ (i + j - 3) * (s + t) ^ 3 := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hsum hR _) (pow_nonneg hsum _)

theorem evalTerm_lower {p : Term} {s t R : Real}
    (hs : 0 <= s) (ht : 0 <= t) (hR : s + t <= R)
    (hdeg : 3 <= p.i + p.j) (hc : p.c <= 0) :
    (p.c : Real) * R ^ (p.i + p.j - 3) * (s + t) ^ 3 <=
      evalTerm p s t := by
  unfold evalTerm
  have hm := monomial_le_radius_mul_cube (i := p.i) (j := p.j) hs ht hR hdeg
  have hc' : (p.c : Real) <= 0 := by exact_mod_cast hc
  have := mul_le_mul_of_nonpos_left hm hc'
  nlinarith

theorem evalTerms_nonneg {xs : List Term} {s t : Real}
    (hs : 0 <= s) (ht : 0 <= t)
    (hc : forall p, p ∈ xs -> 0 <= p.c) :
    0 <= evalTerms xs s t := by
  induction xs with
  | nil => simp [evalTerms]
  | cons p ps ih =>
      rw [evalTerms]
      apply add_nonneg
      · unfold evalTerm
        have hp : (0 : Real) <= p.c := by exact_mod_cast hc p (by simp)
        positivity
      · exact ih (fun q hq => hc q (by simp [hq]))

theorem evalTerms_lower_negAggregate {xs : List Term} {s t R : Real}
    (hs : 0 <= s) (ht : 0 <= t) (hR : s + t <= R)
    (hdeg : forall p, p ∈ xs -> 3 <= p.i + p.j)
    (hc : forall p, p ∈ xs -> p.c <= 0) :
    negAggregate R xs * (s + t) ^ 3 <= evalTerms xs s t := by
  induction xs with
  | nil => simp [negAggregate, evalTerms]
  | cons p ps ih =>
      rw [negAggregate, evalTerms]
      have hp := evalTerm_lower hs ht hR
        (hdeg p (by simp)) (hc p (by simp))
      have hps := ih (fun q hq => hdeg q (by simp [hq]))
        (fun q hq => hc q (by simp [hq]))
      nlinarith

end GeneralCK.Certificates.E8OriginPolynomialLower

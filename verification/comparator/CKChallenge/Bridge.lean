import CKChallenge.Defs
import GeneralCK.Statement

/-! Bridge: the repository's statement `GeneralCK.GeneralCourtadeKumar` implies the
Formal Conjectures statement. The two sets of definitions have identical bodies, so this is
definitional unfolding. -/

namespace CourtadeKumar

theorem of_general (h : GeneralCK.GeneralCourtadeKumar) (n : ℕ) (f : Cube n → Bool) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : mutualInfo f p ≤ 1 - binEntropyBits p :=
  h n f p hp₀ hp₁

end CourtadeKumar

#print axioms CourtadeKumar.of_general

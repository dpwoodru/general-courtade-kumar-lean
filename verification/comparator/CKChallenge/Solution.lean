import CKChallenge.Bridge
import CKRoute.Final

namespace CourtadeKumar

theorem courtade_kumar (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    mutualInfo f p ≤ 1 - binEntropyBits p :=
  of_general GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed n f p hp₀ hp₁

end CourtadeKumar

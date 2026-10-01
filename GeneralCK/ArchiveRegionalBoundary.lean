import GeneralCK.ConditionalCK
import GeneralCK.FiniteLaw

/-!
# A Lean boundary matching the archived same-side/opposite-side split

The historical Python certificate bundle organizes its global hybrid Bellman
proof by the two canonical mean regions. Each field below is the *entire*
regional conclusion, including any retained analytic manuscript inputs. It
must not be described as a numerical-only certificate proposition.
-/

namespace GeneralCK.ArchiveRegionalBoundary

structure Inputs : Prop where
  sameSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.b ≤ 1 / 2 → μ.gap ≤ μ.cost
  oppositeSide : ∀ (k : ℕ) (μ : GeneralCK.InteriorLaw (Fin k)),
    μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b → μ.gap ≤ μ.cost

theorem Inputs.toFiniteHybridBellman (h : Inputs) : GeneralCK.FiniteHybridBellman := by
  apply GeneralCK.finiteHybridBellman_of_canonical
  intro k μ hab hsum
  by_cases hb : μ.b ≤ 1 / 2
  · exact h.sameSide k μ hab hsum hb
  · exact h.oppositeSide k μ hab hsum (le_of_lt (lt_of_not_ge hb))

theorem Inputs.generalCourtadeKumar (h : Inputs) : GeneralCK.GeneralCourtadeKumar :=
  GeneralCK.generalCourtadeKumar_of_finiteHybridBellman h.toFiniteHybridBellman

#print axioms Inputs.toFiniteHybridBellman
#print axioms Inputs.generalCourtadeKumar

end GeneralCK.ArchiveRegionalBoundary

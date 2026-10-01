/-
Lane P-HMC — THE CHAIN.  Does my reduction actually land on FIELD 6's type?

`Reduce.lean` proved `HalfMeanSlopeGapOnCompact → PureGapD0CompactOwner`.  That is one link.
This module composes the remaining links and asks the kernel whether the result has EXACTLY
the type `GeneralCK.HalfMeanCurvatureNegative` — the type of field 6 of `ProductionOwners`
(`FinalProductionAssemblyPositiveCutoff.lean:50`, file sha256
39909ae04385a2ac9312e3a54267a48acf23b91277762d01a8d9f80c3ad1ce67).

A prose claim that two types are "the same" is worth nothing; this makes the elaborator say it.

🔴 STILL NOT CLOSURE.  Everything here is conditional on `HalfMeanSlopeGapOnCompact`, which is
UNPROVED.  What this establishes is that the hypothesis is the ONLY thing missing — i.e. that
there is no further type mismatch, no further hypothesis, and no further unowned leaf hiding
behind the composition.
-/
import GeneralCK.LanePHMC.Reduce
import E8GlobalRatioCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.LanePHMC

/-- The whole of field 6, from the single `e8Q`-free hypothesis. -/
theorem halfMeanCurvatureNegative_of_slopeGap
    (h : HalfMeanSlopeGapOnCompact) : HalfMeanCurvatureNegative :=
  halfMeanCurvatureNegative_of_remainingD0
    (pureGapD0RemainingOwners_of_compact_and_largeSStructure
      (pureGapD0CompactOwner_of_slopeGap h)
      GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified)

/-- GATE BY NAME.  The conclusion is the field-6 type under its own name. -/
example (h : HalfMeanSlopeGapOnCompact) : HalfMeanCurvatureNegative :=
  halfMeanCurvatureNegative_of_slopeGap h

/-- GATE UNFOLDED.  The same term against the field type written out in full, so a
`def` that merely *names* the right thing cannot pass for the thing itself. -/
example (h : HalfMeanSlopeGapOnCompact) :
    ∀ a e f : ℝ, a < 1 / 2 → 0 < e → 0 < f →
      e < H a → f < H (1 / 2) →
      e8Theta ((1 / 2 - a) / e) =
        2 * e8Theta ((1 / 2 - a) / (e + f)) →
      deriv (deriv (halfMeanPureGapCurve a e f)) (1 / 2) < 0 :=
  halfMeanCurvatureNegative_of_slopeGap h

/-- The `largeS` certificate really is unconditional: zero binders. -/
example : E8LargeSStructure := GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified

#check @halfMeanCurvatureNegative_of_slopeGap
#check @GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified
#print axioms halfMeanCurvatureNegative_of_slopeGap
#print axioms GeneralCK.E8RatioMonotonicity.e8LargeSStructureCertified

theorem phmc_chain_positive_control : (5 : Nat) + 7 = 12 := by norm_num
#print axioms phmc_chain_positive_control

end GeneralCK.LanePHMC

import CKRoute.Final

/-!
# Final check: the default `lake build` target

`lake build` compiles this file and therefore the final theorem together with its whole import
closure (45,500 modules). The two `#guard_msgs` commands make the build fail unless

* the final theorem has type `GeneralCK.GeneralCourtadeKumar`, the 63-line statement in
  `GeneralCK/Statement.lean`, and
* it depends on exactly Lean's three standard axioms: no `sorry` (`sorryAx`), no `native_decide`
  (`Lean.ofReduceBool`) and no added `axiom`.

Lean breaks the axiom list over several lines, hence `whitespace := lax`.
-/

/-- info: GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed : GeneralCK.GeneralCourtadeKumar -/
#guard_msgs (whitespace := lax) in
#check @GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed

/-- info: 'GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed

-- repeated without a guard so that the axioms appear in the build log
#print axioms GeneralCK.ArchiveRegionalBoundary.generalCourtadeKumar_closed

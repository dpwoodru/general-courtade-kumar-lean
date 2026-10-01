import GeneralCK.Certificates.BivariateProvedProgram

/-!
# One Boolean arithmetic pass for correction programs

Correction programs have a fixed, long arithmetic skeleton and only a small
number of logarithm/contact instructions.  This kernel checks every arithmetic
instruction in one Boolean traversal.  The accompanying `NonlinearValid`
predicate contains proof fields only at the transcendental instructions.  The
soundness theorem reconstructs the ordinary `Accepted` proposition used by the
existing semantic API.
-/

namespace GeneralCK.Certificates.CorrectionHybridProgramKernel

open BivariateJetProgram (Shape zeroBox)
open BivariateProvedProgram

def arithmeticStepCheck {p : ℕ} (shape : Shape)
    (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Bool :=
  decide (InRange shape boxes.length) && match shape with
  | .add i j => ((boxes.getD i (zeroBox p)).add
      (boxes.getD j (zeroBox p))).subsetCheck out
  | .neg i => (boxes.getD i (zeroBox p)).neg.subsetCheck out
  | .mul i j => ((boxes.getD i (zeroBox p)).mul
      (boxes.getD j (zeroBox p))).subsetCheck out
  | .inv i => (boxes.getD i (zeroBox p)).invCheck out
  | .log _ | .contact _ => true

def arithmeticCheck {p : ℕ} : List (Instruction p) →
    List (DyadicBivariateJetEnclosure p) → Bool
  | [], _ => true
  | instruction :: rest, boxes =>
      arithmeticStepCheck instruction.shape boxes instruction.proposed &&
        arithmeticCheck rest (instruction.proposed :: boxes)

def nonlinearStepValid {p : ℕ} (shape : Shape)
    (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Prop :=
  match shape with
  | .log _ | .contact _ => StepValid shape boxes out
  | _ => True

def NonlinearValid {p : ℕ} : List (Instruction p) →
    List (DyadicBivariateJetEnclosure p) → Prop
  | [], _ => True
  | instruction :: rest, boxes =>
      nonlinearStepValid instruction.shape boxes instruction.proposed ∧
      NonlinearValid rest (instruction.proposed :: boxes)

theorem arithmeticStepCheck_sound_of_nonlinear {p : ℕ} {shape : Shape}
    {boxes : List (DyadicBivariateJetEnclosure p)}
    {out : DyadicBivariateJetEnclosure p}
    (hc : arithmeticStepCheck shape boxes out = true)
    (hn : nonlinearStepValid shape boxes out) :
    StepValid shape boxes out := by
  have parts := Bool.and_eq_true_iff.mp hc
  have hrange : InRange shape boxes.length := of_decide_eq_true parts.1
  cases shape with
  | add _ _ => exact ⟨hrange, parts.2⟩
  | neg _ => exact ⟨hrange, parts.2⟩
  | mul _ _ => exact ⟨hrange, parts.2⟩
  | inv _ => exact ⟨hrange, parts.2⟩
  | log _ => exact hn
  | contact _ => exact hn

theorem accepted_of_arithmeticCheck_of_nonlinearValid {p : ℕ}
    (program : List (Instruction p))
    (boxes : List (DyadicBivariateJetEnclosure p))
    (hc : arithmeticCheck program boxes = true)
    (hn : NonlinearValid program boxes) : Accepted program boxes := by
  induction program generalizing boxes with
  | nil => trivial
  | cons instruction rest ih =>
      have checks := Bool.and_eq_true_iff.mp hc
      exact ⟨arithmeticStepCheck_sound_of_nonlinear checks.1 hn.1,
        ih _ checks.2 hn.2⟩

theorem nonlinearValid_of_accepted {p : ℕ}
    (program : List (Instruction p))
    (boxes : List (DyadicBivariateJetEnclosure p))
    (h : Accepted program boxes) : NonlinearValid program boxes := by
  induction program generalizing boxes with
  | nil => trivial
  | cons instruction rest ih =>
      constructor
      · cases hs : instruction.shape <;> simp only [nonlinearStepValid]
        all_goals simpa only [hs] using h.1
      · exact ih _ h.2

#print axioms arithmeticStepCheck_sound_of_nonlinear
#print axioms accepted_of_arithmeticCheck_of_nonlinearValid
#print axioms nonlinearValid_of_accepted

end GeneralCK.Certificates.CorrectionHybridProgramKernel

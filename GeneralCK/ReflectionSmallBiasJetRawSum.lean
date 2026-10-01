import GeneralCK.ReflectionSmallBiasJetReplay

/-! Append finite Taylor sums without repeatedly normalizing intermediate lists. -/

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open SmallBiasPolynomial

theorem addAppend {n : ℕ} {k : ℂ} {f g : ℂ × ℂ → ℂ} {p q : List Term}
    (hf : Approximates n k f p) (hg : Approximates n k g q) :
    Approximates n k (fun z => f z + g z) (p ++ q) := by
  refine ⟨hf.analytic.add hg.analytic, ?_⟩
  apply (hf.error.add hg.error).congr_left
  intro z
  rw [eval_append]
  ring

end GeneralCK.Reflection.SmallBiasJet.Approximates


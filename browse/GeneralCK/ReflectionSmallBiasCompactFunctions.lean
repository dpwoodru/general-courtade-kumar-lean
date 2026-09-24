import GeneralCK.ReflectionSmallBiasJetFunctions
import GeneralCK.ReflectionSmallBiasJetComposition
import GeneralCK.ReflectionSmallBiasPolynomialCertificate

/-! Compact, kernel-checked entropy and atanh series used before composition. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def entropySeed : List Term :=
  [⟨0, 0, 1, 1⟩, ⟨2, 0, 0, -1/2⟩, ⟨4, 0, 0, -1/12⟩,
   ⟨6, 0, 0, -1/30⟩, ⟨8, 0, 0, -1/56⟩, ⟨10, 0, 0, -1/90⟩,
   ⟨12, 0, 0, -1/132⟩, ⟨14, 0, 0, -1/182⟩, ⟨16, 0, 0, -1/240⟩,
   ⟨18, 0, 0, -1/306⟩, ⟨20, 0, 0, -1/380⟩, ⟨22, 0, 0, -1/462⟩]

def atanhSeed : List Term :=
  [⟨1, 0, 0, 1⟩, ⟨3, 0, 0, 1/3⟩, ⟨5, 0, 0, 1/5⟩,
   ⟨7, 0, 0, 1/7⟩, ⟨9, 0, 0, 1/9⟩, ⟨11, 0, 0, 1/11⟩,
   ⟨13, 0, 0, 1/13⟩, ⟨15, 0, 0, 1/15⟩, ⟨17, 0, 0, 1/17⟩,
   ⟨19, 0, 0, 1/19⟩, ⟨21, 0, 0, 1/21⟩, ⟨23, 0, 0, 1/23⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem entropySeed_checked : equalityCheck (entropy 24 coordinateA) entropySeed = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atanhSeed_checked : equalityCheck (atanh 24 coordinateA) atanhSeed = true := by
  decide +kernel

def compactEntropy (p : List Term) : List Term := substitute 24 p (const 0) entropySeed
def compactAtanh (p : List Term) : List Term := substitute 24 p (const 0) atanhSeed

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open SmallBiasPolynomial

theorem compactEntropy {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ))
    (hf : Approximates 24 k f p) (hzero : f 0 = 0) :
    Approximates 24 k (fun z => ComplexEntropy.entropyExt (f z))
      (SmallBiasPolynomial.compactEntropy p) := by
  have hs := ((coordinateA 24 k).entropy hk hklog (by rfl)).replacePolynomial
    (equalityCheck_sound entropySeed_checked k)
  simpa only [Rat.cast_zero, SmallBiasPolynomial.compactEntropy] using
    hf.comp hk (const 24 k 0) hzero (by simp) hs

theorem compactAtanh {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hf : Approximates 24 k f p) (hzero : f 0 = 0) :
    Approximates 24 k (fun z => SmallBiasComplexDomain.atanhExt (f z))
      (SmallBiasPolynomial.compactAtanh p) := by
  have hs := ((coordinateA 24 k).atanh hk (by rfl)).replacePolynomial
    (equalityCheck_sound atanhSeed_checked k)
  simpa only [Rat.cast_zero, SmallBiasPolynomial.compactAtanh] using
    hf.comp hk (const 24 k 0) hzero (by simp) hs

end GeneralCK.Reflection.SmallBiasJet.Approximates

import GeneralCK.ReflectionSmallBiasJetInverse
import GeneralCK.ReflectionSmallBiasPicard

/-! # Entropy, atanh and finite contact iteration in the Taylor verifier -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def entropy (n : ℕ) (p : List Term) : List Term :=
  add (parameter 1) (scale (-1 / 2)
    (add (mulTrunc n (add (const 1) p) (logOneAdd n p))
      (mulTrunc n (add (const 1) (scale (-1) p)) (logOneAdd n (scale (-1) p)))))

def atanh (n : ℕ) (p : List Term) : List Term :=
  scale (1 / 2) (add (logOneAdd n p) (scale (-1) (logOneAdd n (scale (-1) p))))

def picard (n : ℕ) : ℕ → List Term
  | 0 => const 0
  | m + 1 => mulTrunc n coordinateA (entropy n (picard n m))

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem entropy {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ))
    (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0) :
    Approximates (n + 1) k (fun z => ComplexEntropy.entropyExt (f z))
      (SmallBiasPolynomial.entropy (n + 1) p) := by
  have hneg := hf.scale (-1)
  have hneg0 : (fun z => ((-1 : ℚ) : ℂ) * f z) 0 = 0 := by simp [hzero]
  have hplus := (const (n + 1) k 1).add hf
  have hminus := (const (n + 1) k 1).add hneg
  have hp := hplus.mul hk (hf.logOneAdd hk hzero)
  have hm := hminus.mul hk (hneg.logOneAdd hk hneg0)
  have hh := (parameter (n + 1) k 1).add ((hp.add hm).scale (-1 / 2))
  convert hh using 1
  · funext z
    simp only [ComplexEntropy.entropyExt, hklog, zpow_one, Rat.cast_one,
      Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, neg_one_mul, ← sub_eq_add_neg]
    ring
  · rfl

theorem atanh {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hk : k ≠ 0) (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0) :
    Approximates (n + 1) k (fun z => SmallBiasComplexDomain.atanhExt (f z))
      (SmallBiasPolynomial.atanh (n + 1) p) := by
  have hneg := hf.scale (-1)
  have hneg0 : (fun z => ((-1 : ℚ) : ℂ) * f z) 0 = 0 := by simp [hzero]
  have hh := ((hf.logOneAdd hk hzero).add ((hneg.logOneAdd hk hneg0).scale (-1))).scale (1 / 2)
  convert hh using 1
  · funext z
    simp only [SmallBiasComplexDomain.atanhExt, Rat.cast_one, Rat.cast_neg,
      Rat.cast_div, Rat.cast_ofNat, neg_one_mul, ← sub_eq_add_neg]
    ring
  · rfl

theorem picard {n : ℕ} {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ)) (m : ℕ) :
    Approximates (n + 1) k (fun z => SmallBiasPicard.iterate m z.1)
      (SmallBiasPolynomial.picard (n + 1) m) := by
  induction m with
  | zero => simpa only [SmallBiasPicard.iterate, SmallBiasPolynomial.picard, Rat.cast_zero]
      using const (n + 1) k 0
  | succ m ih =>
    exact (coordinateA (n + 1) k).mul hk (ih.entropy hk hklog (by simp))

end GeneralCK.Reflection.SmallBiasJet.Approximates

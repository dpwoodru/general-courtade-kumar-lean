import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay1
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay2
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay3
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay4
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay5
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay6
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay7
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay8
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay9
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay10
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay11
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay12
import GeneralCK.Certificates.ReflectionSmallBiasPicardReplay13
import GeneralCK.Certificates.ReflectionSmallBiasPicardPhiReplay
import GeneralCK.ReflectionSmallBiasContactValueJet

namespace GeneralCK.Reflection.SmallBiasPicardData

open SmallBiasJet SmallBiasPicard

theorem iterate12_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => iterate 12 z.1) stage12 := by
  have h0 : Approximates 24 k (fun z => iterate 0 z.1) stage0 := by
    convert Approximates.exactPolynomial 24 k ([] : List SmallBiasPolynomial.Term) using 1
    <;> rfl
  have h1 : Approximates 24 k (fun z => iterate 1 z.1) stage1 :=
    stage1_replay hk hklog h0 (by simp)
  have h2 : Approximates 24 k (fun z => iterate 2 z.1) stage2 :=
    stage2_replay hk hklog h1 (by simp)
  have h3 : Approximates 24 k (fun z => iterate 3 z.1) stage3 :=
    stage3_replay hk hklog h2 (by simp)
  have h4 : Approximates 24 k (fun z => iterate 4 z.1) stage4 :=
    stage4_replay hk hklog h3 (by simp)
  have h5 : Approximates 24 k (fun z => iterate 5 z.1) stage5 :=
    stage5_replay hk hklog h4 (by simp)
  have h6 : Approximates 24 k (fun z => iterate 6 z.1) stage6 :=
    stage6_replay hk hklog h5 (by simp)
  have h7 : Approximates 24 k (fun z => iterate 7 z.1) stage7 :=
    stage7_replay hk hklog h6 (by simp)
  have h8 : Approximates 24 k (fun z => iterate 8 z.1) stage8 :=
    stage8_replay hk hklog h7 (by simp)
  have h9 : Approximates 24 k (fun z => iterate 9 z.1) stage9 :=
    stage9_replay hk hklog h8 (by simp)
  have h10 : Approximates 24 k (fun z => iterate 10 z.1) stage10 :=
    stage10_replay hk hklog h9 (by simp)
  have h11 : Approximates 24 k (fun z => iterate 11 z.1) stage11 :=
    stage11_replay hk hklog h10 (by simp)
  have h12 : Approximates 24 k (fun z => iterate 12 z.1) stage12 :=
    stage12_replay hk hklog h11 (by simp)
  exact h12

theorem iterate_stable_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) (m : ℕ) :
    Approximates 24 k (fun z => iterate (12+m) z.1) stage12 := by
  induction m with
  | zero => exact iterate12_approximates hk hklog
  | succ m ih =>
    exact stage13_replay hk hklog ih (by simp)

theorem phi_approximates_table {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => SmallBiasContactValueJet.phi z.1) phi := by
  apply SmallBiasContactValueJet.phi_from_finite_jet
  exact phi_replay hk (iterate_stable_approximates hk hklog 10) (by simp)

end GeneralCK.Reflection.SmallBiasPicardData

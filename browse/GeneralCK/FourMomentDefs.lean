import GeneralCK.BellmanAssembly

namespace GeneralCK

/-- The finite interior version of the upstream atom correction kappa. -/
noncomputable def atomCorrection (u v : ℝ) : ℝ :=
  interiorCost u v-F |u-v| ((H u+H v)/2)

/-- The upstream entropy correction g, through lower-half entropy representatives. -/
noncomputable def entropyCorrection (e f : ℝ) : ℝ :=
  atomCorrection (entropyInverse e) (entropyInverse f)

noncomputable def fourMomentLowerBound (a b e f : ℝ) : ℝ :=
  F |a-b| ((e+f)/2)+entropyCorrection e f

/-- The upstream pure gap L4-Rphi; distinct from cost-Rphi and the hybrid gap. -/
noncomputable def pureGap (a b e f : ℝ) : ℝ :=
  fourMomentLowerBound a b e f-candidateGap phi a b e f

@[simp] theorem entropyCorrection_self (e : ℝ) : entropyCorrection e e = 0 := by
  simp [entropyCorrection,atomCorrection,interiorCost,F]

end GeneralCK

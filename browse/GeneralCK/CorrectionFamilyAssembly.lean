import GeneralCK.CorrectionRatioBellmanClosure

/-!
# Assembly interface for generated correction families

Generated correction certificates naturally prove positivity on closed
`(u, rho)` boxes.  These definitions and lemmas combine such theorems without
replaying any interval arithmetic and expose the full-box premise consumed by
the Bellman closure.
-/

namespace GeneralCK.Correction

/-- Positivity of the actual correction Hessian minors at one probability-ratio
point. -/
def ActualRatioMinorsPositive (u rho : ℝ) : Prop :=
  0 < Mleft (H u) (H (u+rho*(1/2-u))) ∧
  0 < Mdet (H u) (H (u+rho*(1/2-u)))

/-- The common conclusion of a generated correction-family aggregate theorem
on a closed coordinate box.  The separate `rho < 1` premise handles a closed
certificate box whose upper face is `rho = 1`. -/
def ActualRatioFamilyOn (u0 u1 rho0 rho1 : ℝ) : Prop :=
  ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc u0 u1 → rho ∈ Set.Icc rho0 rho1 → rho < 1 →
    ActualRatioMinorsPositive u rho

theorem ActualRatioFamilyOn.mono {u0 u1 rho0 rho1 U0 U1 R0 R1 : ℝ}
    (h : ActualRatioFamilyOn u0 u1 rho0 rho1)
    (hu0 : u0 ≤ U0) (hu1 : U1 ≤ u1) (hr0 : rho0 ≤ R0) (hr1 : R1 ≤ rho1) :
    ActualRatioFamilyOn U0 U1 R0 R1 := by
  intro u rho hu hr hrho
  exact h ⟨hu0.trans hu.1, hu.2.trans hu1⟩
    ⟨hr0.trans hr.1, hr.2.trans hr1⟩ hrho

theorem ActualRatioFamilyOn.union_u {u0 c u1 rho0 rho1 : ℝ}
    (hleft : ActualRatioFamilyOn u0 c rho0 rho1)
    (hright : ActualRatioFamilyOn c u1 rho0 rho1) :
    ActualRatioFamilyOn u0 u1 rho0 rho1 := by
  intro u rho hu hr hrho
  by_cases huc : u ≤ c
  · exact hleft ⟨hu.1, huc⟩ hr hrho
  · exact hright ⟨le_of_lt (lt_of_not_ge huc), hu.2⟩ hr hrho

theorem ActualRatioFamilyOn.union_rho {u0 u1 rho0 c rho1 : ℝ}
    (hlow : ActualRatioFamilyOn u0 u1 rho0 c)
    (hhigh : ActualRatioFamilyOn u0 u1 c rho1) :
    ActualRatioFamilyOn u0 u1 rho0 rho1 := by
  intro u rho hu hr hrho
  by_cases hrc : rho ≤ c
  · exact hlow hu ⟨hr.1, hrc⟩ hrho
  · exact hhigh hu ⟨le_of_lt (lt_of_not_ge hrc), hr.2⟩ hrho

/-- The planned C1 and C2 aggregate theorems join exactly at `u = 1/10`.
C1 starts at `rho = 3/40`, so it also covers the narrower common band
`rho ≥ 1/10`. -/
theorem actualRatioFamilyOn_c1_c2_band
    (hC1 : ActualRatioFamilyOn (1/50) (1/10) (3/40) 1)
    (hC2 : ActualRatioFamilyOn (1/10) (1/5) (1/10) 1) :
    ActualRatioFamilyOn (1/50) (1/5) (1/10) 1 := by
  have hC1' : ActualRatioFamilyOn (1/50) (1/10) (1/10) 1 :=
    hC1.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hC1'.union_u hC2

/-- Adapter whose hypotheses exactly match the generated `full_c1` and
`full_c2` theorem signatures.  It can be instantiated as soon as both family
aggregates have independently passed Lean checking. -/
theorem actualRatioFamilyOn_c1_c2_of_aggregate_theorems
    (full_c1 : ∀ ⦃u rho : ℝ⦄,
      u ∈ Set.Icc (1/50) (1/10) → rho ∈ Set.Icc (3/40) 1 → rho < 1 →
      0 < Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Mdet (H u) (H (u+rho*(1/2-u))))
    (full_c2 : ∀ ⦃u rho : ℝ⦄,
      u ∈ Set.Icc (1/10) (1/5) → rho ∈ Set.Icc (1/10) 1 → rho < 1 →
      0 < Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Mdet (H u) (H (u+rho*(1/2-u)))) :
    ActualRatioFamilyOn (1/50) (1/5) (1/10) 1 :=
  actualRatioFamilyOn_c1_c2_band full_c1 full_c2

/-- A generated family covering the full closed coordinate box supplies the
open-coordinate premise used by `CorrectionRatioBellmanClosure`. -/
theorem actualRatioFamily_of_full_box
    (hbox : ActualRatioFamilyOn 0 (1/2) 0 1) :
    ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Mdet (H u) (H (u+rho*(1/2-u))) := by
  intro u rho hu huhalf hr hr1
  exact hbox ⟨hu.le, huhalf.le⟩ ⟨hr.le, hr1.le⟩ hr1

#print axioms ActualRatioFamilyOn.mono
#print axioms ActualRatioFamilyOn.union_u
#print axioms ActualRatioFamilyOn.union_rho
#print axioms actualRatioFamilyOn_c1_c2_band
#print axioms actualRatioFamilyOn_c1_c2_of_aggregate_theorems
#print axioms actualRatioFamily_of_full_box

end GeneralCK.Correction

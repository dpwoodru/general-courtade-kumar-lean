import GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema
namespace GeneralCK.Certificates.E8TAxisZero0004Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel
noncomputable def sLower : ℝ := (3 / 32 : ℝ)
noncomputable def sUpper : ℝ := (1 / 10 : ℝ)
noncomputable def tLower : ℝ := (0 / 1 : ℝ)
noncomputable def tUpper : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerS : ℝ := (31 / 320 : ℝ)
noncomputable def centerT : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-4567192616659071619386515102238384436424789197, 4567192616659071619386515102238384436424789197⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩

def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩
theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]
theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith
end GeneralCK.Certificates.E8TAxisZero0004Geometry

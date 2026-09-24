import CKLaneC.RSCell.CellAPI

/-!
# Lane C, RA-stat interior: FLAT staged cell check (one kernel `decide` per stage)

The monolithic `cellCheck c q` evaluates the whole rayGamma TM inside one declaration, which peaks at about 9.5 GB.
Here a witness `w : Wit` supplies the intermediate TMs as literals:
* the base-derived inputs of the blocks;
* the outputs of the five heavy blocks.

Each stage is checked by its own `decide` in its own theorem, so the kernel caches are per stage.
`cellG_eq_GW` shows purely symbolically, by rewriting, that when all stages hold, `cellG c q = GW w`.
Hence `staged_check` yields `cellCheck c q = true`, and `cellCheck_sound` applies unchanged.
-/

namespace CKLaneC.RSCell

open CKLaneC.TM3

deriving instance DecidableEq for TM

structure Wit where
  Z0 : TM
  Z1 : TM
  Z2 : TM
  Z3 : TM
  iE : TM
  iHu : TM
  T : TM
  E : TM
  de : TM
  dde : TM
  nJu : TM
  Jd1 : TM
  term0 : TM
  r0 : TM
  r1 : TM
  r2 : TM
  r3 : TM
  eta : TM

/-- Stage B: the base block and the inputs of the heavy blocks. -/
noncomputable def stageB (c : Cell) (w : Wit) : Bool :=
  decide (mul (base c).TD (base c).iE = w.Z0) && decide (mul (base c).Dd (base c).iE = w.Z1)
  && decide (mul (TM.add (base c).r12b (base c).TD) (base c).iE = w.Z2)
  && decide (mul (TM.add (base c).r12b (TM.scaleInt (base c).TD 2)) (base c).iHu = w.Z3)
  && decide (mulc (TM.neg (base c).Ju) half = w.de) && decide (mulc (base c).Jd1 half = w.dde)
  && decide (TM.neg (base c).Ju = w.nJu) && decide ((base c).Jd1 = w.Jd1)
  && decide ((base c).iE = w.iE) && decide ((base c).iHu = w.iHu) && decide ((base c).T = w.T)
  && decide ((base c).E = w.E) && decide ((base c).term0 = w.term0)

noncomputable def stageC0 (w : Wit) (q : Cert) : Bool :=
  decide (raysec w.Z0 w.iE w.T w.de w.dde (contactFuncs w.Z0 (checkImplicit true w.Z0 q.V0 q.r0)) = w.r0)

noncomputable def stageC1 (w : Wit) (q : Cert) : Bool :=
  decide (raysec w.Z1 w.iE (TM.const ONEi 0) w.de w.dde (contactFuncs w.Z1 (checkImplicit true w.Z1 q.V1 q.r1))
    = w.r1)

noncomputable def stageC2 (w : Wit) (q : Cert) : Bool :=
  decide (raysec w.Z2 w.iE w.T w.de w.dde (contactFuncs w.Z2 (checkImplicit true w.Z2 q.V2 q.r2)) = w.r2)

noncomputable def stageC3 (w : Wit) (q : Cert) : Bool :=
  decide (raysec w.Z3 w.iHu (TM.scaleInt w.T 2) w.nJu w.Jd1 (contactFuncs w.Z3 (checkImplicit true w.Z3 q.V3 q.r3))
    = w.r3)

noncomputable def stageE (w : Wit) (q : Cert) : Bool :=
  decide (etaBlock w.E w.de w.dde (checkImplicit false w.E q.Vm q.rm) = w.eta)

/-- The final TM assembled from the witness. -/
noncomputable def GW (w : Wit) : TM :=
  TM.add (TM.add (TM.add (TM.add (TM.add w.term0 w.r0) (TM.neg w.r1)) w.r2) w.eta) (TM.neg (mulc w.r3 half))

noncomputable def stageF (w : Wit) : Bool := (GW w).ok && decide (0 < (GW w).lower)

theorem cellG_eq_GW (c : Cell) (q : Cert) (w : Wit) (hB : stageB c w = true) (h0 : stageC0 w q = true)
    (h1 : stageC1 w q = true) (h2 : stageC2 w q = true) (h3 : stageC3 w q = true) (hE : stageE w q = true) :
    cellG c q = GW w := by
  simp only [stageB, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hZ0, hZ1⟩, hZ2⟩, hZ3⟩, hde⟩, hdde⟩, hnJu⟩, hJd1⟩, hiE⟩, hiHu⟩, hT⟩, hEE⟩, hterm0⟩ := hB
  simp only [stageC0, stageC1, stageC2, stageC3, stageE, decide_eq_true_eq] at h0 h1 h2 h3 hE
  simp only [cellG]
  rw [hZ0, hZ1, hZ2, hZ3, hde, hdde, hnJu, hJd1, hiE, hiHu, hT, hEE, hterm0, h0, h1, h2, h3, hE]
  rfl

/-- All stages together give the monolithic check. -/
theorem staged_check (c : Cell) (q : Cert) (w : Wit) (hd : domOK c = true) (hB : stageB c w = true)
    (h0 : stageC0 w q = true) (h1 : stageC1 w q = true) (h2 : stageC2 w q = true) (h3 : stageC3 w q = true)
    (hE : stageE w q = true) (hF : stageF w = true) : (domOK c && cellCheck c q) = true := by
  have hG := cellG_eq_GW c q w hB h0 h1 h2 h3 hE
  have : cellCheck c q = stageF w := by
    unfold cellCheck stageF; rw [hG]
  rw [hd, this, hF]; rfl

end CKLaneC.RSCell

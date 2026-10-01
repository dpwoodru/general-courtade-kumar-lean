import GeneralCK.Certificates.JetProgram

namespace GeneralCK.Certificates.JetProgram

/-- Scalar semantics allow expression matching without expanding unused derivative fields. -/
noncomputable def Op.evalReal {p : ℕ} (op : Op p) (values : List ℝ) : ℝ := match op with
  | .add i j => values.getD i 0+values.getD j 0
  | .neg i => -values.getD i 0
  | .mul i j => values.getD i 0*values.getD j 0
  | .inv i => (values.getD i 0)⁻¹
  | .log i _ _ => Real.log (values.getD i 0)
  | .contact i _ _ _ _ _ => GeneralCK.Reflection.biasContact (values.getD i 0)

theorem value_getD (jets : List Jet2) (i : ℕ) (t : ℝ) :
    (jets.getD i zeroJet).value t=(jets.map (fun j => j.value t)).getD i 0 := by
  induction jets generalizing i with
  | nil => simp [zeroJet,Jet2.const]
  | cons j jets ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Op.eval_value {p : ℕ} (op : Op p) (jets : List Jet2) (t : ℝ) :
    (op.eval jets).value t=op.evalReal (jets.map (fun j => j.value t)) := by
  cases op <;> simp only [Op.eval,Op.evalReal,Jet2.add,Jet2.neg,Jet2.mul,Jet2.inv,Jet2.log,
    Jet2.comp,reflectionContactJet,value_getD]

noncomputable def evalRealProgram {p : ℕ} : List (Instruction p) → List ℝ → List ℝ
  | [], values => values
  | ins :: rest, values => evalRealProgram rest (ins.op.evalReal values :: values)

theorem finalJets_values {p : ℕ} (program : List (Instruction p)) (jets : List Jet2) (t : ℝ) :
    (finalJets program jets).map (fun j => j.value t)=
      evalRealProgram program (jets.map (fun j => j.value t)) := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,evalRealProgram,List.map_cons,Op.eval_value] using
      ih (ins.op.eval jets :: jets)

theorem finalJet_value {p : ℕ} (program : List (Instruction p)) (jets : List Jet2) (i : ℕ) (t : ℝ) :
    ((finalJets program jets).getD i zeroJet).value t=
      (evalRealProgram program (jets.map (fun j => j.value t))).getD i 0 := by
  rw [value_getD,finalJets_values]

end GeneralCK.Certificates.JetProgram

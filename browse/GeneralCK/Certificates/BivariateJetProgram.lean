import GeneralCK.Certificates.DyadicBivariateJetBounds

namespace GeneralCK.Certificates.BivariateJetProgram

/-- Every nonlinear witness is checked; none is a semantic hypothesis. -/
inductive Op (p : ℕ) where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ) (lower upper : DyadicLog.Witness)
  | contact (arg : ℕ) (c B : DyadicInterval p) (outer : DyadicJetEnclosure p)
      (bracket : DyadicContact.BracketWitness p) (denominator : DyadicEntropy.BWitness p)

def zeroBox (p : ℕ) : DyadicBivariateJetEnclosure p := DyadicBivariateJetEnclosure.const p 0
def zeroJet : BivariateJet2 := BivariateJet2.const 0

/-- The computational shape contains no interval proposals or witnesses. -/
inductive Shape where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ)
  | contact (arg : ℕ)
  deriving DecidableEq

noncomputable def Shape.eval (shape : Shape) (jets : List BivariateJet2) : BivariateJet2 :=
  match shape with
  | .add i j => (jets.getD i zeroJet).add (jets.getD j zeroJet)
  | .neg i => (jets.getD i zeroJet).neg
  | .mul i j => (jets.getD i zeroJet).mul (jets.getD j zeroJet)
  | .inv i => (jets.getD i zeroJet).inv
  | .log i => (jets.getD i zeroJet).log
  | .contact i => BivariateJet2.outerCompose reflectionContactJet (jets.getD i zeroJet)

namespace Op

def shape {p : ℕ} : Op p → Shape
  | .add i j => .add i j
  | .neg i => .neg i
  | .mul i j => .mul i j
  | .inv i => .inv i
  | .log i _ _ => .log i
  | .contact i _ _ _ _ _ => .contact i

def InRange {p : ℕ} (op : Op p) (n : ℕ) : Prop := match op with
  | .add i j | .mul i j => i<n ∧ j<n
  | .neg i | .inv i | .log i _ _ | .contact i _ _ _ _ _ => i<n

instance {p : ℕ} (op : Op p) (n : ℕ) : Decidable (op.InRange n) := by
  cases op <;> unfold InRange <;> infer_instance

noncomputable def eval {p : ℕ} (op : Op p) (jets : List BivariateJet2) : BivariateJet2 := match op with
  | .add i j => (jets.getD i zeroJet).add (jets.getD j zeroJet)
  | .neg i => (jets.getD i zeroJet).neg
  | .mul i j => (jets.getD i zeroJet).mul (jets.getD j zeroJet)
  | .inv i => (jets.getD i zeroJet).inv
  | .log i _ _ => (jets.getD i zeroJet).log
  | .contact i _ _ _ _ _ => BivariateJet2.outerCompose reflectionContactJet (jets.getD i zeroJet)

theorem eval_eq_shape {p : ℕ} (op : Op p) (jets : List BivariateJet2) :
    op.eval jets=op.shape.eval jets := by cases op <;> rfl

def check {p : ℕ} (op : Op p) (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Bool :=
  decide (op.InRange boxes.length) && match op with
  | .add i j => ((boxes.getD i (zeroBox p)).add (boxes.getD j (zeroBox p))).subsetCheck out
  | .neg i => (boxes.getD i (zeroBox p)).neg.subsetCheck out
  | .mul i j => ((boxes.getD i (zeroBox p)).mul (boxes.getD j (zeroBox p))).subsetCheck out
  | .inv i => (boxes.getD i (zeroBox p)).invCheck out
  | .log i wl wu => (boxes.getD i (zeroBox p)).logCheck out wl wu
  | .contact i c B outer w bw =>
      (boxes.getD i (zeroBox p)).contactCheck out c B outer w bw

end Op

structure Instruction (p : ℕ) where
  op : Op p
  proposed : DyadicBivariateJetEnclosure p

def check {p : ℕ} : List (Instruction p) → List (DyadicBivariateJetEnclosure p) → Bool
  | [], _ => true
  | ins::rest, boxes => ins.op.check boxes ins.proposed && check rest (ins.proposed::boxes)

def finalBoxes {p : ℕ} : List (Instruction p) → List (DyadicBivariateJetEnclosure p) → List (DyadicBivariateJetEnclosure p)
  | [], boxes => boxes
  | ins::rest, boxes => finalBoxes rest (ins.proposed::boxes)

noncomputable def finalJets {p : ℕ} : List (Instruction p) → List BivariateJet2 → List BivariateJet2
  | [], jets => jets
  | ins::rest, jets => finalJets rest (ins.op.eval jets::jets)

def shapes {p : ℕ} (program : List (Instruction p)) : List Shape :=
  program.map (fun ins => ins.op.shape)

noncomputable def executeShapes : List Shape → List BivariateJet2 → List BivariateJet2
  | [], jets => jets
  | op::rest, jets => executeShapes rest (op.eval jets::jets)

/-- Exact expression semantics are independent of every proposed enclosure and
every numerical witness, including the certificate precision. -/
theorem finalJets_eq_executeShapes {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) : finalJets program jets=executeShapes (shapes program) jets := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih => simpa only [finalJets,shapes,List.map_cons,executeShapes,Op.eval_eq_shape] using ih (ins.op.shape.eval jets::jets)

theorem finalJets_eq_of_shapes_eq {p q : ℕ} {left : List (Instruction p)}
    {right : List (Instruction q)} (h : shapes left=shapes right) (jets : List BivariateJet2) :
    finalJets left jets=finalJets right jets := by
  rw [finalJets_eq_executeShapes,finalJets_eq_executeShapes,h]

def RegistersContain {p : ℕ} (boxes : List (DyadicBivariateJetEnclosure p)) (jets : List BivariateJet2) (t : ℝ) : Prop :=
  boxes.length=jets.length ∧ ∀ i, (boxes.getD i (zeroBox p)).Contains (jets.getD i zeroJet) t

def RegistersSound (jets : List BivariateJet2) (da dz t : ℝ) : Prop :=
  ∀ i, (jets.getD i zeroJet).DirectionalSoundAt da dz t

theorem RegistersContain.nil (p : ℕ) (t : ℝ) :
    RegistersContain ([] : List (DyadicBivariateJetEnclosure p)) [] t := by
  refine ⟨rfl,fun i => ?_⟩
  simpa only [List.getD_nil,zeroBox,zeroJet,Int.cast_zero] using
    DyadicBivariateJetEnclosure.contains_const p 0 t

theorem RegistersSound.nil (da dz t : ℝ) : RegistersSound [] da dz t := by
  intro i
  simpa only [List.getD_nil,zeroJet,BivariateJet2.DirectionalSoundAt,
    BivariateJet2.projection_const] using Jet2.soundAt_const 0 t

theorem Op.check_inRange {p : ℕ} {op : Op p} {boxes : List (DyadicBivariateJetEnclosure p)}
    {out : DyadicBivariateJetEnclosure p} (h : op.check boxes out=true) : op.InRange boxes.length :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem RegistersContain.cons {p : ℕ} {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {t : ℝ} {box : DyadicBivariateJetEnclosure p} {jet : BivariateJet2} (h : RegistersContain boxes jets t)
    (hj : box.Contains jet t) : RegistersContain (box::boxes) (jet::jets) t := by
  refine ⟨by simpa using h.1,?_⟩
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h.2 i

theorem RegistersSound.cons {jets : List BivariateJet2} {jet : BivariateJet2} {da dz t : ℝ}
    (h : RegistersSound jets da dz t) (hj : jet.DirectionalSoundAt da dz t) :
    RegistersSound (jet::jets) da dz t := by
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h i

theorem Op.check_encloses {p : ℕ} (op : Op p) {boxes : List (DyadicBivariateJetEnclosure p)}
    {jets : List BivariateJet2} {out : DyadicBivariateJetEnclosure p} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : op.check boxes out=true) : out.Contains (op.eval jets) t := by
  have hd := (Bool.and_eq_true_iff.mp hc).2
  cases op with
  | add i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).add (h.2 j))
  | neg i => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd (h.2 i).neg
  | mul i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).mul (h.2 j))
  | inv i => simpa only [Op.eval,BivariateJet2.inv_eq_outerCompose] using DyadicBivariateJetEnclosure.invCheck_sound hd (h.2 i)
  | log i wl wu => simpa only [Op.eval,BivariateJet2.log_eq_outerCompose] using DyadicBivariateJetEnclosure.logCheck_sound hd (h.2 i)
  | contact i c B outer w bw =>
    exact DyadicBivariateJetEnclosure.contactCheck_sound hd (h.2 i)

theorem Op.check_soundAt {p : ℕ} (op : Op p) {boxes : List (DyadicBivariateJetEnclosure p)}
    {jets : List BivariateJet2} {out : DyadicBivariateJetEnclosure p} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t)
    (hc : op.check boxes out=true) : (op.eval jets).DirectionalSoundAt da dz t := by
  have hd := (Bool.and_eq_true_iff.mp hc).2
  cases op with
  | add i j => exact (hs i).add (hs j)
  | neg i => exact (hs i).neg
  | mul i j => exact (hs i).mul (hs j)
  | inv i =>
    have hp := DyadicBivariateJetEnclosure.invCheck_positive hd
    have hpos := DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact (hs i).inv hpos.ne'
  | log i wl wu =>
    have hp := DyadicBivariateJetEnclosure.logCheck_positive hd
    have hpos := DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact (hs i).log hpos.ne'
  | contact i c B outer w bw =>
    have hp := DyadicBivariateJetEnclosure.contactCheck_positive hd
    have hpos := DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact BivariateJet2.DirectionalSoundAt.outerCompose (reflectionContactJet_soundAt hpos) (hs i)

/-- Acceptance preserves enclosure semantics for every register. -/
theorem check_encloses {p : ℕ} (program : List (Instruction p)) {boxes : List (DyadicBivariateJetEnclosure p)}
    {jets : List BivariateJet2} {t : ℝ} (h : RegistersContain boxes jets t) (hc : check program boxes=true) :
    RegistersContain (finalBoxes program boxes) (finalJets program jets) t := by
  induction program generalizing boxes jets with
  | nil => exact h
  | cons ins rest ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    exact ih (h.cons (ins.op.check_encloses h hh.1)) hh.2

/-- Domain guards and input soundness also preserve the actual derivative chain. -/
theorem check_preserves_sound {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t) (hc : check program boxes=true) :
    RegistersSound (finalJets program jets) da dz t := by
  induction program generalizing boxes jets with
  | nil => exact hs
  | cons ins rest ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    exact ih (h.cons (ins.op.check_encloses h hh.1))
      (hs.cons (ins.op.check_soundAt h hs hh.1)) hh.2

theorem check_encloses_on {p : ℕ} (program : List (Instruction p)) {boxes : List (DyadicBivariateJetEnclosure p)}
    {jets : List BivariateJet2} {s : Set ℝ} (h : ∀ t ∈ s, RegistersContain boxes jets t)
    (hc : check program boxes=true) :
    ∀ t ∈ s, RegistersContain (finalBoxes program boxes) (finalJets program jets) t :=
  fun t ht => check_encloses program (h t ht) hc

theorem check_preserves_soundOn {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {s : Set ℝ} {da dz : ℝ}
    (h : ∀ t ∈ s, RegistersContain boxes jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz s)
    (hc : check program boxes=true) : ∀ i, ((finalJets program jets).getD i zeroJet).DirectionalSoundOn da dz s :=
  fun i t ht => check_preserves_sound program (h t ht) (fun i => hs i t ht) hc i


/-- Scalar semantics allow expression matching without expanding unused derivative fields. -/
noncomputable def Op.evalReal {p : ℕ} (op : Op p) (values : List ℝ) : ℝ := match op with
  | .add i j => values.getD i 0+values.getD j 0
  | .neg i => -values.getD i 0
  | .mul i j => values.getD i 0*values.getD j 0
  | .inv i => (values.getD i 0)⁻¹
  | .log i _ _ => Real.log (values.getD i 0)
  | .contact i _ _ _ _ _ => GeneralCK.Reflection.biasContact (values.getD i 0)

theorem value_getD (jets : List BivariateJet2) (i : ℕ) (t : ℝ) :
    (jets.getD i zeroJet).value t=(jets.map (fun j => j.value t)).getD i 0 := by
  induction jets generalizing i with
  | nil => simp [zeroJet,BivariateJet2.const]
  | cons j jets ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem Op.eval_value {p : ℕ} (op : Op p) (jets : List BivariateJet2) (t : ℝ) :
    (op.eval jets).value t=op.evalReal (jets.map (fun j => j.value t)) := by
  cases op <;> simp only [Op.eval,Op.evalReal,BivariateJet2.add,BivariateJet2.neg,BivariateJet2.mul,BivariateJet2.inv,BivariateJet2.log,
    BivariateJet2.outerCompose,reflectionContactJet,value_getD]

noncomputable def evalRealProgram {p : ℕ} : List (Instruction p) → List ℝ → List ℝ
  | [], values => values
  | ins :: rest, values => evalRealProgram rest (ins.op.evalReal values :: values)

theorem finalJets_values {p : ℕ} (program : List (Instruction p)) (jets : List BivariateJet2) (t : ℝ) :
    (finalJets program jets).map (fun j => j.value t)=
      evalRealProgram program (jets.map (fun j => j.value t)) := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,evalRealProgram,List.map_cons,Op.eval_value] using
      ih (ins.op.eval jets :: jets)

theorem finalJet_value {p : ℕ} (program : List (Instruction p)) (jets : List BivariateJet2) (i : ℕ) (t : ℝ) :
    ((finalJets program jets).getD i zeroJet).value t=
      (evalRealProgram program (jets.map (fun j => j.value t))).getD i 0 := by
  rw [value_getD,finalJets_values]


end GeneralCK.Certificates.BivariateJetProgram

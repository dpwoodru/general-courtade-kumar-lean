import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0688 : RatBall :=
  ⟨⟨47/160, -33/160⟩, 3/320⟩
def center0688 : GaussianRat :=
  ⟨205693537/1000000000, -132383201/1000000000⟩
def contact0688 : RatBall := localContactBall tau0688 center0688
def work0688 : RoundedTauEval :=
  evalTau precision tau0688 contact0688 logTwoBall

theorem center_sq0688 : (center0688.re : ℝ)^2 +
    (center0688.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0688]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0688 : work0688.theta.ok = true ∧
    work0688.jac.invOK = true ∧ acceptsUnitSq work0688.out = true := by
  norm_num [work0688, contact0688, tau0688, center0688, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0688 : CellCertificate where
  tauBall := tau0688
  contactCenter := center0688
  contactBall := contact0688
  work := work0688
  center_sq := center_sq0688
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0688.1
  jac_ok := checks0688.2.1
  accepted := checks0688.2.2

def tau0689 : RatBall :=
  ⟨⟨49/160, -37/160⟩, 3/320⟩
def center0689 : GaussianRat :=
  ⟨8639819/40000000, -36909857/250000000⟩
def contact0689 : RatBall := localContactBall tau0689 center0689
def work0689 : RoundedTauEval :=
  evalTau precision tau0689 contact0689 logTwoBall

theorem center_sq0689 : (center0689.re : ℝ)^2 +
    (center0689.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0689]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0689 : work0689.theta.ok = true ∧
    work0689.jac.invOK = true ∧ acceptsUnitSq work0689.out = true := by
  norm_num [work0689, contact0689, tau0689, center0689, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0689 : CellCertificate where
  tauBall := tau0689
  contactCenter := center0689
  contactBall := contact0689
  work := work0689
  center_sq := center_sq0689
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0689.1
  jac_ok := checks0689.2.1
  accepted := checks0689.2.2

def tau0690 : RatBall :=
  ⟨⟨49/160, -7/32⟩, 3/320⟩
def center0690 : GaussianRat :=
  ⟨26859619/125000000, -139498183/1000000000⟩
def contact0690 : RatBall := localContactBall tau0690 center0690
def work0690 : RoundedTauEval :=
  evalTau precision tau0690 contact0690 logTwoBall

theorem center_sq0690 : (center0690.re : ℝ)^2 +
    (center0690.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0690]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0690 : work0690.theta.ok = true ∧
    work0690.jac.invOK = true ∧ acceptsUnitSq work0690.out = true := by
  norm_num [work0690, contact0690, tau0690, center0690, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0690 : CellCertificate where
  tauBall := tau0690
  contactCenter := center0690
  contactBall := contact0690
  work := work0690
  center_sq := center_sq0690
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0690.1
  jac_ok := checks0690.2.1
  accepted := checks0690.2.2

def tau0691 : RatBall :=
  ⟨⟨51/160, -7/32⟩, 3/320⟩
def center0691 : GaussianRat :=
  ⟨111484361/500000000, -13840239/100000000⟩
def contact0691 : RatBall := localContactBall tau0691 center0691
def work0691 : RoundedTauEval :=
  evalTau precision tau0691 contact0691 logTwoBall

theorem center_sq0691 : (center0691.re : ℝ)^2 +
    (center0691.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0691]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0691 : work0691.theta.ok = true ∧
    work0691.jac.invOK = true ∧ acceptsUnitSq work0691.out = true := by
  norm_num [work0691, contact0691, tau0691, center0691, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0691 : CellCertificate where
  tauBall := tau0691
  contactCenter := center0691
  contactBall := contact0691
  work := work0691
  center_sq := center_sq0691
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0691.1
  jac_ok := checks0691.2.1
  accepted := checks0691.2.2

def tau0692 : RatBall :=
  ⟨⟨49/160, -33/160⟩, 3/320⟩
def center0692 : GaussianRat :=
  ⟨8553183/40000000, -26276749/200000000⟩
def contact0692 : RatBall := localContactBall tau0692 center0692
def work0692 : RoundedTauEval :=
  evalTau precision tau0692 contact0692 logTwoBall

theorem center_sq0692 : (center0692.re : ℝ)^2 +
    (center0692.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0692]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0692 : work0692.theta.ok = true ∧
    work0692.jac.invOK = true ∧ acceptsUnitSq work0692.out = true := by
  norm_num [work0692, contact0692, tau0692, center0692, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0692 : CellCertificate where
  tauBall := tau0692
  contactCenter := center0692
  contactBall := contact0692
  work := work0692
  center_sq := center_sq0692
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0692.1
  jac_ok := checks0692.2.1
  accepted := checks0692.2.2

def tau0693 : RatBall :=
  ⟨⟨51/160, -33/160⟩, 3/320⟩
def center0693 : GaussianRat :=
  ⟨13868507/62500000, -13035901/100000000⟩
def contact0693 : RatBall := localContactBall tau0693 center0693
def work0693 : RoundedTauEval :=
  evalTau precision tau0693 contact0693 logTwoBall

theorem center_sq0693 : (center0693.re : ℝ)^2 +
    (center0693.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0693]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0693 : work0693.theta.ok = true ∧
    work0693.jac.invOK = true ∧ acceptsUnitSq work0693.out = true := by
  norm_num [work0693, contact0693, tau0693, center0693, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0693 : CellCertificate where
  tauBall := tau0693
  contactCenter := center0693
  contactBall := contact0693
  work := work0693
  center_sq := center_sq0693
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0693.1
  jac_ok := checks0693.2.1
  accepted := checks0693.2.2

def tau0694 : RatBall :=
  ⟨⟨53/160, -33/160⟩, 3/320⟩
def center0694 : GaussianRat :=
  ⟨114945839/500000000, -32327639/250000000⟩
def contact0694 : RatBall := localContactBall tau0694 center0694
def work0694 : RoundedTauEval :=
  evalTau precision tau0694 contact0694 logTwoBall

theorem center_sq0694 : (center0694.re : ℝ)^2 +
    (center0694.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0694]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0694 : work0694.theta.ok = true ∧
    work0694.jac.invOK = true ∧ acceptsUnitSq work0694.out = true := by
  norm_num [work0694, contact0694, tau0694, center0694, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0694 : CellCertificate where
  tauBall := tau0694
  contactCenter := center0694
  contactBall := contact0694
  work := work0694
  center_sq := center_sq0694
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0694.1
  jac_ok := checks0694.2.1
  accepted := checks0694.2.2

def tau0695 : RatBall :=
  ⟨⟨37/160, -31/160⟩, 3/320⟩
def center0695 : GaussianRat :=
  ⟨163226979/1000000000, -128476919/1000000000⟩
def contact0695 : RatBall := localContactBall tau0695 center0695
def work0695 : RoundedTauEval :=
  evalTau precision tau0695 contact0695 logTwoBall

theorem center_sq0695 : (center0695.re : ℝ)^2 +
    (center0695.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0695]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0695 : work0695.theta.ok = true ∧
    work0695.jac.invOK = true ∧ acceptsUnitSq work0695.out = true := by
  norm_num [work0695, contact0695, tau0695, center0695, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
    localContactBall, localResidual, fixedPointImageBox, entropyBox,
    logTwoBall, oneBall, E8DerivativeBallEvaluator.twoBall,
    E8DerivativeBallEvaluator.fourBall, checkLogs, contactRadiusQ,
    squareRadiusQ, compress, floorGrid, ceilGrid,
    E8RoundedRatBall.add, E8RoundedRatBall.sub, E8RoundedRatBall.mul,
    E8RoundedRatBall.scale, E8RoundedRatBall.invAuto,
    RatBall.logOnePlus12, RatBall.logTaylor, RatBall.pow, RatBall.add,
    RatBall.sub, RatBall.neg, RatBall.mul, RatBall.scale, RatBall.divAuto,
    RatBall.invAuto, RatBall.inv, RatBall.invOK, acceptsUnitSq,
    RatBall.point, RatBall.zero, GaussianRat.add, GaussianRat.neg,
    GaussianRat.mul, GaussianRat.scale, GaussianRat.inv, GaussianRat.lower,
    GaussianRat.l1, Rat.floor_def, Rat.ceil]

def cell0695 : CellCertificate where
  tauBall := tau0695
  contactCenter := center0695
  contactBall := contact0695
  work := work0695
  center_sq := center_sq0695
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0695.1
  jac_ok := checks0695.2.1
  accepted := checks0695.2.2

def cells : List CellCertificate := [cell0688, cell0689, cell0690, cell0691, cell0692, cell0693, cell0694, cell0695]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086

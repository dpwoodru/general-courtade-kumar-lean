import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0128 : RatBall :=
  ⟨⟨3/80, -21/80⟩, 3/160⟩
def center0128 : GaussianRat :=
  ⟨27977261/1000000000, -186182371/1000000000⟩
def contact0128 : RatBall := localContactBall tau0128 center0128
def work0128 : RoundedTauEval :=
  evalTau precision tau0128 contact0128 logTwoBall

theorem center_sq0128 : (center0128.re : ℝ)^2 +
    (center0128.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0128]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0128 : work0128.theta.ok = true ∧
    work0128.jac.invOK = true ∧ acceptsUnitSq work0128.out = true := by
  norm_num [work0128, contact0128, tau0128, center0128, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0128 : CellCertificate where
  tauBall := tau0128
  contactCenter := center0128
  contactBall := contact0128
  work := work0128
  center_sq := center_sq0128
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0128.1
  jac_ok := checks0128.2.1
  accepted := checks0128.2.2

def tau0129 : RatBall :=
  ⟨⟨1/16, -21/80⟩, 3/160⟩
def center0129 : GaussianRat :=
  ⟨46572457/1000000000, -46409673/250000000⟩
def contact0129 : RatBall := localContactBall tau0129 center0129
def work0129 : RoundedTauEval :=
  evalTau precision tau0129 contact0129 logTwoBall

theorem center_sq0129 : (center0129.re : ℝ)^2 +
    (center0129.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0129]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0129 : work0129.theta.ok = true ∧
    work0129.jac.invOK = true ∧ acceptsUnitSq work0129.out = true := by
  norm_num [work0129, contact0129, tau0129, center0129, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0129 : CellCertificate where
  tauBall := tau0129
  contactCenter := center0129
  contactBall := contact0129
  work := work0129
  center_sq := center_sq0129
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0129.1
  jac_ok := checks0129.2.1
  accepted := checks0129.2.2

def tau0130 : RatBall :=
  ⟨⟨7/80, -21/80⟩, 3/160⟩
def center0130 : GaussianRat :=
  ⟨6508393/100000000, -184829567/1000000000⟩
def contact0130 : RatBall := localContactBall tau0130 center0130
def work0130 : RoundedTauEval :=
  evalTau precision tau0130 contact0130 logTwoBall

theorem center_sq0130 : (center0130.re : ℝ)^2 +
    (center0130.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0130]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0130 : work0130.theta.ok = true ∧
    work0130.jac.invOK = true ∧ acceptsUnitSq work0130.out = true := by
  norm_num [work0130, contact0130, tau0130, center0130, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0130 : CellCertificate where
  tauBall := tau0130
  contactCenter := center0130
  contactBall := contact0130
  work := work0130
  center_sq := center_sq0130
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0130.1
  jac_ok := checks0130.2.1
  accepted := checks0130.2.2

def tau0131 : RatBall :=
  ⟨⟨1/80, -19/80⟩, 3/160⟩
def center0131 : GaussianRat :=
  ⟨1150363/125000000, -41981661/250000000⟩
def contact0131 : RatBall := localContactBall tau0131 center0131
def work0131 : RoundedTauEval :=
  evalTau precision tau0131 contact0131 logTwoBall

theorem center_sq0131 : (center0131.re : ℝ)^2 +
    (center0131.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0131]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0131 : work0131.theta.ok = true ∧
    work0131.jac.invOK = true ∧ acceptsUnitSq work0131.out = true := by
  norm_num [work0131, contact0131, tau0131, center0131, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0131 : CellCertificate where
  tauBall := tau0131
  contactCenter := center0131
  contactBall := contact0131
  work := work0131
  center_sq := center_sq0131
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0131.1
  jac_ok := checks0131.2.1
  accepted := checks0131.2.2

def tau0132 : RatBall :=
  ⟨⟨3/80, -19/80⟩, 3/160⟩
def center0132 : GaussianRat :=
  ⟨551859/20000000, -167686167/1000000000⟩
def contact0132 : RatBall := localContactBall tau0132 center0132
def work0132 : RoundedTauEval :=
  evalTau precision tau0132 contact0132 logTwoBall

theorem center_sq0132 : (center0132.re : ℝ)^2 +
    (center0132.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0132]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0132 : work0132.theta.ok = true ∧
    work0132.jac.invOK = true ∧ acceptsUnitSq work0132.out = true := by
  norm_num [work0132, contact0132, tau0132, center0132, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0132 : CellCertificate where
  tauBall := tau0132
  contactCenter := center0132
  contactBall := contact0132
  work := work0132
  center_sq := center_sq0132
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0132.1
  jac_ok := checks0132.2.1
  accepted := checks0132.2.2

def tau0133 : RatBall :=
  ⟨⟨1/80, -17/80⟩, 3/160⟩
def center0133 : GaussianRat :=
  ⟨2272549/250000000, -14963863/100000000⟩
def contact0133 : RatBall := localContactBall tau0133 center0133
def work0133 : RoundedTauEval :=
  evalTau precision tau0133 contact0133 logTwoBall

theorem center_sq0133 : (center0133.re : ℝ)^2 +
    (center0133.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0133]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0133 : work0133.theta.ok = true ∧
    work0133.jac.invOK = true ∧ acceptsUnitSq work0133.out = true := by
  norm_num [work0133, contact0133, tau0133, center0133, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0133 : CellCertificate where
  tauBall := tau0133
  contactCenter := center0133
  contactBall := contact0133
  work := work0133
  center_sq := center_sq0133
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0133.1
  jac_ok := checks0133.2.1
  accepted := checks0133.2.2

def tau0134 : RatBall :=
  ⟨⟨3/80, -17/80⟩, 3/160⟩
def center0134 : GaussianRat :=
  ⟨13627917/500000000, -149428611/1000000000⟩
def contact0134 : RatBall := localContactBall tau0134 center0134
def work0134 : RoundedTauEval :=
  evalTau precision tau0134 contact0134 logTwoBall

theorem center_sq0134 : (center0134.re : ℝ)^2 +
    (center0134.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0134]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0134 : work0134.theta.ok = true ∧
    work0134.jac.invOK = true ∧ acceptsUnitSq work0134.out = true := by
  norm_num [work0134, contact0134, tau0134, center0134, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0134 : CellCertificate where
  tauBall := tau0134
  contactCenter := center0134
  contactBall := contact0134
  work := work0134
  center_sq := center_sq0134
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0134.1
  jac_ok := checks0134.2.1
  accepted := checks0134.2.2

def tau0135 : RatBall :=
  ⟨⟨1/16, -19/80⟩, 3/160⟩
def center0135 : GaussianRat :=
  ⟨45935893/1000000000, -836037/5000000⟩
def contact0135 : RatBall := localContactBall tau0135 center0135
def work0135 : RoundedTauEval :=
  evalTau precision tau0135 contact0135 logTwoBall

theorem center_sq0135 : (center0135.re : ℝ)^2 +
    (center0135.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0135]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0135 : work0135.theta.ok = true ∧
    work0135.jac.invOK = true ∧ acceptsUnitSq work0135.out = true := by
  norm_num [work0135, contact0135, tau0135, center0135, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0135 : CellCertificate where
  tauBall := tau0135
  contactCenter := center0135
  contactBall := contact0135
  work := work0135
  center_sq := center_sq0135
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0135.1
  jac_ok := checks0135.2.1
  accepted := checks0135.2.2

def cells : List CellCertificate := [cell0128, cell0129, cell0130, cell0131, cell0132, cell0133, cell0134, cell0135]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016

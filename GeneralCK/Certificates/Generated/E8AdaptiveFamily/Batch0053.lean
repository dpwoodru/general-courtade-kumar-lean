import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0424 : RatBall :=
  ⟨⟨-1/160, -53/160⟩, 3/320⟩
def center0424 : GaussianRat :=
  ⟨-611093/125000000, -238963881/1000000000⟩
def contact0424 : RatBall := localContactBall tau0424 center0424
def work0424 : RoundedTauEval :=
  evalTau precision tau0424 contact0424 logTwoBall

theorem center_sq0424 : (center0424.re : ℝ)^2 +
    (center0424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0424 : work0424.theta.ok = true ∧
    work0424.jac.invOK = true ∧ acceptsUnitSq work0424.out = true := by
  norm_num [work0424, contact0424, tau0424, center0424, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0424 : CellCertificate where
  tauBall := tau0424
  contactCenter := center0424
  contactBall := contact0424
  work := work0424
  center_sq := center_sq0424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0424.1
  jac_ok := checks0424.2.1
  accepted := checks0424.2.2

def tau0425 : RatBall :=
  ⟨⟨-7/160, -51/160⟩, 3/320⟩
def center0425 : GaussianRat :=
  ⟨-1693169/50000000, -228698347/1000000000⟩
def contact0425 : RatBall := localContactBall tau0425 center0425
def work0425 : RoundedTauEval :=
  evalTau precision tau0425 contact0425 logTwoBall

theorem center_sq0425 : (center0425.re : ℝ)^2 +
    (center0425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0425 : work0425.theta.ok = true ∧
    work0425.jac.invOK = true ∧ acceptsUnitSq work0425.out = true := by
  norm_num [work0425, contact0425, tau0425, center0425, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0425 : CellCertificate where
  tauBall := tau0425
  contactCenter := center0425
  contactBall := contact0425
  work := work0425
  center_sq := center_sq0425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0425.1
  jac_ok := checks0425.2.1
  accepted := checks0425.2.2

def tau0426 : RatBall :=
  ⟨⟨-1/32, -51/160⟩, 3/320⟩
def center0426 : GaussianRat :=
  ⟨-24200917/1000000000, -228965453/1000000000⟩
def contact0426 : RatBall := localContactBall tau0426 center0426
def work0426 : RoundedTauEval :=
  evalTau precision tau0426 contact0426 logTwoBall

theorem center_sq0426 : (center0426.re : ℝ)^2 +
    (center0426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0426 : work0426.theta.ok = true ∧
    work0426.jac.invOK = true ∧ acceptsUnitSq work0426.out = true := by
  norm_num [work0426, contact0426, tau0426, center0426, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0426 : CellCertificate where
  tauBall := tau0426
  contactCenter := center0426
  contactBall := contact0426
  work := work0426
  center_sq := center_sq0426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0426.1
  jac_ok := checks0426.2.1
  accepted := checks0426.2.2

def tau0427 : RatBall :=
  ⟨⟨-7/160, -49/160⟩, 3/320⟩
def center0427 : GaussianRat :=
  ⟨-16780473/500000000, -219087113/1000000000⟩
def contact0427 : RatBall := localContactBall tau0427 center0427
def work0427 : RoundedTauEval :=
  evalTau precision tau0427 contact0427 logTwoBall

theorem center_sq0427 : (center0427.re : ℝ)^2 +
    (center0427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0427 : work0427.theta.ok = true ∧
    work0427.jac.invOK = true ∧ acceptsUnitSq work0427.out = true := by
  norm_num [work0427, contact0427, tau0427, center0427, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0427 : CellCertificate where
  tauBall := tau0427
  contactCenter := center0427
  contactBall := contact0427
  work := work0427
  center_sq := center_sq0427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0427.1
  jac_ok := checks0427.2.1
  accepted := checks0427.2.2

def tau0428 : RatBall :=
  ⟨⟨-1/32, -49/160⟩, 3/320⟩
def center0428 : GaussianRat :=
  ⟨-2398433/100000000, -219339251/1000000000⟩
def contact0428 : RatBall := localContactBall tau0428 center0428
def work0428 : RoundedTauEval :=
  evalTau precision tau0428 contact0428 logTwoBall

theorem center_sq0428 : (center0428.re : ℝ)^2 +
    (center0428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0428 : work0428.theta.ok = true ∧
    work0428.jac.invOK = true ∧ acceptsUnitSq work0428.out = true := by
  norm_num [work0428, contact0428, tau0428, center0428, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0428 : CellCertificate where
  tauBall := tau0428
  contactCenter := center0428
  contactBall := contact0428
  work := work0428
  center_sq := center_sq0428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0428.1
  jac_ok := checks0428.2.1
  accepted := checks0428.2.2

def tau0429 : RatBall :=
  ⟨⟨-3/160, -51/160⟩, 3/320⟩
def center0429 : GaussianRat :=
  ⟨-581027/40000000, -57285979/250000000⟩
def contact0429 : RatBall := localContactBall tau0429 center0429
def work0429 : RoundedTauEval :=
  evalTau precision tau0429 contact0429 logTwoBall

theorem center_sq0429 : (center0429.re : ℝ)^2 +
    (center0429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0429 : work0429.theta.ok = true ∧
    work0429.jac.invOK = true ∧ acceptsUnitSq work0429.out = true := by
  norm_num [work0429, contact0429, tau0429, center0429, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0429 : CellCertificate where
  tauBall := tau0429
  contactCenter := center0429
  contactBall := contact0429
  work := work0429
  center_sq := center_sq0429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0429.1
  jac_ok := checks0429.2.1
  accepted := checks0429.2.2

def tau0430 : RatBall :=
  ⟨⟨-1/160, -51/160⟩, 3/320⟩
def center0430 : GaussianRat :=
  ⟨-4842747/1000000000, -45846653/200000000⟩
def contact0430 : RatBall := localContactBall tau0430 center0430
def work0430 : RoundedTauEval :=
  evalTau precision tau0430 contact0430 logTwoBall

theorem center_sq0430 : (center0430.re : ℝ)^2 +
    (center0430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0430 : work0430.theta.ok = true ∧
    work0430.jac.invOK = true ∧ acceptsUnitSq work0430.out = true := by
  norm_num [work0430, contact0430, tau0430, center0430, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0430 : CellCertificate where
  tauBall := tau0430
  contactCenter := center0430
  contactBall := contact0430
  work := work0430
  center_sq := center_sq0430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0430.1
  jac_ok := checks0430.2.1
  accepted := checks0430.2.2

def tau0431 : RatBall :=
  ⟨⟨-3/160, -49/160⟩, 3/320⟩
def center0431 : GaussianRat :=
  ⟨-14395497/1000000000, -27438463/125000000⟩
def contact0431 : RatBall := localContactBall tau0431 center0431
def work0431 : RoundedTauEval :=
  evalTau precision tau0431 contact0431 logTwoBall

theorem center_sq0431 : (center0431.re : ℝ)^2 +
    (center0431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0431 : work0431.theta.ok = true ∧
    work0431.jac.invOK = true ∧ acceptsUnitSq work0431.out = true := by
  norm_num [work0431, contact0431, tau0431, center0431, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0431 : CellCertificate where
  tauBall := tau0431
  contactCenter := center0431
  contactBall := contact0431
  work := work0431
  center_sq := center_sq0431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0431.1
  jac_ok := checks0431.2.1
  accepted := checks0431.2.2

def cells : List CellCertificate := [cell0424, cell0425, cell0426, cell0427, cell0428, cell0429, cell0430, cell0431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053

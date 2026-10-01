import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0058

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0464 : RatBall :=
  ⟨⟨-17/160, -41/160⟩, 3/320⟩
def center0464 : GaussianRat :=
  ⟨-1572299/20000000, -179469913/1000000000⟩
def contact0464 : RatBall := localContactBall tau0464 center0464
def work0464 : RoundedTauEval :=
  evalTau precision tau0464 contact0464 logTwoBall

theorem center_sq0464 : (center0464.re : ℝ)^2 +
    (center0464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0464 : work0464.theta.ok = true ∧
    work0464.jac.invOK = true ∧ acceptsUnitSq work0464.out = true := by
  norm_num [work0464, contact0464, tau0464, center0464, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0464 : CellCertificate where
  tauBall := tau0464
  contactCenter := center0464
  contactBall := contact0464
  work := work0464
  center_sq := center_sq0464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0464.1
  jac_ok := checks0464.2.1
  accepted := checks0464.2.2

def tau0465 : RatBall :=
  ⟨⟨-31/160, -39/160⟩, 3/320⟩
def center0465 : GaussianRat :=
  ⟨-2814451/20000000, -33084071/200000000⟩
def contact0465 : RatBall := localContactBall tau0465 center0465
def work0465 : RoundedTauEval :=
  evalTau precision tau0465 contact0465 logTwoBall

theorem center_sq0465 : (center0465.re : ℝ)^2 +
    (center0465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0465 : work0465.theta.ok = true ∧
    work0465.jac.invOK = true ∧ acceptsUnitSq work0465.out = true := by
  norm_num [work0465, contact0465, tau0465, center0465, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0465 : CellCertificate where
  tauBall := tau0465
  contactCenter := center0465
  contactBall := contact0465
  work := work0465
  center_sq := center_sq0465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0465.1
  jac_ok := checks0465.2.1
  accepted := checks0465.2.2

def tau0466 : RatBall :=
  ⟨⟨-29/160, -39/160⟩, 3/320⟩
def center0466 : GaussianRat :=
  ⟨-131916433/1000000000, -83139101/500000000⟩
def contact0466 : RatBall := localContactBall tau0466 center0466
def work0466 : RoundedTauEval :=
  evalTau precision tau0466 contact0466 logTwoBall

theorem center_sq0466 : (center0466.re : ℝ)^2 +
    (center0466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0466 : work0466.theta.ok = true ∧
    work0466.jac.invOK = true ∧ acceptsUnitSq work0466.out = true := by
  norm_num [work0466, contact0466, tau0466, center0466, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0466 : CellCertificate where
  tauBall := tau0466
  contactCenter := center0466
  contactBall := contact0466
  work := work0466
  center_sq := center_sq0466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0466.1
  jac_ok := checks0466.2.1
  accepted := checks0466.2.2

def tau0467 : RatBall :=
  ⟨⟨-31/160, -37/160⟩, 3/320⟩
def center0467 : GaussianRat :=
  ⟨-139868391/1000000000, -78332251/500000000⟩
def contact0467 : RatBall := localContactBall tau0467 center0467
def work0467 : RoundedTauEval :=
  evalTau precision tau0467 contact0467 logTwoBall

theorem center_sq0467 : (center0467.re : ℝ)^2 +
    (center0467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0467 : work0467.theta.ok = true ∧
    work0467.jac.invOK = true ∧ acceptsUnitSq work0467.out = true := by
  norm_num [work0467, contact0467, tau0467, center0467, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0467 : CellCertificate where
  tauBall := tau0467
  contactCenter := center0467
  contactBall := contact0467
  work := work0467
  center_sq := center_sq0467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0467.1
  jac_ok := checks0467.2.1
  accepted := checks0467.2.2

def tau0468 : RatBall :=
  ⟨⟨-29/160, -37/160⟩, 3/320⟩
def center0468 : GaussianRat :=
  ⟨-8194291/62500000, -7873457/50000000⟩
def contact0468 : RatBall := localContactBall tau0468 center0468
def work0468 : RoundedTauEval :=
  evalTau precision tau0468 contact0468 logTwoBall

theorem center_sq0468 : (center0468.re : ℝ)^2 +
    (center0468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0468 : work0468.theta.ok = true ∧
    work0468.jac.invOK = true ∧ acceptsUnitSq work0468.out = true := by
  norm_num [work0468, contact0468, tau0468, center0468, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0468 : CellCertificate where
  tauBall := tau0468
  contactCenter := center0468
  contactBall := contact0468
  work := work0468
  center_sq := center_sq0468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0468.1
  jac_ok := checks0468.2.1
  accepted := checks0468.2.2

def tau0469 : RatBall :=
  ⟨⟨-27/160, -39/160⟩, 3/320⟩
def center0469 : GaussianRat :=
  ⟨-123057717/1000000000, -167087407/1000000000⟩
def contact0469 : RatBall := localContactBall tau0469 center0469
def work0469 : RoundedTauEval :=
  evalTau precision tau0469 contact0469 logTwoBall

theorem center_sq0469 : (center0469.re : ℝ)^2 +
    (center0469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0469 : work0469.theta.ok = true ∧
    work0469.jac.invOK = true ∧ acceptsUnitSq work0469.out = true := by
  norm_num [work0469, contact0469, tau0469, center0469, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0469 : CellCertificate where
  tauBall := tau0469
  contactCenter := center0469
  contactBall := contact0469
  work := work0469
  center_sq := center_sq0469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0469.1
  jac_ok := checks0469.2.1
  accepted := checks0469.2.2

def tau0470 : RatBall :=
  ⟨⟨-5/32, -39/160⟩, 3/320⟩
def center0470 : GaussianRat :=
  ⟨-57074691/500000000, -83923163/500000000⟩
def contact0470 : RatBall := localContactBall tau0470 center0470
def work0470 : RoundedTauEval :=
  evalTau precision tau0470 contact0470 logTwoBall

theorem center_sq0470 : (center0470.re : ℝ)^2 +
    (center0470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0470 : work0470.theta.ok = true ∧
    work0470.jac.invOK = true ∧ acceptsUnitSq work0470.out = true := by
  norm_num [work0470, contact0470, tau0470, center0470, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0470 : CellCertificate where
  tauBall := tau0470
  contactCenter := center0470
  contactBall := contact0470
  work := work0470
  center_sq := center_sq0470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0470.1
  jac_ok := checks0470.2.1
  accepted := checks0470.2.2

def tau0471 : RatBall :=
  ⟨⟨-27/160, -37/160⟩, 3/320⟩
def center0471 : GaussianRat :=
  ⟨-122297939/1000000000, -158228017/1000000000⟩
def contact0471 : RatBall := localContactBall tau0471 center0471
def work0471 : RoundedTauEval :=
  evalTau precision tau0471 contact0471 logTwoBall

theorem center_sq0471 : (center0471.re : ℝ)^2 +
    (center0471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0471 : work0471.theta.ok = true ∧
    work0471.jac.invOK = true ∧ acceptsUnitSq work0471.out = true := by
  norm_num [work0471, contact0471, tau0471, center0471, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0471 : CellCertificate where
  tauBall := tau0471
  contactCenter := center0471
  contactBall := contact0471
  work := work0471
  center_sq := center_sq0471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0471.1
  jac_ok := checks0471.2.1
  accepted := checks0471.2.2

def cells : List CellCertificate := [cell0464, cell0465, cell0466, cell0467, cell0468, cell0469, cell0470, cell0471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0058

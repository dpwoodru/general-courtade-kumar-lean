import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2544 : RatBall :=
  ⟨⟨73/320, 101/320⟩, 3/640⟩
def center2544 : GaussianRat :=
  ⟨85759271/500000000, 26642441/125000000⟩
def contact2544 : RatBall := localContactBall tau2544 center2544
def work2544 : RoundedTauEval :=
  evalTau precision tau2544 contact2544 logTwoBall

theorem center_sq2544 : (center2544.re : ℝ)^2 +
    (center2544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2544 : work2544.theta.ok = true ∧
    work2544.jac.invOK = true ∧ acceptsUnitSq work2544.out = true := by
  norm_num [work2544, contact2544, tau2544, center2544, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2544 : CellCertificate where
  tauBall := tau2544
  contactCenter := center2544
  contactBall := contact2544
  work := work2544
  center_sq := center_sq2544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2544.1
  jac_ok := checks2544.2.1
  accepted := checks2544.2.2

def tau2545 : RatBall :=
  ⟨⟨15/64, 101/320⟩, 3/640⟩
def center2545 : GaussianRat :=
  ⟨21994767/125000000, 212432751/1000000000⟩
def contact2545 : RatBall := localContactBall tau2545 center2545
def work2545 : RoundedTauEval :=
  evalTau precision tau2545 contact2545 logTwoBall

theorem center_sq2545 : (center2545.re : ℝ)^2 +
    (center2545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2545 : work2545.theta.ok = true ∧
    work2545.jac.invOK = true ∧ acceptsUnitSq work2545.out = true := by
  norm_num [work2545, contact2545, tau2545, center2545, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2545 : CellCertificate where
  tauBall := tau2545
  contactCenter := center2545
  contactBall := contact2545
  work := work2545
  center_sq := center_sq2545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2545.1
  jac_ok := checks2545.2.1
  accepted := checks2545.2.2

def tau2546 : RatBall :=
  ⟨⟨73/320, 103/320⟩, 3/640⟩
def center2546 : GaussianRat :=
  ⟨34445579/200000000, 217595773/1000000000⟩
def contact2546 : RatBall := localContactBall tau2546 center2546
def work2546 : RoundedTauEval :=
  evalTau precision tau2546 contact2546 logTwoBall

theorem center_sq2546 : (center2546.re : ℝ)^2 +
    (center2546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2546 : work2546.theta.ok = true ∧
    work2546.jac.invOK = true ∧ acceptsUnitSq work2546.out = true := by
  norm_num [work2546, contact2546, tau2546, center2546, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2546 : CellCertificate where
  tauBall := tau2546
  contactCenter := center2546
  contactBall := contact2546
  work := work2546
  center_sq := center_sq2546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2546.1
  jac_ok := checks2546.2.1
  accepted := checks2546.2.2

def tau2547 : RatBall :=
  ⟨⟨15/64, 103/320⟩, 3/640⟩
def center2547 : GaussianRat :=
  ⟨44170389/250000000, 43373931/200000000⟩
def contact2547 : RatBall := localContactBall tau2547 center2547
def work2547 : RoundedTauEval :=
  evalTau precision tau2547 contact2547 logTwoBall

theorem center_sq2547 : (center2547.re : ℝ)^2 +
    (center2547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2547 : work2547.theta.ok = true ∧
    work2547.jac.invOK = true ∧ acceptsUnitSq work2547.out = true := by
  norm_num [work2547, contact2547, tau2547, center2547, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2547 : CellCertificate where
  tauBall := tau2547
  contactCenter := center2547
  contactBall := contact2547
  work := work2547
  center_sq := center_sq2547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2547.1
  jac_ok := checks2547.2.1
  accepted := checks2547.2.2

def tau2548 : RatBall :=
  ⟨⟨77/320, 101/320⟩, 3/640⟩
def center2548 : GaussianRat :=
  ⟨45094603/250000000, 105856123/500000000⟩
def contact2548 : RatBall := localContactBall tau2548 center2548
def work2548 : RoundedTauEval :=
  evalTau precision tau2548 contact2548 logTwoBall

theorem center_sq2548 : (center2548.re : ℝ)^2 +
    (center2548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2548 : work2548.theta.ok = true ∧
    work2548.jac.invOK = true ∧ acceptsUnitSq work2548.out = true := by
  norm_num [work2548, contact2548, tau2548, center2548, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2548 : CellCertificate where
  tauBall := tau2548
  contactCenter := center2548
  contactBall := contact2548
  work := work2548
  center_sq := center_sq2548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2548.1
  jac_ok := checks2548.2.1
  accepted := checks2548.2.2

def tau2549 : RatBall :=
  ⟨⟨79/320, 101/320⟩, 3/640⟩
def center2549 : GaussianRat :=
  ⟨92389531/500000000, 210978373/1000000000⟩
def contact2549 : RatBall := localContactBall tau2549 center2549
def work2549 : RoundedTauEval :=
  evalTau precision tau2549 contact2549 logTwoBall

theorem center_sq2549 : (center2549.re : ℝ)^2 +
    (center2549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2549 : work2549.theta.ok = true ∧
    work2549.jac.invOK = true ∧ acceptsUnitSq work2549.out = true := by
  norm_num [work2549, contact2549, tau2549, center2549, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2549 : CellCertificate where
  tauBall := tau2549
  contactCenter := center2549
  contactBall := contact2549
  work := work2549
  center_sq := center_sq2549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2549.1
  jac_ok := checks2549.2.1
  accepted := checks2549.2.2

def tau2550 : RatBall :=
  ⟨⟨77/320, 103/320⟩, 3/640⟩
def center2550 : GaussianRat :=
  ⟨36223107/200000000, 108064747/500000000⟩
def contact2550 : RatBall := localContactBall tau2550 center2550
def work2550 : RoundedTauEval :=
  evalTau precision tau2550 contact2550 logTwoBall

theorem center_sq2550 : (center2550.re : ℝ)^2 +
    (center2550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2550 : work2550.theta.ok = true ∧
    work2550.jac.invOK = true ∧ acceptsUnitSq work2550.out = true := by
  norm_num [work2550, contact2550, tau2550, center2550, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2550 : CellCertificate where
  tauBall := tau2550
  contactCenter := center2550
  contactBall := contact2550
  work := work2550
  center_sq := center_sq2550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2550.1
  jac_ok := checks2550.2.1
  accepted := checks2550.2.2

def tau2551 : RatBall :=
  ⟨⟨13/64, 21/64⟩, 3/640⟩
def center2551 : GaussianRat :=
  ⟨30978099/200000000, 224898511/1000000000⟩
def contact2551 : RatBall := localContactBall tau2551 center2551
def work2551 : RoundedTauEval :=
  evalTau precision tau2551 contact2551 logTwoBall

theorem center_sq2551 : (center2551.re : ℝ)^2 +
    (center2551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2551 : work2551.theta.ok = true ∧
    work2551.jac.invOK = true ∧ acceptsUnitSq work2551.out = true := by
  norm_num [work2551, contact2551, tau2551, center2551, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2551 : CellCertificate where
  tauBall := tau2551
  contactCenter := center2551
  contactBall := contact2551
  work := work2551
  center_sq := center_sq2551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2551.1
  jac_ok := checks2551.2.1
  accepted := checks2551.2.2

def cells : List CellCertificate := [cell2544, cell2545, cell2546, cell2547, cell2548, cell2549, cell2550, cell2551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0318

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2480 : RatBall :=
  ⟨⟨81/320, 93/320⟩, 3/640⟩
def center2480 : GaussianRat :=
  ⟨93152319/500000000, 24105877/125000000⟩
def contact2480 : RatBall := localContactBall tau2480 center2480
def work2480 : RoundedTauEval :=
  evalTau precision tau2480 contact2480 logTwoBall

theorem center_sq2480 : (center2480.re : ℝ)^2 +
    (center2480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2480 : work2480.theta.ok = true ∧
    work2480.jac.invOK = true ∧ acceptsUnitSq work2480.out = true := by
  norm_num [work2480, contact2480, tau2480, center2480, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2480 : CellCertificate where
  tauBall := tau2480
  contactCenter := center2480
  contactBall := contact2480
  work := work2480
  center_sq := center_sq2480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2480.1
  jac_ok := checks2480.2.1
  accepted := checks2480.2.2

def tau2481 : RatBall :=
  ⟨⟨83/320, 93/320⟩, 3/640⟩
def center2481 : GaussianRat :=
  ⟨95308733/500000000, 192166077/1000000000⟩
def contact2481 : RatBall := localContactBall tau2481 center2481
def work2481 : RoundedTauEval :=
  evalTau precision tau2481 contact2481 logTwoBall

theorem center_sq2481 : (center2481.re : ℝ)^2 +
    (center2481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2481 : work2481.theta.ok = true ∧
    work2481.jac.invOK = true ∧ acceptsUnitSq work2481.out = true := by
  norm_num [work2481, contact2481, tau2481, center2481, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2481 : CellCertificate where
  tauBall := tau2481
  contactCenter := center2481
  contactBall := contact2481
  work := work2481
  center_sq := center_sq2481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2481.1
  jac_ok := checks2481.2.1
  accepted := checks2481.2.2

def tau2482 : RatBall :=
  ⟨⟨81/320, 19/64⟩, 3/640⟩
def center2482 : GaussianRat :=
  ⟨186989333/1000000000, 49293783/250000000⟩
def contact2482 : RatBall := localContactBall tau2482 center2482
def work2482 : RoundedTauEval :=
  evalTau precision tau2482 contact2482 logTwoBall

theorem center_sq2482 : (center2482.re : ℝ)^2 +
    (center2482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2482]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2482 : work2482.theta.ok = true ∧
    work2482.jac.invOK = true ∧ acceptsUnitSq work2482.out = true := by
  norm_num [work2482, contact2482, tau2482, center2482, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2482 : CellCertificate where
  tauBall := tau2482
  contactCenter := center2482
  contactBall := contact2482
  work := work2482
  center_sq := center_sq2482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2482.1
  jac_ok := checks2482.2.1
  accepted := checks2482.2.2

def tau2483 : RatBall :=
  ⟨⟨83/320, 19/64⟩, 3/640⟩
def center2483 : GaussianRat :=
  ⟨191313683/1000000000, 3929501/20000000⟩
def contact2483 : RatBall := localContactBall tau2483 center2483
def work2483 : RoundedTauEval :=
  evalTau precision tau2483 contact2483 logTwoBall

theorem center_sq2483 : (center2483.re : ℝ)^2 +
    (center2483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2483 : work2483.theta.ok = true ∧
    work2483.jac.invOK = true ∧ acceptsUnitSq work2483.out = true := by
  norm_num [work2483, contact2483, tau2483, center2483, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2483 : CellCertificate where
  tauBall := tau2483
  contactCenter := center2483
  contactBall := contact2483
  work := work2483
  center_sq := center_sq2483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2483.1
  jac_ok := checks2483.2.1
  accepted := checks2483.2.2

def tau2484 : RatBall :=
  ⟨⟨17/64, 93/320⟩, 3/640⟩
def center2484 : GaussianRat :=
  ⟨97455589/500000000, 191473909/1000000000⟩
def contact2484 : RatBall := localContactBall tau2484 center2484
def work2484 : RoundedTauEval :=
  evalTau precision tau2484 contact2484 logTwoBall

theorem center_sq2484 : (center2484.re : ℝ)^2 +
    (center2484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2484 : work2484.theta.ok = true ∧
    work2484.jac.invOK = true ∧ acceptsUnitSq work2484.out = true := by
  norm_num [work2484, contact2484, tau2484, center2484, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2484 : CellCertificate where
  tauBall := tau2484
  contactCenter := center2484
  contactBall := contact2484
  work := work2484
  center_sq := center_sq2484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2484.1
  jac_ok := checks2484.2.1
  accepted := checks2484.2.2

def tau2485 : RatBall :=
  ⟨⟨87/320, 93/320⟩, 3/640⟩
def center2485 : GaussianRat :=
  ⟨2489819/12500000, 47692707/250000000⟩
def contact2485 : RatBall := localContactBall tau2485 center2485
def work2485 : RoundedTauEval :=
  evalTau precision tau2485 contact2485 logTwoBall

theorem center_sq2485 : (center2485.re : ℝ)^2 +
    (center2485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2485 : work2485.theta.ok = true ∧
    work2485.jac.invOK = true ∧ acceptsUnitSq work2485.out = true := by
  norm_num [work2485, contact2485, tau2485, center2485, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2485 : CellCertificate where
  tauBall := tau2485
  contactCenter := center2485
  contactBall := contact2485
  work := work2485
  center_sq := center_sq2485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2485.1
  jac_ok := checks2485.2.1
  accepted := checks2485.2.2

def tau2486 : RatBall :=
  ⟨⟨17/64, 19/64⟩, 3/640⟩
def center2486 : GaussianRat :=
  ⟨39123719/200000000, 48940869/250000000⟩
def contact2486 : RatBall := localContactBall tau2486 center2486
def work2486 : RoundedTauEval :=
  evalTau precision tau2486 contact2486 logTwoBall

theorem center_sq2486 : (center2486.re : ℝ)^2 +
    (center2486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2486 : work2486.theta.ok = true ∧
    work2486.jac.invOK = true ∧ acceptsUnitSq work2486.out = true := by
  norm_num [work2486, contact2486, tau2486, center2486, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2486 : CellCertificate where
  tauBall := tau2486
  contactCenter := center2486
  contactBall := contact2486
  work := work2486
  center_sq := center_sq2486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2486.1
  jac_ok := checks2486.2.1
  accepted := checks2486.2.2

def tau2487 : RatBall :=
  ⟨⟨87/320, 19/64⟩, 3/640⟩
def center2487 : GaussianRat :=
  ⟨199903813/1000000000, 195040739/1000000000⟩
def contact2487 : RatBall := localContactBall tau2487 center2487
def work2487 : RoundedTauEval :=
  evalTau precision tau2487 contact2487 logTwoBall

theorem center_sq2487 : (center2487.re : ℝ)^2 +
    (center2487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2487 : work2487.theta.ok = true ∧
    work2487.jac.invOK = true ∧ acceptsUnitSq work2487.out = true := by
  norm_num [work2487, contact2487, tau2487, center2487, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2487 : CellCertificate where
  tauBall := tau2487
  contactCenter := center2487
  contactBall := contact2487
  work := work2487
  center_sq := center_sq2487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2487.1
  jac_ok := checks2487.2.1
  accepted := checks2487.2.2

def cells : List CellCertificate := [cell2480, cell2481, cell2482, cell2483, cell2484, cell2485, cell2486, cell2487]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2504 : RatBall :=
  ⟨⟨101/320, 15/64⟩, 3/640⟩
def center2504 : GaussianRat :=
  ⟨13899213/62500000, 2975829/20000000⟩
def contact2504 : RatBall := localContactBall tau2504 center2504
def work2504 : RoundedTauEval :=
  evalTau precision tau2504 contact2504 logTwoBall

theorem center_sq2504 : (center2504.re : ℝ)^2 +
    (center2504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2504 : work2504.theta.ok = true ∧
    work2504.jac.invOK = true ∧ acceptsUnitSq work2504.out = true := by
  norm_num [work2504, contact2504, tau2504, center2504, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2504 : CellCertificate where
  tauBall := tau2504
  contactCenter := center2504
  contactBall := contact2504
  work := work2504
  center_sq := center_sq2504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2504.1
  jac_ok := checks2504.2.1
  accepted := checks2504.2.2

def tau2505 : RatBall :=
  ⟨⟨103/320, 15/64⟩, 3/640⟩
def center2505 : GaussianRat :=
  ⟨14151969/62500000, 148191091/1000000000⟩
def contact2505 : RatBall := localContactBall tau2505 center2505
def work2505 : RoundedTauEval :=
  evalTau precision tau2505 contact2505 logTwoBall

theorem center_sq2505 : (center2505.re : ℝ)^2 +
    (center2505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2505 : work2505.theta.ok = true ∧
    work2505.jac.invOK = true ∧ acceptsUnitSq work2505.out = true := by
  norm_num [work2505, contact2505, tau2505, center2505, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2505 : CellCertificate where
  tauBall := tau2505
  contactCenter := center2505
  contactBall := contact2505
  work := work2505
  center_sq := center_sq2505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2505.1
  jac_ok := checks2505.2.1
  accepted := checks2505.2.2

def tau2506 : RatBall :=
  ⟨⟨97/320, 77/320⟩, 3/640⟩
def center2506 : GaussianRat :=
  ⟨10741779/50000000, 300909/1953125⟩
def contact2506 : RatBall := localContactBall tau2506 center2506
def work2506 : RoundedTauEval :=
  evalTau precision tau2506 contact2506 logTwoBall

theorem center_sq2506 : (center2506.re : ℝ)^2 +
    (center2506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2506 : work2506.theta.ok = true ∧
    work2506.jac.invOK = true ∧ acceptsUnitSq work2506.out = true := by
  norm_num [work2506, contact2506, tau2506, center2506, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2506 : CellCertificate where
  tauBall := tau2506
  contactCenter := center2506
  contactBall := contact2506
  work := work2506
  center_sq := center_sq2506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2506.1
  jac_ok := checks2506.2.1
  accepted := checks2506.2.2

def tau2507 : RatBall :=
  ⟨⟨99/320, 77/320⟩, 3/640⟩
def center2507 : GaussianRat :=
  ⟨218923989/1000000000, 38365123/250000000⟩
def contact2507 : RatBall := localContactBall tau2507 center2507
def work2507 : RoundedTauEval :=
  evalTau precision tau2507 contact2507 logTwoBall

theorem center_sq2507 : (center2507.re : ℝ)^2 +
    (center2507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2507 : work2507.theta.ok = true ∧
    work2507.jac.invOK = true ∧ acceptsUnitSq work2507.out = true := by
  norm_num [work2507, contact2507, tau2507, center2507, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2507 : CellCertificate where
  tauBall := tau2507
  contactCenter := center2507
  contactBall := contact2507
  work := work2507
  center_sq := center_sq2507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2507.1
  jac_ok := checks2507.2.1
  accepted := checks2507.2.2

def tau2508 : RatBall :=
  ⟨⟨97/320, 79/320⟩, 3/640⟩
def center2508 : GaussianRat :=
  ⟨215446071/1000000000, 158166863/1000000000⟩
def contact2508 : RatBall := localContactBall tau2508 center2508
def work2508 : RoundedTauEval :=
  evalTau precision tau2508 contact2508 logTwoBall

theorem center_sq2508 : (center2508.re : ℝ)^2 +
    (center2508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2508 : work2508.theta.ok = true ∧
    work2508.jac.invOK = true ∧ acceptsUnitSq work2508.out = true := by
  norm_num [work2508, contact2508, tau2508, center2508, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2508 : CellCertificate where
  tauBall := tau2508
  contactCenter := center2508
  contactBall := contact2508
  work := work2508
  center_sq := center_sq2508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2508.1
  jac_ok := checks2508.2.1
  accepted := checks2508.2.2

def tau2509 : RatBall :=
  ⟨⟨99/320, 79/320⟩, 3/640⟩
def center2509 : GaussianRat :=
  ⟨109770971/500000000, 78771627/500000000⟩
def contact2509 : RatBall := localContactBall tau2509 center2509
def work2509 : RoundedTauEval :=
  evalTau precision tau2509 contact2509 logTwoBall

theorem center_sq2509 : (center2509.re : ℝ)^2 +
    (center2509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2509]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2509 : work2509.theta.ok = true ∧
    work2509.jac.invOK = true ∧ acceptsUnitSq work2509.out = true := by
  norm_num [work2509, contact2509, tau2509, center2509, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2509 : CellCertificate where
  tauBall := tau2509
  contactCenter := center2509
  contactBall := contact2509
  work := work2509
  center_sq := center_sq2509
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2509.1
  jac_ok := checks2509.2.1
  accepted := checks2509.2.2

def tau2510 : RatBall :=
  ⟨⟨101/320, 77/320⟩, 3/640⟩
def center2510 : GaussianRat :=
  ⟨111496867/500000000, 152848327/1000000000⟩
def contact2510 : RatBall := localContactBall tau2510 center2510
def work2510 : RoundedTauEval :=
  evalTau precision tau2510 contact2510 logTwoBall

theorem center_sq2510 : (center2510.re : ℝ)^2 +
    (center2510.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2510]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2510 : work2510.theta.ok = true ∧
    work2510.jac.invOK = true ∧ acceptsUnitSq work2510.out = true := by
  norm_num [work2510, contact2510, tau2510, center2510, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2510 : CellCertificate where
  tauBall := tau2510
  contactCenter := center2510
  contactBall := contact2510
  work := work2510
  center_sq := center_sq2510
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2510.1
  jac_ok := checks2510.2.1
  accepted := checks2510.2.2

def tau2511 : RatBall :=
  ⟨⟨103/320, 77/320⟩, 3/640⟩
def center2511 : GaussianRat :=
  ⟨113522317/500000000, 152229153/1000000000⟩
def contact2511 : RatBall := localContactBall tau2511 center2511
def work2511 : RoundedTauEval :=
  evalTau precision tau2511 contact2511 logTwoBall

theorem center_sq2511 : (center2511.re : ℝ)^2 +
    (center2511.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2511]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2511 : work2511.theta.ok = true ∧
    work2511.jac.invOK = true ∧ acceptsUnitSq work2511.out = true := by
  norm_num [work2511, contact2511, tau2511, center2511, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2511 : CellCertificate where
  tauBall := tau2511
  contactCenter := center2511
  contactBall := contact2511
  work := work2511
  center_sq := center_sq2511
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2511.1
  jac_ok := checks2511.2.1
  accepted := checks2511.2.2

def cells : List CellCertificate := [cell2504, cell2505, cell2506, cell2507, cell2508, cell2509, cell2510, cell2511]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2344 : RatBall :=
  ⟨⟨49/320, 101/320⟩, 3/640⟩
def center2344 : GaussianRat :=
  ⟨3652061/31250000, 220423219/1000000000⟩
def contact2344 : RatBall := localContactBall tau2344 center2344
def work2344 : RoundedTauEval :=
  evalTau precision tau2344 contact2344 logTwoBall

theorem center_sq2344 : (center2344.re : ℝ)^2 +
    (center2344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2344 : work2344.theta.ok = true ∧
    work2344.jac.invOK = true ∧ acceptsUnitSq work2344.out = true := by
  norm_num [work2344, contact2344, tau2344, center2344, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2344 : CellCertificate where
  tauBall := tau2344
  contactCenter := center2344
  contactBall := contact2344
  work := work2344
  center_sq := center_sq2344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2344.1
  jac_ok := checks2344.2.1
  accepted := checks2344.2.2

def tau2345 : RatBall :=
  ⟨⟨51/320, 101/320⟩, 3/640⟩
def center2345 : GaussianRat :=
  ⟨30377187/250000000, 6872127/31250000⟩
def contact2345 : RatBall := localContactBall tau2345 center2345
def work2345 : RoundedTauEval :=
  evalTau precision tau2345 contact2345 logTwoBall

theorem center_sq2345 : (center2345.re : ℝ)^2 +
    (center2345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2345 : work2345.theta.ok = true ∧
    work2345.jac.invOK = true ∧ acceptsUnitSq work2345.out = true := by
  norm_num [work2345, contact2345, tau2345, center2345, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2345 : CellCertificate where
  tauBall := tau2345
  contactCenter := center2345
  contactBall := contact2345
  work := work2345
  center_sq := center_sq2345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2345.1
  jac_ok := checks2345.2.1
  accepted := checks2345.2.2

def tau2346 : RatBall :=
  ⟨⟨49/320, 103/320⟩, 3/640⟩
def center2346 : GaussianRat :=
  ⟨117379261/1000000000, 56270573/250000000⟩
def contact2346 : RatBall := localContactBall tau2346 center2346
def work2346 : RoundedTauEval :=
  evalTau precision tau2346 contact2346 logTwoBall

theorem center_sq2346 : (center2346.re : ℝ)^2 +
    (center2346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2346 : work2346.theta.ok = true ∧
    work2346.jac.invOK = true ∧ acceptsUnitSq work2346.out = true := by
  norm_num [work2346, contact2346, tau2346, center2346, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2346 : CellCertificate where
  tauBall := tau2346
  contactCenter := center2346
  contactBall := contact2346
  work := work2346
  center_sq := center_sq2346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2346.1
  jac_ok := checks2346.2.1
  accepted := checks2346.2.2

def tau2347 : RatBall :=
  ⟨⟨51/320, 103/320⟩, 3/640⟩
def center2347 : GaussianRat :=
  ⟨7627513/62500000, 224552577/1000000000⟩
def contact2347 : RatBall := localContactBall tau2347 center2347
def work2347 : RoundedTauEval :=
  evalTau precision tau2347 contact2347 logTwoBall

theorem center_sq2347 : (center2347.re : ℝ)^2 +
    (center2347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2347 : work2347.theta.ok = true ∧
    work2347.jac.invOK = true ∧ acceptsUnitSq work2347.out = true := by
  norm_num [work2347, contact2347, tau2347, center2347, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2347 : CellCertificate where
  tauBall := tau2347
  contactCenter := center2347
  contactBall := contact2347
  work := work2347
  center_sq := center_sq2347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2347.1
  jac_ok := checks2347.2.1
  accepted := checks2347.2.2

def tau2348 : RatBall :=
  ⟨⟨53/320, 101/320⟩, 3/640⟩
def center2348 : GaussianRat :=
  ⟨15767113/125000000, 219375147/1000000000⟩
def contact2348 : RatBall := localContactBall tau2348 center2348
def work2348 : RoundedTauEval :=
  evalTau precision tau2348 contact2348 logTwoBall

theorem center_sq2348 : (center2348.re : ℝ)^2 +
    (center2348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2348 : work2348.theta.ok = true ∧
    work2348.jac.invOK = true ∧ acceptsUnitSq work2348.out = true := by
  norm_num [work2348, contact2348, tau2348, center2348, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2348 : CellCertificate where
  tauBall := tau2348
  contactCenter := center2348
  contactBall := contact2348
  work := work2348
  center_sq := center_sq2348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2348.1
  jac_ok := checks2348.2.1
  accepted := checks2348.2.2

def tau2349 : RatBall :=
  ⟨⟨11/64, 101/320⟩, 3/640⟩
def center2349 : GaussianRat :=
  ⟨3268749/25000000, 54706193/250000000⟩
def contact2349 : RatBall := localContactBall tau2349 center2349
def work2349 : RoundedTauEval :=
  evalTau precision tau2349 contact2349 logTwoBall

theorem center_sq2349 : (center2349.re : ℝ)^2 +
    (center2349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2349 : work2349.theta.ok = true ∧
    work2349.jac.invOK = true ∧ acceptsUnitSq work2349.out = true := by
  norm_num [work2349, contact2349, tau2349, center2349, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2349 : CellCertificate where
  tauBall := tau2349
  contactCenter := center2349
  contactBall := contact2349
  work := work2349
  center_sq := center_sq2349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2349.1
  jac_ok := checks2349.2.1
  accepted := checks2349.2.2

def tau2350 : RatBall :=
  ⟨⟨53/320, 103/320⟩, 3/640⟩
def center2350 : GaussianRat :=
  ⟨126686203/1000000000, 224004631/1000000000⟩
def contact2350 : RatBall := localContactBall tau2350 center2350
def work2350 : RoundedTauEval :=
  evalTau precision tau2350 contact2350 logTwoBall

theorem center_sq2350 : (center2350.re : ℝ)^2 +
    (center2350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2350 : work2350.theta.ok = true ∧
    work2350.jac.invOK = true ∧ acceptsUnitSq work2350.out = true := by
  norm_num [work2350, contact2350, tau2350, center2350, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2350 : CellCertificate where
  tauBall := tau2350
  contactCenter := center2350
  contactBall := contact2350
  work := work2350
  center_sq := center_sq2350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2350.1
  jac_ok := checks2350.2.1
  accepted := checks2350.2.2

def tau2351 : RatBall :=
  ⟨⟨11/64, 103/320⟩, 3/640⟩
def center2351 : GaussianRat :=
  ⟨8207299/62500000, 8937551/40000000⟩
def contact2351 : RatBall := localContactBall tau2351 center2351
def work2351 : RoundedTauEval :=
  evalTau precision tau2351 contact2351 logTwoBall

theorem center_sq2351 : (center2351.re : ℝ)^2 +
    (center2351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2351 : work2351.theta.ok = true ∧
    work2351.jac.invOK = true ∧ acceptsUnitSq work2351.out = true := by
  norm_num [work2351, contact2351, tau2351, center2351, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2351 : CellCertificate where
  tauBall := tau2351
  contactCenter := center2351
  contactBall := contact2351
  work := work2351
  center_sq := center_sq2351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2351.1
  jac_ok := checks2351.2.1
  accepted := checks2351.2.2

def cells : List CellCertificate := [cell2344, cell2345, cell2346, cell2347, cell2348, cell2349, cell2350, cell2351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293

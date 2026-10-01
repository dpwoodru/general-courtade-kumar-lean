import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2376 : RatBall :=
  ⟨⟨49/320, 109/320⟩, 3/640⟩
def center2376 : GaussianRat :=
  ⟨119007309/1000000000, 59793181/250000000⟩
def contact2376 : RatBall := localContactBall tau2376 center2376
def work2376 : RoundedTauEval :=
  evalTau precision tau2376 contact2376 logTwoBall

theorem center_sq2376 : (center2376.re : ℝ)^2 +
    (center2376.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2376]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2376 : work2376.theta.ok = true ∧
    work2376.jac.invOK = true ∧ acceptsUnitSq work2376.out = true := by
  norm_num [work2376, contact2376, tau2376, center2376, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2376 : CellCertificate where
  tauBall := tau2376
  contactCenter := center2376
  contactBall := contact2376
  work := work2376
  center_sq := center_sq2376
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2376.1
  jac_ok := checks2376.2.1
  accepted := checks2376.2.2

def tau2377 : RatBall :=
  ⟨⟨51/320, 109/320⟩, 3/640⟩
def center2377 : GaussianRat :=
  ⟨61862799/500000000, 238597409/1000000000⟩
def contact2377 : RatBall := localContactBall tau2377 center2377
def work2377 : RoundedTauEval :=
  evalTau precision tau2377 contact2377 logTwoBall

theorem center_sq2377 : (center2377.re : ℝ)^2 +
    (center2377.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2377]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2377 : work2377.theta.ok = true ∧
    work2377.jac.invOK = true ∧ acceptsUnitSq work2377.out = true := by
  norm_num [work2377, contact2377, tau2377, center2377, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2377 : CellCertificate where
  tauBall := tau2377
  contactCenter := center2377
  contactBall := contact2377
  work := work2377
  center_sq := center_sq2377
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2377.1
  jac_ok := checks2377.2.1
  accepted := checks2377.2.2

def tau2378 : RatBall :=
  ⟨⟨49/320, 111/320⟩, 3/640⟩
def center2378 : GaussianRat :=
  ⟨29895113/250000000, 121954461/500000000⟩
def contact2378 : RatBall := localContactBall tau2378 center2378
def work2378 : RoundedTauEval :=
  evalTau precision tau2378 contact2378 logTwoBall

theorem center_sq2378 : (center2378.re : ℝ)^2 +
    (center2378.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2378]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2378 : work2378.theta.ok = true ∧
    work2378.jac.invOK = true ∧ acceptsUnitSq work2378.out = true := by
  norm_num [work2378, contact2378, tau2378, center2378, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2378 : CellCertificate where
  tauBall := tau2378
  contactCenter := center2378
  contactBall := contact2378
  work := work2378
  center_sq := center_sq2378
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2378.1
  jac_ok := checks2378.2.1
  accepted := checks2378.2.2

def tau2379 : RatBall :=
  ⟨⟨51/320, 111/320⟩, 3/640⟩
def center2379 : GaussianRat :=
  ⟨124318847/1000000000, 121658863/500000000⟩
def contact2379 : RatBall := localContactBall tau2379 center2379
def work2379 : RoundedTauEval :=
  evalTau precision tau2379 contact2379 logTwoBall

theorem center_sq2379 : (center2379.re : ℝ)^2 +
    (center2379.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2379]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2379 : work2379.theta.ok = true ∧
    work2379.jac.invOK = true ∧ acceptsUnitSq work2379.out = true := by
  norm_num [work2379, contact2379, tau2379, center2379, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2379 : CellCertificate where
  tauBall := tau2379
  contactCenter := center2379
  contactBall := contact2379
  work := work2379
  center_sq := center_sq2379
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2379.1
  jac_ok := checks2379.2.1
  accepted := checks2379.2.2

def tau2380 : RatBall :=
  ⟨⟨53/320, 109/320⟩, 3/640⟩
def center2380 : GaussianRat :=
  ⟨25685587/200000000, 238002417/1000000000⟩
def contact2380 : RatBall := localContactBall tau2380 center2380
def work2380 : RoundedTauEval :=
  evalTau precision tau2380 contact2380 logTwoBall

theorem center_sq2380 : (center2380.re : ℝ)^2 +
    (center2380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2380 : work2380.theta.ok = true ∧
    work2380.jac.invOK = true ∧ acceptsUnitSq work2380.out = true := by
  norm_num [work2380, contact2380, tau2380, center2380, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2380 : CellCertificate where
  tauBall := tau2380
  contactCenter := center2380
  contactBall := contact2380
  work := work2380
  center_sq := center_sq2380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2380.1
  jac_ok := checks2380.2.1
  accepted := checks2380.2.2

def tau2381 : RatBall :=
  ⟨⟨11/64, 109/320⟩, 3/640⟩
def center2381 : GaussianRat :=
  ⟨133113831/1000000000, 118694053/500000000⟩
def contact2381 : RatBall := localContactBall tau2381 center2381
def work2381 : RoundedTauEval :=
  evalTau precision tau2381 contact2381 logTwoBall

theorem center_sq2381 : (center2381.re : ℝ)^2 +
    (center2381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2381 : work2381.theta.ok = true ∧
    work2381.jac.invOK = true ∧ acceptsUnitSq work2381.out = true := by
  norm_num [work2381, contact2381, tau2381, center2381, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2381 : CellCertificate where
  tauBall := tau2381
  contactCenter := center2381
  contactBall := contact2381
  work := work2381
  center_sq := center_sq2381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2381.1
  jac_ok := checks2381.2.1
  accepted := checks2381.2.2

def tau2382 : RatBall :=
  ⟨⟨53/320, 111/320⟩, 3/640⟩
def center2382 : GaussianRat :=
  ⟨4032529/31250000, 121353177/500000000⟩
def contact2382 : RatBall := localContactBall tau2382 center2382
def work2382 : RoundedTauEval :=
  evalTau precision tau2382 contact2382 logTwoBall

theorem center_sq2382 : (center2382.re : ℝ)^2 +
    (center2382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2382 : work2382.theta.ok = true ∧
    work2382.jac.invOK = true ∧ acceptsUnitSq work2382.out = true := by
  norm_num [work2382, contact2382, tau2382, center2382, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2382 : CellCertificate where
  tauBall := tau2382
  contactCenter := center2382
  contactBall := contact2382
  work := work2382
  center_sq := center_sq2382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2382.1
  jac_ok := checks2382.2.1
  accepted := checks2382.2.2

def tau2383 : RatBall :=
  ⟨⟨11/64, 111/320⟩, 3/640⟩
def center2383 : GaussianRat :=
  ⟨133746201/1000000000, 121037589/500000000⟩
def contact2383 : RatBall := localContactBall tau2383 center2383
def work2383 : RoundedTauEval :=
  evalTau precision tau2383 contact2383 logTwoBall

theorem center_sq2383 : (center2383.re : ℝ)^2 +
    (center2383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2383 : work2383.theta.ok = true ∧
    work2383.jac.invOK = true ∧ acceptsUnitSq work2383.out = true := by
  norm_num [work2383, contact2383, tau2383, center2383, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2383 : CellCertificate where
  tauBall := tau2383
  contactCenter := center2383
  contactBall := contact2383
  work := work2383
  center_sq := center_sq2383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2383.1
  jac_ok := checks2383.2.1
  accepted := checks2383.2.2

def cells : List CellCertificate := [cell2376, cell2377, cell2378, cell2379, cell2380, cell2381, cell2382, cell2383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297

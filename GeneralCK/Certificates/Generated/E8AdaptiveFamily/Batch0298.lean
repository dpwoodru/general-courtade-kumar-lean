import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0298

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2384 : RatBall :=
  ⟨⟨57/320, 21/64⟩, 3/640⟩
def center2384 : GaussianRat :=
  ⟨136531833/1000000000, 227470663/1000000000⟩
def contact2384 : RatBall := localContactBall tau2384 center2384
def work2384 : RoundedTauEval :=
  evalTau precision tau2384 contact2384 logTwoBall

theorem center_sq2384 : (center2384.re : ℝ)^2 +
    (center2384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2384 : work2384.theta.ok = true ∧
    work2384.jac.invOK = true ∧ acceptsUnitSq work2384.out = true := by
  norm_num [work2384, contact2384, tau2384, center2384, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2384 : CellCertificate where
  tauBall := tau2384
  contactCenter := center2384
  contactBall := contact2384
  work := work2384
  center_sq := center_sq2384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2384.1
  jac_ok := checks2384.2.1
  accepted := checks2384.2.2

def tau2385 : RatBall :=
  ⟨⟨59/320, 21/64⟩, 3/640⟩
def center2385 : GaussianRat :=
  ⟨70573769/500000000, 113426637/500000000⟩
def contact2385 : RatBall := localContactBall tau2385 center2385
def work2385 : RoundedTauEval :=
  evalTau precision tau2385 contact2385 logTwoBall

theorem center_sq2385 : (center2385.re : ℝ)^2 +
    (center2385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2385 : work2385.theta.ok = true ∧
    work2385.jac.invOK = true ∧ acceptsUnitSq work2385.out = true := by
  norm_num [work2385, contact2385, tau2385, center2385, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2385 : CellCertificate where
  tauBall := tau2385
  contactCenter := center2385
  contactBall := contact2385
  work := work2385
  center_sq := center_sq2385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2385.1
  jac_ok := checks2385.2.1
  accepted := checks2385.2.2

def tau2386 : RatBall :=
  ⟨⟨57/320, 107/320⟩, 3/640⟩
def center2386 : GaussianRat :=
  ⟨6857441/50000000, 46420737/200000000⟩
def contact2386 : RatBall := localContactBall tau2386 center2386
def work2386 : RoundedTauEval :=
  evalTau precision tau2386 contact2386 logTwoBall

theorem center_sq2386 : (center2386.re : ℝ)^2 +
    (center2386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2386 : work2386.theta.ok = true ∧
    work2386.jac.invOK = true ∧ acceptsUnitSq work2386.out = true := by
  norm_num [work2386, contact2386, tau2386, center2386, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2386 : CellCertificate where
  tauBall := tau2386
  contactCenter := center2386
  contactBall := contact2386
  work := work2386
  center_sq := center_sq2386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2386.1
  jac_ok := checks2386.2.1
  accepted := checks2386.2.2

def tau2387 : RatBall :=
  ⟨⟨59/320, 107/320⟩, 3/640⟩
def center2387 : GaussianRat :=
  ⟨141782257/1000000000, 231469249/1000000000⟩
def contact2387 : RatBall := localContactBall tau2387 center2387
def work2387 : RoundedTauEval :=
  evalTau precision tau2387 contact2387 logTwoBall

theorem center_sq2387 : (center2387.re : ℝ)^2 +
    (center2387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2387 : work2387.theta.ok = true ∧
    work2387.jac.invOK = true ∧ acceptsUnitSq work2387.out = true := by
  norm_num [work2387, contact2387, tau2387, center2387, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2387 : CellCertificate where
  tauBall := tau2387
  contactCenter := center2387
  contactBall := contact2387
  work := work2387
  center_sq := center_sq2387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2387.1
  jac_ok := checks2387.2.1
  accepted := checks2387.2.2

def tau2388 : RatBall :=
  ⟨⟨61/320, 21/64⟩, 3/640⟩
def center2388 : GaussianRat :=
  ⟨145746161/1000000000, 113109273/500000000⟩
def contact2388 : RatBall := localContactBall tau2388 center2388
def work2388 : RoundedTauEval :=
  evalTau precision tau2388 contact2388 logTwoBall

theorem center_sq2388 : (center2388.re : ℝ)^2 +
    (center2388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2388 : work2388.theta.ok = true ∧
    work2388.jac.invOK = true ∧ acceptsUnitSq work2388.out = true := by
  norm_num [work2388, contact2388, tau2388, center2388, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2388 : CellCertificate where
  tauBall := tau2388
  contactCenter := center2388
  contactBall := contact2388
  work := work2388
  center_sq := center_sq2388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2388.1
  jac_ok := checks2388.2.1
  accepted := checks2388.2.2

def tau2389 : RatBall :=
  ⟨⟨63/320, 21/64⟩, 3/640⟩
def center2389 : GaussianRat :=
  ⟨75163641/500000000, 225566837/1000000000⟩
def contact2389 : RatBall := localContactBall tau2389 center2389
def work2389 : RoundedTauEval :=
  evalTau precision tau2389 contact2389 logTwoBall

theorem center_sq2389 : (center2389.re : ℝ)^2 +
    (center2389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2389 : work2389.theta.ok = true ∧
    work2389.jac.invOK = true ∧ acceptsUnitSq work2389.out = true := by
  norm_num [work2389, contact2389, tau2389, center2389, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2389 : CellCertificate where
  tauBall := tau2389
  contactCenter := center2389
  contactBall := contact2389
  work := work2389
  center_sq := center_sq2389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2389.1
  jac_ok := checks2389.2.1
  accepted := checks2389.2.2

def tau2390 : RatBall :=
  ⟨⟨61/320, 107/320⟩, 3/640⟩
def center2390 : GaussianRat :=
  ⟨146398251/1000000000, 115408523/500000000⟩
def contact2390 : RatBall := localContactBall tau2390 center2390
def work2390 : RoundedTauEval :=
  evalTau precision tau2390 contact2390 logTwoBall

theorem center_sq2390 : (center2390.re : ℝ)^2 +
    (center2390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2390 : work2390.theta.ok = true ∧
    work2390.jac.invOK = true ∧ acceptsUnitSq work2390.out = true := by
  norm_num [work2390, contact2390, tau2390, center2390, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2390 : CellCertificate where
  tauBall := tau2390
  contactCenter := center2390
  contactBall := contact2390
  work := work2390
  center_sq := center_sq2390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2390.1
  jac_ok := checks2390.2.1
  accepted := checks2390.2.2

def tau2391 : RatBall :=
  ⟨⟨63/320, 107/320⟩, 3/640⟩
def center2391 : GaussianRat :=
  ⟨150996377/1000000000, 230147447/1000000000⟩
def contact2391 : RatBall := localContactBall tau2391 center2391
def work2391 : RoundedTauEval :=
  evalTau precision tau2391 contact2391 logTwoBall

theorem center_sq2391 : (center2391.re : ℝ)^2 +
    (center2391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2391 : work2391.theta.ok = true ∧
    work2391.jac.invOK = true ∧ acceptsUnitSq work2391.out = true := by
  norm_num [work2391, contact2391, tau2391, center2391, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2391 : CellCertificate where
  tauBall := tau2391
  contactCenter := center2391
  contactBall := contact2391
  work := work2391
  center_sq := center_sq2391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2391.1
  jac_ok := checks2391.2.1
  accepted := checks2391.2.2

def cells : List CellCertificate := [cell2384, cell2385, cell2386, cell2387, cell2388, cell2389, cell2390, cell2391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0298

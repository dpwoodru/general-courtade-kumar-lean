import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1336 : RatBall :=
  ⟨⟨-67/320, -19/64⟩, 3/640⟩
def center1336 : GaussianRat :=
  ⟨-78099293/500000000, -100863299/500000000⟩
def contact1336 : RatBall := localContactBall tau1336 center1336
def work1336 : RoundedTauEval :=
  evalTau precision tau1336 contact1336 logTwoBall

theorem center_sq1336 : (center1336.re : ℝ)^2 +
    (center1336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1336 : work1336.theta.ok = true ∧
    work1336.jac.invOK = true ∧ acceptsUnitSq work1336.out = true := by
  norm_num [work1336, contact1336, tau1336, center1336, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1336 : CellCertificate where
  tauBall := tau1336
  contactCenter := center1336
  contactBall := contact1336
  work := work1336
  center_sq := center_sq1336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1336.1
  jac_ok := checks1336.2.1
  accepted := checks1336.2.2

def tau1337 : RatBall :=
  ⟨⟨-13/64, -19/64⟩, 3/640⟩
def center1337 : GaussianRat :=
  ⟨-30345869/200000000, -40464617/200000000⟩
def contact1337 : RatBall := localContactBall tau1337 center1337
def work1337 : RoundedTauEval :=
  evalTau precision tau1337 contact1337 logTwoBall

theorem center_sq1337 : (center1337.re : ℝ)^2 +
    (center1337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1337 : work1337.theta.ok = true ∧
    work1337.jac.invOK = true ∧ acceptsUnitSq work1337.out = true := by
  norm_num [work1337, contact1337, tau1337, center1337, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1337 : CellCertificate where
  tauBall := tau1337
  contactCenter := center1337
  contactBall := contact1337
  work := work1337
  center_sq := center_sq1337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1337.1
  jac_ok := checks1337.2.1
  accepted := checks1337.2.2

def tau1338 : RatBall :=
  ⟨⟨-67/320, -93/320⟩, 3/640⟩
def center1338 : GaussianRat :=
  ⟨-3112069/20000000, -197272757/1000000000⟩
def contact1338 : RatBall := localContactBall tau1338 center1338
def work1338 : RoundedTauEval :=
  evalTau precision tau1338 contact1338 logTwoBall

theorem center_sq1338 : (center1338.re : ℝ)^2 +
    (center1338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1338 : work1338.theta.ok = true ∧
    work1338.jac.invOK = true ∧ acceptsUnitSq work1338.out = true := by
  norm_num [work1338, contact1338, tau1338, center1338, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1338 : CellCertificate where
  tauBall := tau1338
  contactCenter := center1338
  contactBall := contact1338
  work := work1338
  center_sq := center_sq1338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1338.1
  jac_ok := checks1338.2.1
  accepted := checks1338.2.2

def tau1339 : RatBall :=
  ⟨⟨-13/64, -93/320⟩, 3/640⟩
def center1339 : GaussianRat :=
  ⟨-151148249/1000000000, -98926301/500000000⟩
def contact1339 : RatBall := localContactBall tau1339 center1339
def work1339 : RoundedTauEval :=
  evalTau precision tau1339 contact1339 logTwoBall

theorem center_sq1339 : (center1339.re : ℝ)^2 +
    (center1339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1339 : work1339.theta.ok = true ∧
    work1339.jac.invOK = true ∧ acceptsUnitSq work1339.out = true := by
  norm_num [work1339, contact1339, tau1339, center1339, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1339 : CellCertificate where
  tauBall := tau1339
  contactCenter := center1339
  contactBall := contact1339
  work := work1339
  center_sq := center_sq1339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1339.1
  jac_ok := checks1339.2.1
  accepted := checks1339.2.2

def tau1340 : RatBall :=
  ⟨⟨-19/64, -79/320⟩, 3/640⟩
def center1340 : GaussianRat :=
  ⟨-211331481/1000000000, -158782791/1000000000⟩
def contact1340 : RatBall := localContactBall tau1340 center1340
def work1340 : RoundedTauEval :=
  evalTau precision tau1340 contact1340 logTwoBall

theorem center_sq1340 : (center1340.re : ℝ)^2 +
    (center1340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1340 : work1340.theta.ok = true ∧
    work1340.jac.invOK = true ∧ acceptsUnitSq work1340.out = true := by
  norm_num [work1340, contact1340, tau1340, center1340, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1340 : CellCertificate where
  tauBall := tau1340
  contactCenter := center1340
  contactBall := contact1340
  work := work1340
  center_sq := center_sq1340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1340.1
  jac_ok := checks1340.2.1
  accepted := checks1340.2.2

def tau1341 : RatBall :=
  ⟨⟨-93/320, -79/320⟩, 3/640⟩
def center1341 : GaussianRat :=
  ⟨-207198371/1000000000, -15939079/100000000⟩
def contact1341 : RatBall := localContactBall tau1341 center1341
def work1341 : RoundedTauEval :=
  evalTau precision tau1341 contact1341 logTwoBall

theorem center_sq1341 : (center1341.re : ℝ)^2 +
    (center1341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1341 : work1341.theta.ok = true ∧
    work1341.jac.invOK = true ∧ acceptsUnitSq work1341.out = true := by
  norm_num [work1341, contact1341, tau1341, center1341, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1341 : CellCertificate where
  tauBall := tau1341
  contactCenter := center1341
  contactBall := contact1341
  work := work1341
  center_sq := center_sq1341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1341.1
  jac_ok := checks1341.2.1
  accepted := checks1341.2.2

def tau1342 : RatBall :=
  ⟨⟨-19/64, -77/320⟩, 3/640⟩
def center1342 : GaussianRat :=
  ⟨-26341087/125000000, -77331419/500000000⟩
def contact1342 : RatBall := localContactBall tau1342 center1342
def work1342 : RoundedTauEval :=
  evalTau precision tau1342 contact1342 logTwoBall

theorem center_sq1342 : (center1342.re : ℝ)^2 +
    (center1342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1342 : work1342.theta.ok = true ∧
    work1342.jac.invOK = true ∧ acceptsUnitSq work1342.out = true := by
  norm_num [work1342, contact1342, tau1342, center1342, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1342 : CellCertificate where
  tauBall := tau1342
  contactCenter := center1342
  contactBall := contact1342
  work := work1342
  center_sq := center_sq1342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1342.1
  jac_ok := checks1342.2.1
  accepted := checks1342.2.2

def tau1343 : RatBall :=
  ⟨⟨-93/320, -77/320⟩, 3/640⟩
def center1343 : GaussianRat :=
  ⟨-12912721/62500000, -7762627/50000000⟩
def contact1343 : RatBall := localContactBall tau1343 center1343
def work1343 : RoundedTauEval :=
  evalTau precision tau1343 contact1343 logTwoBall

theorem center_sq1343 : (center1343.re : ℝ)^2 +
    (center1343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1343 : work1343.theta.ok = true ∧
    work1343.jac.invOK = true ∧ acceptsUnitSq work1343.out = true := by
  norm_num [work1343, contact1343, tau1343, center1343, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1343 : CellCertificate where
  tauBall := tau1343
  contactCenter := center1343
  contactBall := contact1343
  work := work1343
  center_sq := center_sq1343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1343.1
  jac_ok := checks1343.2.1
  accepted := checks1343.2.2

def cells : List CellCertificate := [cell1336, cell1337, cell1338, cell1339, cell1340, cell1341, cell1342, cell1343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

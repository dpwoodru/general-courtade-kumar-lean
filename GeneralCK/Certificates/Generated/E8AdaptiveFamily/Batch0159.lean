import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1272 : RatBall :=
  ⟨⟨-91/320, -91/320⟩, 3/640⟩
def center1272 : GaussianRat :=
  ⟨-51739029/250000000, -46278317/250000000⟩
def contact1272 : RatBall := localContactBall tau1272 center1272
def work1272 : RoundedTauEval :=
  evalTau precision tau1272 contact1272 logTwoBall

theorem center_sq1272 : (center1272.re : ℝ)^2 +
    (center1272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1272 : work1272.theta.ok = true ∧
    work1272.jac.invOK = true ∧ acceptsUnitSq work1272.out = true := by
  norm_num [work1272, contact1272, tau1272, center1272, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1272 : CellCertificate where
  tauBall := tau1272
  contactCenter := center1272
  contactBall := contact1272
  work := work1272
  center_sq := center_sq1272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1272.1
  jac_ok := checks1272.2.1
  accepted := checks1272.2.2

def tau1273 : RatBall :=
  ⟨⟨-89/320, -91/320⟩, 3/640⟩
def center1273 : GaussianRat :=
  ⟨-202731249/1000000000, -37163483/200000000⟩
def contact1273 : RatBall := localContactBall tau1273 center1273
def work1273 : RoundedTauEval :=
  evalTau precision tau1273 contact1273 logTwoBall

theorem center_sq1273 : (center1273.re : ℝ)^2 +
    (center1273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1273 : work1273.theta.ok = true ∧
    work1273.jac.invOK = true ∧ acceptsUnitSq work1273.out = true := by
  norm_num [work1273, contact1273, tau1273, center1273, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1273 : CellCertificate where
  tauBall := tau1273
  contactCenter := center1273
  contactBall := contact1273
  work := work1273
  center_sq := center_sq1273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1273.1
  jac_ok := checks1273.2.1
  accepted := checks1273.2.2

def tau1274 : RatBall :=
  ⟨⟨-91/320, -89/320⟩, 3/640⟩
def center1274 : GaussianRat :=
  ⟨-103128439/500000000, -180903081/1000000000⟩
def contact1274 : RatBall := localContactBall tau1274 center1274
def work1274 : RoundedTauEval :=
  evalTau precision tau1274 contact1274 logTwoBall

theorem center_sq1274 : (center1274.re : ℝ)^2 +
    (center1274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1274 : work1274.theta.ok = true ∧
    work1274.jac.invOK = true ∧ acceptsUnitSq work1274.out = true := by
  norm_num [work1274, contact1274, tau1274, center1274, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1274 : CellCertificate where
  tauBall := tau1274
  contactCenter := center1274
  contactBall := contact1274
  work := work1274
  center_sq := center_sq1274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1274.1
  jac_ok := checks1274.2.1
  accepted := checks1274.2.2

def tau1275 : RatBall :=
  ⟨⟨-89/320, -89/320⟩, 3/640⟩
def center1275 : GaussianRat :=
  ⟨-40408359/200000000, -181587727/1000000000⟩
def contact1275 : RatBall := localContactBall tau1275 center1275
def work1275 : RoundedTauEval :=
  evalTau precision tau1275 contact1275 logTwoBall

theorem center_sq1275 : (center1275.re : ℝ)^2 +
    (center1275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1275 : work1275.theta.ok = true ∧
    work1275.jac.invOK = true ∧ acceptsUnitSq work1275.out = true := by
  norm_num [work1275, contact1275, tau1275, center1275, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1275 : CellCertificate where
  tauBall := tau1275
  contactCenter := center1275
  contactBall := contact1275
  work := work1275
  center_sq := center_sq1275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1275.1
  jac_ok := checks1275.2.1
  accepted := checks1275.2.2

def tau1276 : RatBall :=
  ⟨⟨-87/320, -19/64⟩, 3/640⟩
def center1276 : GaussianRat :=
  ⟨-199903813/1000000000, -195040739/1000000000⟩
def contact1276 : RatBall := localContactBall tau1276 center1276
def work1276 : RoundedTauEval :=
  evalTau precision tau1276 contact1276 logTwoBall

theorem center_sq1276 : (center1276.re : ℝ)^2 +
    (center1276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1276 : work1276.theta.ok = true ∧
    work1276.jac.invOK = true ∧ acceptsUnitSq work1276.out = true := by
  norm_num [work1276, contact1276, tau1276, center1276, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1276 : CellCertificate where
  tauBall := tau1276
  contactCenter := center1276
  contactBall := contact1276
  work := work1276
  center_sq := center_sq1276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1276.1
  jac_ok := checks1276.2.1
  accepted := checks1276.2.2

def tau1277 : RatBall :=
  ⟨⟨-17/64, -19/64⟩, 3/640⟩
def center1277 : GaussianRat :=
  ⟨-39123719/200000000, -48940869/250000000⟩
def contact1277 : RatBall := localContactBall tau1277 center1277
def work1277 : RoundedTauEval :=
  evalTau precision tau1277 contact1277 logTwoBall

theorem center_sq1277 : (center1277.re : ℝ)^2 +
    (center1277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1277 : work1277.theta.ok = true ∧
    work1277.jac.invOK = true ∧ acceptsUnitSq work1277.out = true := by
  norm_num [work1277, contact1277, tau1277, center1277, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1277 : CellCertificate where
  tauBall := tau1277
  contactCenter := center1277
  contactBall := contact1277
  work := work1277
  center_sq := center_sq1277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1277.1
  jac_ok := checks1277.2.1
  accepted := checks1277.2.2

def tau1278 : RatBall :=
  ⟨⟨-87/320, -93/320⟩, 3/640⟩
def center1278 : GaussianRat :=
  ⟨-2489819/12500000, -47692707/250000000⟩
def contact1278 : RatBall := localContactBall tau1278 center1278
def work1278 : RoundedTauEval :=
  evalTau precision tau1278 contact1278 logTwoBall

theorem center_sq1278 : (center1278.re : ℝ)^2 +
    (center1278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1278 : work1278.theta.ok = true ∧
    work1278.jac.invOK = true ∧ acceptsUnitSq work1278.out = true := by
  norm_num [work1278, contact1278, tau1278, center1278, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1278 : CellCertificate where
  tauBall := tau1278
  contactCenter := center1278
  contactBall := contact1278
  work := work1278
  center_sq := center_sq1278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1278.1
  jac_ok := checks1278.2.1
  accepted := checks1278.2.2

def tau1279 : RatBall :=
  ⟨⟨-17/64, -93/320⟩, 3/640⟩
def center1279 : GaussianRat :=
  ⟨-97455589/500000000, -191473909/1000000000⟩
def contact1279 : RatBall := localContactBall tau1279 center1279
def work1279 : RoundedTauEval :=
  evalTau precision tau1279 contact1279 logTwoBall

theorem center_sq1279 : (center1279.re : ℝ)^2 +
    (center1279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1279 : work1279.theta.ok = true ∧
    work1279.jac.invOK = true ∧ acceptsUnitSq work1279.out = true := by
  norm_num [work1279, contact1279, tau1279, center1279, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1279 : CellCertificate where
  tauBall := tau1279
  contactCenter := center1279
  contactBall := contact1279
  work := work1279
  center_sq := center_sq1279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1279.1
  jac_ok := checks1279.2.1
  accepted := checks1279.2.2

def cells : List CellCertificate := [cell1272, cell1273, cell1274, cell1275, cell1276, cell1277, cell1278, cell1279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159

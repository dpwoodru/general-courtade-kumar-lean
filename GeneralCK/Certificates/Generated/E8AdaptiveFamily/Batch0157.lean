import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1256 : RatBall :=
  ⟨⟨-99/320, -77/320⟩, 3/640⟩
def center1256 : GaussianRat :=
  ⟨-218923989/1000000000, -38365123/250000000⟩
def contact1256 : RatBall := localContactBall tau1256 center1256
def work1256 : RoundedTauEval :=
  evalTau precision tau1256 contact1256 logTwoBall

theorem center_sq1256 : (center1256.re : ℝ)^2 +
    (center1256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1256 : work1256.theta.ok = true ∧
    work1256.jac.invOK = true ∧ acceptsUnitSq work1256.out = true := by
  norm_num [work1256, contact1256, tau1256, center1256, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1256 : CellCertificate where
  tauBall := tau1256
  contactCenter := center1256
  contactBall := contact1256
  work := work1256
  center_sq := center_sq1256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1256.1
  jac_ok := checks1256.2.1
  accepted := checks1256.2.2

def tau1257 : RatBall :=
  ⟨⟨-97/320, -77/320⟩, 3/640⟩
def center1257 : GaussianRat :=
  ⟨-10741779/50000000, -300909/1953125⟩
def contact1257 : RatBall := localContactBall tau1257 center1257
def work1257 : RoundedTauEval :=
  evalTau precision tau1257 contact1257 logTwoBall

theorem center_sq1257 : (center1257.re : ℝ)^2 +
    (center1257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1257 : work1257.theta.ok = true ∧
    work1257.jac.invOK = true ∧ acceptsUnitSq work1257.out = true := by
  norm_num [work1257, contact1257, tau1257, center1257, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1257 : CellCertificate where
  tauBall := tau1257
  contactCenter := center1257
  contactBall := contact1257
  work := work1257
  center_sq := center_sq1257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1257.1
  jac_ok := checks1257.2.1
  accepted := checks1257.2.2

def tau1258 : RatBall :=
  ⟨⟨-103/320, -15/64⟩, 3/640⟩
def center1258 : GaussianRat :=
  ⟨-14151969/62500000, -148191091/1000000000⟩
def contact1258 : RatBall := localContactBall tau1258 center1258
def work1258 : RoundedTauEval :=
  evalTau precision tau1258 contact1258 logTwoBall

theorem center_sq1258 : (center1258.re : ℝ)^2 +
    (center1258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1258 : work1258.theta.ok = true ∧
    work1258.jac.invOK = true ∧ acceptsUnitSq work1258.out = true := by
  norm_num [work1258, contact1258, tau1258, center1258, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1258 : CellCertificate where
  tauBall := tau1258
  contactCenter := center1258
  contactBall := contact1258
  work := work1258
  center_sq := center_sq1258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1258.1
  jac_ok := checks1258.2.1
  accepted := checks1258.2.2

def tau1259 : RatBall :=
  ⟨⟨-101/320, -15/64⟩, 3/640⟩
def center1259 : GaussianRat :=
  ⟨-13899213/62500000, -2975829/20000000⟩
def contact1259 : RatBall := localContactBall tau1259 center1259
def work1259 : RoundedTauEval :=
  evalTau precision tau1259 contact1259 logTwoBall

theorem center_sq1259 : (center1259.re : ℝ)^2 +
    (center1259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1259 : work1259.theta.ok = true ∧
    work1259.jac.invOK = true ∧ acceptsUnitSq work1259.out = true := by
  norm_num [work1259, contact1259, tau1259, center1259, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1259 : CellCertificate where
  tauBall := tau1259
  contactCenter := center1259
  contactBall := contact1259
  work := work1259
  center_sq := center_sq1259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1259.1
  jac_ok := checks1259.2.1
  accepted := checks1259.2.2

def tau1260 : RatBall :=
  ⟨⟨-103/320, -73/320⟩, 3/640⟩
def center1260 : GaussianRat :=
  ⟨-5645929/25000000, -9009977/62500000⟩
def contact1260 : RatBall := localContactBall tau1260 center1260
def work1260 : RoundedTauEval :=
  evalTau precision tau1260 contact1260 logTwoBall

theorem center_sq1260 : (center1260.re : ℝ)^2 +
    (center1260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1260 : work1260.theta.ok = true ∧
    work1260.jac.invOK = true ∧ acceptsUnitSq work1260.out = true := by
  norm_num [work1260, contact1260, tau1260, center1260, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1260 : CellCertificate where
  tauBall := tau1260
  contactCenter := center1260
  contactBall := contact1260
  work := work1260
  center_sq := center_sq1260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1260.1
  jac_ok := checks1260.2.1
  accepted := checks1260.2.2

def tau1261 : RatBall :=
  ⟨⟨-101/320, -73/320⟩, 3/640⟩
def center1261 : GaussianRat :=
  ⟨-44359939/200000000, -72370703/500000000⟩
def contact1261 : RatBall := localContactBall tau1261 center1261
def work1261 : RoundedTauEval :=
  evalTau precision tau1261 contact1261 logTwoBall

theorem center_sq1261 : (center1261.re : ℝ)^2 +
    (center1261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1261 : work1261.theta.ok = true ∧
    work1261.jac.invOK = true ∧ acceptsUnitSq work1261.out = true := by
  norm_num [work1261, contact1261, tau1261, center1261, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1261 : CellCertificate where
  tauBall := tau1261
  contactCenter := center1261
  contactBall := contact1261
  work := work1261
  center_sq := center_sq1261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1261.1
  jac_ok := checks1261.2.1
  accepted := checks1261.2.2

def tau1262 : RatBall :=
  ⟨⟨-109/320, -69/320⟩, 3/640⟩
def center1262 : GaussianRat :=
  ⟨-236668663/1000000000, -134444337/1000000000⟩
def contact1262 : RatBall := localContactBall tau1262 center1262
def work1262 : RoundedTauEval :=
  evalTau precision tau1262 contact1262 logTwoBall

theorem center_sq1262 : (center1262.re : ℝ)^2 +
    (center1262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1262 : work1262.theta.ok = true ∧
    work1262.jac.invOK = true ∧ acceptsUnitSq work1262.out = true := by
  norm_num [work1262, contact1262, tau1262, center1262, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1262 : CellCertificate where
  tauBall := tau1262
  contactCenter := center1262
  contactBall := contact1262
  work := work1262
  center_sq := center_sq1262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1262.1
  jac_ok := checks1262.2.1
  accepted := checks1262.2.2

def tau1263 : RatBall :=
  ⟨⟨-107/320, -71/320⟩, 3/640⟩
def center1263 : GaussianRat :=
  ⟨-58317051/250000000, -34747303/250000000⟩
def contact1263 : RatBall := localContactBall tau1263 center1263
def work1263 : RoundedTauEval :=
  evalTau precision tau1263 contact1263 logTwoBall

theorem center_sq1263 : (center1263.re : ℝ)^2 +
    (center1263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1263 : work1263.theta.ok = true ∧
    work1263.jac.invOK = true ∧ acceptsUnitSq work1263.out = true := by
  norm_num [work1263, contact1263, tau1263, center1263, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1263 : CellCertificate where
  tauBall := tau1263
  contactCenter := center1263
  contactBall := contact1263
  work := work1263
  center_sq := center_sq1263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1263.1
  jac_ok := checks1263.2.1
  accepted := checks1263.2.2

def cells : List CellCertificate := [cell1256, cell1257, cell1258, cell1259, cell1260, cell1261, cell1262, cell1263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157

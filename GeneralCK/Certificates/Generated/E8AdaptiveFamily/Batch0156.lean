import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1248 : RatBall :=
  ⟨⟨-97/320, -81/320⟩, 3/640⟩
def center1248 : GaussianRat :=
  ⟨-108037641/500000000, -81137999/500000000⟩
def contact1248 : RatBall := localContactBall tau1248 center1248
def work1248 : RoundedTauEval :=
  evalTau precision tau1248 contact1248 logTwoBall

theorem center_sq1248 : (center1248.re : ℝ)^2 +
    (center1248.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1248]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1248 : work1248.theta.ok = true ∧
    work1248.jac.invOK = true ∧ acceptsUnitSq work1248.out = true := by
  norm_num [work1248, contact1248, tau1248, center1248, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1248 : CellCertificate where
  tauBall := tau1248
  contactCenter := center1248
  contactBall := contact1248
  work := work1248
  center_sq := center_sq1248
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1248.1
  jac_ok := checks1248.2.1
  accepted := checks1248.2.2

def tau1249 : RatBall :=
  ⟨⟨-21/64, -15/64⟩, 3/640⟩
def center1249 : GaussianRat :=
  ⟨-14403551/62500000, -14758413/100000000⟩
def contact1249 : RatBall := localContactBall tau1249 center1249
def work1249 : RoundedTauEval :=
  evalTau precision tau1249 contact1249 logTwoBall

theorem center_sq1249 : (center1249.re : ℝ)^2 +
    (center1249.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1249]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1249 : work1249.theta.ok = true ∧
    work1249.jac.invOK = true ∧ acceptsUnitSq work1249.out = true := by
  norm_num [work1249, contact1249, tau1249, center1249, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1249 : CellCertificate where
  tauBall := tau1249
  contactCenter := center1249
  contactBall := contact1249
  work := work1249
  center_sq := center_sq1249
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1249.1
  jac_ok := checks1249.2.1
  accepted := checks1249.2.2

def tau1250 : RatBall :=
  ⟨⟨-21/64, -73/320⟩, 3/640⟩
def center1250 : GaussianRat :=
  ⟨-229856067/1000000000, -5742857/40000000⟩
def contact1250 : RatBall := localContactBall tau1250 center1250
def work1250 : RoundedTauEval :=
  evalTau precision tau1250 contact1250 logTwoBall

theorem center_sq1250 : (center1250.re : ℝ)^2 +
    (center1250.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1250]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1250 : work1250.theta.ok = true ∧
    work1250.jac.invOK = true ∧ acceptsUnitSq work1250.out = true := by
  norm_num [work1250, contact1250, tau1250, center1250, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1250 : CellCertificate where
  tauBall := tau1250
  contactCenter := center1250
  contactBall := contact1250
  work := work1250
  center_sq := center_sq1250
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1250.1
  jac_ok := checks1250.2.1
  accepted := checks1250.2.2

def tau1251 : RatBall :=
  ⟨⟨-101/320, -79/320⟩, 3/640⟩
def center1251 : GaussianRat :=
  ⟨-111809453/500000000, -156912213/1000000000⟩
def contact1251 : RatBall := localContactBall tau1251 center1251
def work1251 : RoundedTauEval :=
  evalTau precision tau1251 contact1251 logTwoBall

theorem center_sq1251 : (center1251.re : ℝ)^2 +
    (center1251.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1251]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1251 : work1251.theta.ok = true ∧
    work1251.jac.invOK = true ∧ acceptsUnitSq work1251.out = true := by
  norm_num [work1251, contact1251, tau1251, center1251, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1251 : CellCertificate where
  tauBall := tau1251
  contactCenter := center1251
  contactBall := contact1251
  work := work1251
  center_sq := center_sq1251
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1251.1
  jac_ok := checks1251.2.1
  accepted := checks1251.2.2

def tau1252 : RatBall :=
  ⟨⟨-103/320, -77/320⟩, 3/640⟩
def center1252 : GaussianRat :=
  ⟨-113522317/500000000, -152229153/1000000000⟩
def contact1252 : RatBall := localContactBall tau1252 center1252
def work1252 : RoundedTauEval :=
  evalTau precision tau1252 contact1252 logTwoBall

theorem center_sq1252 : (center1252.re : ℝ)^2 +
    (center1252.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1252 : work1252.theta.ok = true ∧
    work1252.jac.invOK = true ∧ acceptsUnitSq work1252.out = true := by
  norm_num [work1252, contact1252, tau1252, center1252, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1252 : CellCertificate where
  tauBall := tau1252
  contactCenter := center1252
  contactBall := contact1252
  work := work1252
  center_sq := center_sq1252
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1252.1
  jac_ok := checks1252.2.1
  accepted := checks1252.2.2

def tau1253 : RatBall :=
  ⟨⟨-101/320, -77/320⟩, 3/640⟩
def center1253 : GaussianRat :=
  ⟨-111496867/500000000, -152848327/1000000000⟩
def contact1253 : RatBall := localContactBall tau1253 center1253
def work1253 : RoundedTauEval :=
  evalTau precision tau1253 contact1253 logTwoBall

theorem center_sq1253 : (center1253.re : ℝ)^2 +
    (center1253.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1253]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1253 : work1253.theta.ok = true ∧
    work1253.jac.invOK = true ∧ acceptsUnitSq work1253.out = true := by
  norm_num [work1253, contact1253, tau1253, center1253, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1253 : CellCertificate where
  tauBall := tau1253
  contactCenter := center1253
  contactBall := contact1253
  work := work1253
  center_sq := center_sq1253
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1253.1
  jac_ok := checks1253.2.1
  accepted := checks1253.2.2

def tau1254 : RatBall :=
  ⟨⟨-99/320, -79/320⟩, 3/640⟩
def center1254 : GaussianRat :=
  ⟨-109770971/500000000, -78771627/500000000⟩
def contact1254 : RatBall := localContactBall tau1254 center1254
def work1254 : RoundedTauEval :=
  evalTau precision tau1254 contact1254 logTwoBall

theorem center_sq1254 : (center1254.re : ℝ)^2 +
    (center1254.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1254]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1254 : work1254.theta.ok = true ∧
    work1254.jac.invOK = true ∧ acceptsUnitSq work1254.out = true := by
  norm_num [work1254, contact1254, tau1254, center1254, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1254 : CellCertificate where
  tauBall := tau1254
  contactCenter := center1254
  contactBall := contact1254
  work := work1254
  center_sq := center_sq1254
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1254.1
  jac_ok := checks1254.2.1
  accepted := checks1254.2.2

def tau1255 : RatBall :=
  ⟨⟨-97/320, -79/320⟩, 3/640⟩
def center1255 : GaussianRat :=
  ⟨-215446071/1000000000, -158166863/1000000000⟩
def contact1255 : RatBall := localContactBall tau1255 center1255
def work1255 : RoundedTauEval :=
  evalTau precision tau1255 contact1255 logTwoBall

theorem center_sq1255 : (center1255.re : ℝ)^2 +
    (center1255.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1255]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1255 : work1255.theta.ok = true ∧
    work1255.jac.invOK = true ∧ acceptsUnitSq work1255.out = true := by
  norm_num [work1255, contact1255, tau1255, center1255, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1255 : CellCertificate where
  tauBall := tau1255
  contactCenter := center1255
  contactBall := contact1255
  work := work1255
  center_sq := center_sq1255
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1255.1
  jac_ok := checks1255.2.1
  accepted := checks1255.2.2

def cells : List CellCertificate := [cell1248, cell1249, cell1250, cell1251, cell1252, cell1253, cell1254, cell1255]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156

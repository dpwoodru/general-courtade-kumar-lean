import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1296 : RatBall :=
  ⟨⟨-91/320, -87/320⟩, 3/640⟩
def center1296 : GaussianRat :=
  ⟨-102788551/500000000, -176702417/1000000000⟩
def contact1296 : RatBall := localContactBall tau1296 center1296
def work1296 : RoundedTauEval :=
  evalTau precision tau1296 contact1296 logTwoBall

theorem center_sq1296 : (center1296.re : ℝ)^2 +
    (center1296.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1296]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1296 : work1296.theta.ok = true ∧
    work1296.jac.invOK = true ∧ acceptsUnitSq work1296.out = true := by
  norm_num [work1296, contact1296, tau1296, center1296, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1296 : CellCertificate where
  tauBall := tau1296
  contactCenter := center1296
  contactBall := contact1296
  work := work1296
  center_sq := center_sq1296
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1296.1
  jac_ok := checks1296.2.1
  accepted := checks1296.2.2

def tau1297 : RatBall :=
  ⟨⟨-89/320, -87/320⟩, 3/640⟩
def center1297 : GaussianRat :=
  ⟨-201371579/1000000000, -177367859/1000000000⟩
def contact1297 : RatBall := localContactBall tau1297 center1297
def work1297 : RoundedTauEval :=
  evalTau precision tau1297 contact1297 logTwoBall

theorem center_sq1297 : (center1297.re : ℝ)^2 +
    (center1297.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1297]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1297 : work1297.theta.ok = true ∧
    work1297.jac.invOK = true ∧ acceptsUnitSq work1297.out = true := by
  norm_num [work1297, contact1297, tau1297, center1297, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1297 : CellCertificate where
  tauBall := tau1297
  contactCenter := center1297
  contactBall := contact1297
  work := work1297
  center_sq := center_sq1297
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1297.1
  jac_ok := checks1297.2.1
  accepted := checks1297.2.2

def tau1298 : RatBall :=
  ⟨⟨-91/320, -17/64⟩, 3/640⟩
def center1298 : GaussianRat :=
  ⟨-102458249/500000000, -172511057/1000000000⟩
def contact1298 : RatBall := localContactBall tau1298 center1298
def work1298 : RoundedTauEval :=
  evalTau precision tau1298 contact1298 logTwoBall

theorem center_sq1298 : (center1298.re : ℝ)^2 +
    (center1298.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1298]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1298 : work1298.theta.ok = true ∧
    work1298.jac.invOK = true ∧ acceptsUnitSq work1298.out = true := by
  norm_num [work1298, contact1298, tau1298, center1298, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1298 : CellCertificate where
  tauBall := tau1298
  contactCenter := center1298
  contactBall := contact1298
  work := work1298
  center_sq := center_sq1298
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1298.1
  jac_ok := checks1298.2.1
  accepted := checks1298.2.2

def tau1299 : RatBall :=
  ⟨⟨-89/320, -17/64⟩, 3/640⟩
def center1299 : GaussianRat :=
  ⟨-20072031/100000000, -86578791/500000000⟩
def contact1299 : RatBall := localContactBall tau1299 center1299
def work1299 : RoundedTauEval :=
  evalTau precision tau1299 contact1299 logTwoBall

theorem center_sq1299 : (center1299.re : ℝ)^2 +
    (center1299.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1299]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1299 : work1299.theta.ok = true ∧
    work1299.jac.invOK = true ∧ acceptsUnitSq work1299.out = true := by
  norm_num [work1299, contact1299, tau1299, center1299, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1299 : CellCertificate where
  tauBall := tau1299
  contactCenter := center1299
  contactBall := contact1299
  work := work1299
  center_sq := center_sq1299
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1299.1
  jac_ok := checks1299.2.1
  accepted := checks1299.2.2

def tau1300 : RatBall :=
  ⟨⟨-19/64, -83/320⟩, 3/640⟩
def center1300 : GaussianRat :=
  ⟨-212592873/1000000000, -33409337/200000000⟩
def contact1300 : RatBall := localContactBall tau1300 center1300
def work1300 : RoundedTauEval :=
  evalTau precision tau1300 contact1300 logTwoBall

theorem center_sq1300 : (center1300.re : ℝ)^2 +
    (center1300.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1300]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1300 : work1300.theta.ok = true ∧
    work1300.jac.invOK = true ∧ acceptsUnitSq work1300.out = true := by
  norm_num [work1300, contact1300, tau1300, center1300, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1300 : CellCertificate where
  tauBall := tau1300
  contactCenter := center1300
  contactBall := contact1300
  work := work1300
  center_sq := center_sq1300
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1300.1
  jac_ok := checks1300.2.1
  accepted := checks1300.2.2

def tau1301 : RatBall :=
  ⟨⟨-93/320, -83/320⟩, 3/640⟩
def center1301 : GaussianRat :=
  ⟨-52110811/250000000, -167692033/1000000000⟩
def contact1301 : RatBall := localContactBall tau1301 center1301
def work1301 : RoundedTauEval :=
  evalTau precision tau1301 contact1301 logTwoBall

theorem center_sq1301 : (center1301.re : ℝ)^2 +
    (center1301.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1301]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1301 : work1301.theta.ok = true ∧
    work1301.jac.invOK = true ∧ acceptsUnitSq work1301.out = true := by
  norm_num [work1301, contact1301, tau1301, center1301, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1301 : CellCertificate where
  tauBall := tau1301
  contactCenter := center1301
  contactBall := contact1301
  work := work1301
  center_sq := center_sq1301
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1301.1
  jac_ok := checks1301.2.1
  accepted := checks1301.2.2

def tau1302 : RatBall :=
  ⟨⟨-19/64, -81/320⟩, 3/640⟩
def center1302 : GaussianRat :=
  ⟨-211952789/1000000000, -162910673/1000000000⟩
def contact1302 : RatBall := localContactBall tau1302 center1302
def work1302 : RoundedTauEval :=
  evalTau precision tau1302 contact1302 logTwoBall

theorem center_sq1302 : (center1302.re : ℝ)^2 +
    (center1302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1302 : work1302.theta.ok = true ∧
    work1302.jac.invOK = true ∧ acceptsUnitSq work1302.out = true := by
  norm_num [work1302, contact1302, tau1302, center1302, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1302 : CellCertificate where
  tauBall := tau1302
  contactCenter := center1302
  contactBall := contact1302
  work := work1302
  center_sq := center_sq1302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1302.1
  jac_ok := checks1302.2.1
  accepted := checks1302.2.2

def tau1303 : RatBall :=
  ⟨⟨-93/320, -81/320⟩, 3/640⟩
def center1303 : GaussianRat :=
  ⟨-103905761/500000000, -163537217/1000000000⟩
def contact1303 : RatBall := localContactBall tau1303 center1303
def work1303 : RoundedTauEval :=
  evalTau precision tau1303 contact1303 logTwoBall

theorem center_sq1303 : (center1303.re : ℝ)^2 +
    (center1303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1303 : work1303.theta.ok = true ∧
    work1303.jac.invOK = true ∧ acceptsUnitSq work1303.out = true := by
  norm_num [work1303, contact1303, tau1303, center1303, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1303 : CellCertificate where
  tauBall := tau1303
  contactCenter := center1303
  contactBall := contact1303
  work := work1303
  center_sq := center_sq1303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1303.1
  jac_ok := checks1303.2.1
  accepted := checks1303.2.2

def cells : List CellCertificate := [cell1296, cell1297, cell1298, cell1299, cell1300, cell1301, cell1302, cell1303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162

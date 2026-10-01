import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1320 : RatBall :=
  ⟨⟨-15/64, -19/64⟩, 3/640⟩
def center1320 : GaussianRat :=
  ⟨-43475599/250000000, -199203157/1000000000⟩
def contact1320 : RatBall := localContactBall tau1320 center1320
def work1320 : RoundedTauEval :=
  evalTau precision tau1320 contact1320 logTwoBall

theorem center_sq1320 : (center1320.re : ℝ)^2 +
    (center1320.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1320]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1320 : work1320.theta.ok = true ∧
    work1320.jac.invOK = true ∧ acceptsUnitSq work1320.out = true := by
  norm_num [work1320, contact1320, tau1320, center1320, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1320 : CellCertificate where
  tauBall := tau1320
  contactCenter := center1320
  contactBall := contact1320
  work := work1320
  center_sq := center_sq1320
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1320.1
  jac_ok := checks1320.2.1
  accepted := checks1320.2.2

def tau1321 : RatBall :=
  ⟨⟨-73/320, -19/64⟩, 3/640⟩
def center1321 : GaussianRat :=
  ⟨-16950309/100000000, -199854009/1000000000⟩
def contact1321 : RatBall := localContactBall tau1321 center1321
def work1321 : RoundedTauEval :=
  evalTau precision tau1321 contact1321 logTwoBall

theorem center_sq1321 : (center1321.re : ℝ)^2 +
    (center1321.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1321]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1321 : work1321.theta.ok = true ∧
    work1321.jac.invOK = true ∧ acceptsUnitSq work1321.out = true := by
  norm_num [work1321, contact1321, tau1321, center1321, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1321 : CellCertificate where
  tauBall := tau1321
  contactCenter := center1321
  contactBall := contact1321
  work := work1321
  center_sq := center_sq1321
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1321.1
  jac_ok := checks1321.2.1
  accepted := checks1321.2.2

def tau1322 : RatBall :=
  ⟨⟨-15/64, -93/320⟩, 3/640⟩
def center1322 : GaussianRat :=
  ⟨-173254189/1000000000, -38963859/200000000⟩
def contact1322 : RatBall := localContactBall tau1322 center1322
def work1322 : RoundedTauEval :=
  evalTau precision tau1322 contact1322 logTwoBall

theorem center_sq1322 : (center1322.re : ℝ)^2 +
    (center1322.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1322]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1322 : work1322.theta.ok = true ∧
    work1322.jac.invOK = true ∧ acceptsUnitSq work1322.out = true := by
  norm_num [work1322, contact1322, tau1322, center1322, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1322 : CellCertificate where
  tauBall := tau1322
  contactCenter := center1322
  contactBall := contact1322
  work := work1322
  center_sq := center_sq1322
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1322.1
  jac_ok := checks1322.2.1
  accepted := checks1322.2.2

def tau1323 : RatBall :=
  ⟨⟨-73/320, -93/320⟩, 3/640⟩
def center1323 : GaussianRat :=
  ⟨-84433841/500000000, -195452163/1000000000⟩
def contact1323 : RatBall := localContactBall tau1323 center1323
def work1323 : RoundedTauEval :=
  evalTau precision tau1323 contact1323 logTwoBall

theorem center_sq1323 : (center1323.re : ℝ)^2 +
    (center1323.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1323]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1323 : work1323.theta.ok = true ∧
    work1323.jac.invOK = true ∧ acceptsUnitSq work1323.out = true := by
  norm_num [work1323, contact1323, tau1323, center1323, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1323 : CellCertificate where
  tauBall := tau1323
  contactCenter := center1323
  contactBall := contact1323
  work := work1323
  center_sq := center_sq1323
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1323.1
  jac_ok := checks1323.2.1
  accepted := checks1323.2.2

def tau1324 : RatBall :=
  ⟨⟨-79/320, -91/320⟩, 3/640⟩
def center1324 : GaussianRat :=
  ⟨-181318681/1000000000, -189181283/1000000000⟩
def contact1324 : RatBall := localContactBall tau1324 center1324
def work1324 : RoundedTauEval :=
  evalTau precision tau1324 contact1324 logTwoBall

theorem center_sq1324 : (center1324.re : ℝ)^2 +
    (center1324.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1324]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1324 : work1324.theta.ok = true ∧
    work1324.jac.invOK = true ∧ acceptsUnitSq work1324.out = true := by
  norm_num [work1324, contact1324, tau1324, center1324, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1324 : CellCertificate where
  tauBall := tau1324
  contactCenter := center1324
  contactBall := contact1324
  work := work1324
  center_sq := center_sq1324
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1324.1
  jac_ok := checks1324.2.1
  accepted := checks1324.2.2

def tau1325 : RatBall :=
  ⟨⟨-77/320, -91/320⟩, 3/640⟩
def center1325 : GaussianRat :=
  ⟨-17698031/100000000, -94910271/500000000⟩
def contact1325 : RatBall := localContactBall tau1325 center1325
def work1325 : RoundedTauEval :=
  evalTau precision tau1325 contact1325 logTwoBall

theorem center_sq1325 : (center1325.re : ℝ)^2 +
    (center1325.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1325]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1325 : work1325.theta.ok = true ∧
    work1325.jac.invOK = true ∧ acceptsUnitSq work1325.out = true := by
  norm_num [work1325, contact1325, tau1325, center1325, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1325 : CellCertificate where
  tauBall := tau1325
  contactCenter := center1325
  contactBall := contact1325
  work := work1325
  center_sq := center_sq1325
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1325.1
  jac_ok := checks1325.2.1
  accepted := checks1325.2.2

def tau1326 : RatBall :=
  ⟨⟨-79/320, -89/320⟩, 3/640⟩
def center1326 : GaussianRat :=
  ⟨-22585333/125000000, -184857737/1000000000⟩
def contact1326 : RatBall := localContactBall tau1326 center1326
def work1326 : RoundedTauEval :=
  evalTau precision tau1326 contact1326 logTwoBall

theorem center_sq1326 : (center1326.re : ℝ)^2 +
    (center1326.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1326]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1326 : work1326.theta.ok = true ∧
    work1326.jac.invOK = true ∧ acceptsUnitSq work1326.out = true := by
  norm_num [work1326, contact1326, tau1326, center1326, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1326 : CellCertificate where
  tauBall := tau1326
  contactCenter := center1326
  contactBall := contact1326
  work := work1326
  center_sq := center_sq1326
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1326.1
  jac_ok := checks1326.2.1
  accepted := checks1326.2.2

def tau1327 : RatBall :=
  ⟨⟨-77/320, -89/320⟩, 3/640⟩
def center1327 : GaussianRat :=
  ⟨-88177939/500000000, -185479027/1000000000⟩
def contact1327 : RatBall := localContactBall tau1327 center1327
def work1327 : RoundedTauEval :=
  evalTau precision tau1327 contact1327 logTwoBall

theorem center_sq1327 : (center1327.re : ℝ)^2 +
    (center1327.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1327]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1327 : work1327.theta.ok = true ∧
    work1327.jac.invOK = true ∧ acceptsUnitSq work1327.out = true := by
  norm_num [work1327, contact1327, tau1327, center1327, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1327 : CellCertificate where
  tauBall := tau1327
  contactCenter := center1327
  contactBall := contact1327
  work := work1327
  center_sq := center_sq1327
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1327.1
  jac_ok := checks1327.2.1
  accepted := checks1327.2.2

def cells : List CellCertificate := [cell1320, cell1321, cell1322, cell1323, cell1324, cell1325, cell1326, cell1327]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0155

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1240 : RatBall :=
  ⟨⟨-67/320, -99/320⟩, 3/640⟩
def center1240 : GaussianRat :=
  ⟨-157440099/1000000000, -210676827/1000000000⟩
def contact1240 : RatBall := localContactBall tau1240 center1240
def work1240 : RoundedTauEval :=
  evalTau precision tau1240 contact1240 logTwoBall

theorem center_sq1240 : (center1240.re : ℝ)^2 +
    (center1240.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1240]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1240 : work1240.theta.ok = true ∧
    work1240.jac.invOK = true ∧ acceptsUnitSq work1240.out = true := by
  norm_num [work1240, contact1240, tau1240, center1240, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1240 : CellCertificate where
  tauBall := tau1240
  contactCenter := center1240
  contactBall := contact1240
  work := work1240
  center_sq := center_sq1240
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1240.1
  jac_ok := checks1240.2.1
  accepted := checks1240.2.2

def tau1241 : RatBall :=
  ⟨⟨-13/64, -99/320⟩, 3/640⟩
def center1241 : GaussianRat :=
  ⟨-30588339/200000000, -211307539/1000000000⟩
def contact1241 : RatBall := localContactBall tau1241 center1241
def work1241 : RoundedTauEval :=
  evalTau precision tau1241 contact1241 logTwoBall

theorem center_sq1241 : (center1241.re : ℝ)^2 +
    (center1241.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1241]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1241 : work1241.theta.ok = true ∧
    work1241.jac.invOK = true ∧ acceptsUnitSq work1241.out = true := by
  norm_num [work1241, contact1241, tau1241, center1241, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1241 : CellCertificate where
  tauBall := tau1241
  contactCenter := center1241
  contactBall := contact1241
  work := work1241
  center_sq := center_sq1241
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1241.1
  jac_ok := checks1241.2.1
  accepted := checks1241.2.2

def tau1242 : RatBall :=
  ⟨⟨-67/320, -97/320⟩, 3/640⟩
def center1242 : GaussianRat :=
  ⟨-19601337/125000000, -103097251/500000000⟩
def contact1242 : RatBall := localContactBall tau1242 center1242
def work1242 : RoundedTauEval :=
  evalTau precision tau1242 contact1242 logTwoBall

theorem center_sq1242 : (center1242.re : ℝ)^2 +
    (center1242.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1242]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1242 : work1242.theta.ok = true ∧
    work1242.jac.invOK = true ∧ acceptsUnitSq work1242.out = true := by
  norm_num [work1242, contact1242, tau1242, center1242, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1242 : CellCertificate where
  tauBall := tau1242
  contactCenter := center1242
  contactBall := contact1242
  work := work1242
  center_sq := center_sq1242
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1242.1
  jac_ok := checks1242.2.1
  accepted := checks1242.2.2

def tau1243 : RatBall :=
  ⟨⟨-13/64, -97/320⟩, 3/640⟩
def center1243 : GaussianRat :=
  ⟨-9520441/62500000, -206807941/1000000000⟩
def contact1243 : RatBall := localContactBall tau1243 center1243
def work1243 : RoundedTauEval :=
  evalTau precision tau1243 contact1243 logTwoBall

theorem center_sq1243 : (center1243.re : ℝ)^2 +
    (center1243.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1243]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1243 : work1243.theta.ok = true ∧
    work1243.jac.invOK = true ∧ acceptsUnitSq work1243.out = true := by
  norm_num [work1243, contact1243, tau1243, center1243, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1243 : CellCertificate where
  tauBall := tau1243
  contactCenter := center1243
  contactBall := contact1243
  work := work1243
  center_sq := center_sq1243
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1243.1
  jac_ok := checks1243.2.1
  accepted := checks1243.2.2

def tau1244 : RatBall :=
  ⟨⟨-97/320, -17/64⟩, 3/640⟩
def center1244 : GaussianRat :=
  ⟨-54347721/250000000, -170518079/1000000000⟩
def contact1244 : RatBall := localContactBall tau1244 center1244
def work1244 : RoundedTauEval :=
  evalTau precision tau1244 contact1244 logTwoBall

theorem center_sq1244 : (center1244.re : ℝ)^2 +
    (center1244.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1244 : work1244.theta.ok = true ∧
    work1244.jac.invOK = true ∧ acceptsUnitSq work1244.out = true := by
  norm_num [work1244, contact1244, tau1244, center1244, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1244 : CellCertificate where
  tauBall := tau1244
  contactCenter := center1244
  contactBall := contact1244
  work := work1244
  center_sq := center_sq1244
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1244.1
  jac_ok := checks1244.2.1
  accepted := checks1244.2.2

def tau1245 : RatBall :=
  ⟨⟨-99/320, -83/320⟩, 3/640⟩
def center1245 : GaussianRat :=
  ⟨-110417413/500000000, -165731261/1000000000⟩
def contact1245 : RatBall := localContactBall tau1245 center1245
def work1245 : RoundedTauEval :=
  evalTau precision tau1245 contact1245 logTwoBall

theorem center_sq1245 : (center1245.re : ℝ)^2 +
    (center1245.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1245]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1245 : work1245.theta.ok = true ∧
    work1245.jac.invOK = true ∧ acceptsUnitSq work1245.out = true := by
  norm_num [work1245, contact1245, tau1245, center1245, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1245 : CellCertificate where
  tauBall := tau1245
  contactCenter := center1245
  contactBall := contact1245
  work := work1245
  center_sq := center_sq1245
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1245.1
  jac_ok := checks1245.2.1
  accepted := checks1245.2.2

def tau1246 : RatBall :=
  ⟨⟨-97/320, -83/320⟩, 3/640⟩
def center1246 : GaussianRat :=
  ⟨-108361733/500000000, -83196503/500000000⟩
def contact1246 : RatBall := localContactBall tau1246 center1246
def work1246 : RoundedTauEval :=
  evalTau precision tau1246 contact1246 logTwoBall

theorem center_sq1246 : (center1246.re : ℝ)^2 +
    (center1246.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1246]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1246 : work1246.theta.ok = true ∧
    work1246.jac.invOK = true ∧ acceptsUnitSq work1246.out = true := by
  norm_num [work1246, contact1246, tau1246, center1246, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1246 : CellCertificate where
  tauBall := tau1246
  contactCenter := center1246
  contactBall := contact1246
  work := work1246
  center_sq := center_sq1246
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1246.1
  jac_ok := checks1246.2.1
  accepted := checks1246.2.2

def tau1247 : RatBall :=
  ⟨⟨-99/320, -81/320⟩, 3/640⟩
def center1247 : GaussianRat :=
  ⟨-55044701/250000000, -161633449/1000000000⟩
def contact1247 : RatBall := localContactBall tau1247 center1247
def work1247 : RoundedTauEval :=
  evalTau precision tau1247 contact1247 logTwoBall

theorem center_sq1247 : (center1247.re : ℝ)^2 +
    (center1247.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1247]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1247 : work1247.theta.ok = true ∧
    work1247.jac.invOK = true ∧ acceptsUnitSq work1247.out = true := by
  norm_num [work1247, contact1247, tau1247, center1247, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1247 : CellCertificate where
  tauBall := tau1247
  contactCenter := center1247
  contactBall := contact1247
  work := work1247
  center_sq := center_sq1247
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1247.1
  jac_ok := checks1247.2.1
  accepted := checks1247.2.2

def cells : List CellCertificate := [cell1240, cell1241, cell1242, cell1243, cell1244, cell1245, cell1246, cell1247]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0155

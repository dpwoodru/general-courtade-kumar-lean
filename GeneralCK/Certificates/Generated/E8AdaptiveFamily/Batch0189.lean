import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1512 : RatBall :=
  ⟨⟨-11/320, -23/64⟩, 3/640⟩
def center1512 : GaussianRat :=
  ⟨-27492413/1000000000, -2037657/7812500⟩
def contact1512 : RatBall := localContactBall tau1512 center1512
def work1512 : RoundedTauEval :=
  evalTau precision tau1512 contact1512 logTwoBall

theorem center_sq1512 : (center1512.re : ℝ)^2 +
    (center1512.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1512]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1512 : work1512.theta.ok = true ∧
    work1512.jac.invOK = true ∧ acceptsUnitSq work1512.out = true := by
  norm_num [work1512, contact1512, tau1512, center1512, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1512 : CellCertificate where
  tauBall := tau1512
  contactCenter := center1512
  contactBall := contact1512
  work := work1512
  center_sq := center_sq1512
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1512.1
  jac_ok := checks1512.2.1
  accepted := checks1512.2.2

def tau1513 : RatBall :=
  ⟨⟨-9/320, -23/64⟩, 3/640⟩
def center1513 : GaussianRat :=
  ⟨-22499417/1000000000, -260954001/1000000000⟩
def contact1513 : RatBall := localContactBall tau1513 center1513
def work1513 : RoundedTauEval :=
  evalTau precision tau1513 contact1513 logTwoBall

theorem center_sq1513 : (center1513.re : ℝ)^2 +
    (center1513.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1513]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1513 : work1513.theta.ok = true ∧
    work1513.jac.invOK = true ∧ acceptsUnitSq work1513.out = true := by
  norm_num [work1513, contact1513, tau1513, center1513, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1513 : CellCertificate where
  tauBall := tau1513
  contactCenter := center1513
  contactBall := contact1513
  work := work1513
  center_sq := center_sq1513
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1513.1
  jac_ok := checks1513.2.1
  accepted := checks1513.2.2

def tau1514 : RatBall :=
  ⟨⟨-11/320, -113/320⟩, 3/640⟩
def center1514 : GaussianRat :=
  ⟨-5469449/200000000, -51168439/200000000⟩
def contact1514 : RatBall := localContactBall tau1514 center1514
def work1514 : RoundedTauEval :=
  evalTau precision tau1514 contact1514 logTwoBall

theorem center_sq1514 : (center1514.re : ℝ)^2 +
    (center1514.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1514]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1514 : work1514.theta.ok = true ∧
    work1514.jac.invOK = true ∧ acceptsUnitSq work1514.out = true := by
  norm_num [work1514, contact1514, tau1514, center1514, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1514 : CellCertificate where
  tauBall := tau1514
  contactCenter := center1514
  contactBall := contact1514
  work := work1514
  center_sq := center_sq1514
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1514.1
  jac_ok := checks1514.2.1
  accepted := checks1514.2.2

def tau1515 : RatBall :=
  ⟨⟨-9/320, -113/320⟩, 3/640⟩
def center1515 : GaussianRat :=
  ⟨-22380501/1000000000, -127986203/500000000⟩
def contact1515 : RatBall := localContactBall tau1515 center1515
def work1515 : RoundedTauEval :=
  evalTau precision tau1515 contact1515 logTwoBall

theorem center_sq1515 : (center1515.re : ℝ)^2 +
    (center1515.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1515]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1515 : work1515.theta.ok = true ∧
    work1515.jac.invOK = true ∧ acceptsUnitSq work1515.out = true := by
  norm_num [work1515, contact1515, tau1515, center1515, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1515 : CellCertificate where
  tauBall := tau1515
  contactCenter := center1515
  contactBall := contact1515
  work := work1515
  center_sq := center_sq1515
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1515.1
  jac_ok := checks1515.2.1
  accepted := checks1515.2.2

def tau1516 : RatBall :=
  ⟨⟨-7/320, -119/320⟩, 3/640⟩
def center1516 : GaussianRat :=
  ⟨-3539231/200000000, -67777837/250000000⟩
def contact1516 : RatBall := localContactBall tau1516 center1516
def work1516 : RoundedTauEval :=
  evalTau precision tau1516 contact1516 logTwoBall

theorem center_sq1516 : (center1516.re : ℝ)^2 +
    (center1516.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1516]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1516 : work1516.theta.ok = true ∧
    work1516.jac.invOK = true ∧ acceptsUnitSq work1516.out = true := by
  norm_num [work1516, contact1516, tau1516, center1516, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1516 : CellCertificate where
  tauBall := tau1516
  contactCenter := center1516
  contactBall := contact1516
  work := work1516
  center_sq := center_sq1516
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1516.1
  jac_ok := checks1516.2.1
  accepted := checks1516.2.2

def tau1517 : RatBall :=
  ⟨⟨-1/64, -119/320⟩, 3/640⟩
def center1517 : GaussianRat :=
  ⟨-1264209/100000000, -27119647/100000000⟩
def contact1517 : RatBall := localContactBall tau1517 center1517
def work1517 : RoundedTauEval :=
  evalTau precision tau1517 contact1517 logTwoBall

theorem center_sq1517 : (center1517.re : ℝ)^2 +
    (center1517.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1517]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1517 : work1517.theta.ok = true ∧
    work1517.jac.invOK = true ∧ acceptsUnitSq work1517.out = true := by
  norm_num [work1517, contact1517, tau1517, center1517, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1517 : CellCertificate where
  tauBall := tau1517
  contactCenter := center1517
  contactBall := contact1517
  work := work1517
  center_sq := center_sq1517
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1517.1
  jac_ok := checks1517.2.1
  accepted := checks1517.2.2

def tau1518 : RatBall :=
  ⟨⟨-7/320, -117/320⟩, 3/640⟩
def center1518 : GaussianRat :=
  ⟨-3519651/200000000, -8314767/31250000⟩
def contact1518 : RatBall := localContactBall tau1518 center1518
def work1518 : RoundedTauEval :=
  evalTau precision tau1518 contact1518 logTwoBall

theorem center_sq1518 : (center1518.re : ℝ)^2 +
    (center1518.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1518]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1518 : work1518.theta.ok = true ∧
    work1518.jac.invOK = true ∧ acceptsUnitSq work1518.out = true := by
  norm_num [work1518, contact1518, tau1518, center1518, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1518 : CellCertificate where
  tauBall := tau1518
  contactCenter := center1518
  contactBall := contact1518
  work := work1518
  center_sq := center_sq1518
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1518.1
  jac_ok := checks1518.2.1
  accepted := checks1518.2.2

def tau1519 : RatBall :=
  ⟨⟨-1/64, -117/320⟩, 3/640⟩
def center1519 : GaussianRat :=
  ⟨-1257211/100000000, -66538831/250000000⟩
def contact1519 : RatBall := localContactBall tau1519 center1519
def work1519 : RoundedTauEval :=
  evalTau precision tau1519 contact1519 logTwoBall

theorem center_sq1519 : (center1519.re : ℝ)^2 +
    (center1519.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1519]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1519 : work1519.theta.ok = true ∧
    work1519.jac.invOK = true ∧ acceptsUnitSq work1519.out = true := by
  norm_num [work1519, contact1519, tau1519, center1519, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1519 : CellCertificate where
  tauBall := tau1519
  contactCenter := center1519
  contactBall := contact1519
  work := work1519
  center_sq := center_sq1519
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1519.1
  jac_ok := checks1519.2.1
  accepted := checks1519.2.2

def cells : List CellCertificate := [cell1512, cell1513, cell1514, cell1515, cell1516, cell1517, cell1518, cell1519]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

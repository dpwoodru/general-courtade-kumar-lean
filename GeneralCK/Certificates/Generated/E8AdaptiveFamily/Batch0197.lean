import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1576 : RatBall :=
  ⟨⟨9/320, -113/320⟩, 3/640⟩
def center1576 : GaussianRat :=
  ⟨22380501/1000000000, -127986203/500000000⟩
def contact1576 : RatBall := localContactBall tau1576 center1576
def work1576 : RoundedTauEval :=
  evalTau precision tau1576 contact1576 logTwoBall

theorem center_sq1576 : (center1576.re : ℝ)^2 +
    (center1576.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1576]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1576 : work1576.theta.ok = true ∧
    work1576.jac.invOK = true ∧ acceptsUnitSq work1576.out = true := by
  norm_num [work1576, contact1576, tau1576, center1576, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1576 : CellCertificate where
  tauBall := tau1576
  contactCenter := center1576
  contactBall := contact1576
  work := work1576
  center_sq := center_sq1576
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1576.1
  jac_ok := checks1576.2.1
  accepted := checks1576.2.2

def tau1577 : RatBall :=
  ⟨⟨11/320, -113/320⟩, 3/640⟩
def center1577 : GaussianRat :=
  ⟨5469449/200000000, -51168439/200000000⟩
def contact1577 : RatBall := localContactBall tau1577 center1577
def work1577 : RoundedTauEval :=
  evalTau precision tau1577 contact1577 logTwoBall

theorem center_sq1577 : (center1577.re : ℝ)^2 +
    (center1577.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1577]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1577 : work1577.theta.ok = true ∧
    work1577.jac.invOK = true ∧ acceptsUnitSq work1577.out = true := by
  norm_num [work1577, contact1577, tau1577, center1577, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1577 : CellCertificate where
  tauBall := tau1577
  contactCenter := center1577
  contactBall := contact1577
  work := work1577
  center_sq := center_sq1577
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1577.1
  jac_ok := checks1577.2.1
  accepted := checks1577.2.2

def tau1578 : RatBall :=
  ⟨⟨13/320, -23/64⟩, 3/640⟩
def center1578 : GaussianRat :=
  ⟨32481297/1000000000, -260659621/1000000000⟩
def contact1578 : RatBall := localContactBall tau1578 center1578
def work1578 : RoundedTauEval :=
  evalTau precision tau1578 contact1578 logTwoBall

theorem center_sq1578 : (center1578.re : ℝ)^2 +
    (center1578.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1578]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1578 : work1578.theta.ok = true ∧
    work1578.jac.invOK = true ∧ acceptsUnitSq work1578.out = true := by
  norm_num [work1578, contact1578, tau1578, center1578, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1578 : CellCertificate where
  tauBall := tau1578
  contactCenter := center1578
  contactBall := contact1578
  work := work1578
  center_sq := center_sq1578
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1578.1
  jac_ok := checks1578.2.1
  accepted := checks1578.2.2

def tau1579 : RatBall :=
  ⟨⟨3/64, -23/64⟩, 3/640⟩
def center1579 : GaussianRat :=
  ⟨37465331/1000000000, -260472693/1000000000⟩
def contact1579 : RatBall := localContactBall tau1579 center1579
def work1579 : RoundedTauEval :=
  evalTau precision tau1579 contact1579 logTwoBall

theorem center_sq1579 : (center1579.re : ℝ)^2 +
    (center1579.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1579]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1579 : work1579.theta.ok = true ∧
    work1579.jac.invOK = true ∧ acceptsUnitSq work1579.out = true := by
  norm_num [work1579, contact1579, tau1579, center1579, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1579 : CellCertificate where
  tauBall := tau1579
  contactCenter := center1579
  contactBall := contact1579
  work := work1579
  center_sq := center_sq1579
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1579.1
  jac_ok := checks1579.2.1
  accepted := checks1579.2.2

def tau1580 : RatBall :=
  ⟨⟨13/320, -113/320⟩, 3/640⟩
def center1580 : GaussianRat :=
  ⟨32309979/1000000000, -127843073/500000000⟩
def contact1580 : RatBall := localContactBall tau1580 center1580
def work1580 : RoundedTauEval :=
  evalTau precision tau1580 contact1580 logTwoBall

theorem center_sq1580 : (center1580.re : ℝ)^2 +
    (center1580.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1580]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1580 : work1580.theta.ok = true ∧
    work1580.jac.invOK = true ∧ acceptsUnitSq work1580.out = true := by
  norm_num [work1580, contact1580, tau1580, center1580, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1580 : CellCertificate where
  tauBall := tau1580
  contactCenter := center1580
  contactBall := contact1580
  work := work1580
  center_sq := center_sq1580
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1580.1
  jac_ok := checks1580.2.1
  accepted := checks1580.2.2

def tau1581 : RatBall :=
  ⟨⟨3/64, -113/320⟩, 3/640⟩
def center1581 : GaussianRat :=
  ⟨18633993/500000000, -15969023/62500000⟩
def contact1581 : RatBall := localContactBall tau1581 center1581
def work1581 : RoundedTauEval :=
  evalTau precision tau1581 contact1581 logTwoBall

theorem center_sq1581 : (center1581.re : ℝ)^2 +
    (center1581.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1581]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1581 : work1581.theta.ok = true ∧
    work1581.jac.invOK = true ∧ acceptsUnitSq work1581.out = true := by
  norm_num [work1581, contact1581, tau1581, center1581, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1581 : CellCertificate where
  tauBall := tau1581
  contactCenter := center1581
  contactBall := contact1581
  work := work1581
  center_sq := center_sq1581
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1581.1
  jac_ok := checks1581.2.1
  accepted := checks1581.2.2

def tau1582 : RatBall :=
  ⟨⟨17/320, -121/320⟩, 3/640⟩
def center1582 : GaussianRat :=
  ⟨8630399/200000000, -275306779/1000000000⟩
def contact1582 : RatBall := localContactBall tau1582 center1582
def work1582 : RoundedTauEval :=
  evalTau precision tau1582 contact1582 logTwoBall

theorem center_sq1582 : (center1582.re : ℝ)^2 +
    (center1582.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1582]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1582 : work1582.theta.ok = true ∧
    work1582.jac.invOK = true ∧ acceptsUnitSq work1582.out = true := by
  norm_num [work1582, contact1582, tau1582, center1582, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1582 : CellCertificate where
  tauBall := tau1582
  contactCenter := center1582
  contactBall := contact1582
  work := work1582
  center_sq := center_sq1582
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1582.1
  jac_ok := checks1582.2.1
  accepted := checks1582.2.2

def tau1583 : RatBall :=
  ⟨⟨19/320, -121/320⟩, 3/640⟩
def center1583 : GaussianRat :=
  ⟨48205717/1000000000, -275046561/1000000000⟩
def contact1583 : RatBall := localContactBall tau1583 center1583
def work1583 : RoundedTauEval :=
  evalTau precision tau1583 contact1583 logTwoBall

theorem center_sq1583 : (center1583.re : ℝ)^2 +
    (center1583.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1583]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1583 : work1583.theta.ok = true ∧
    work1583.jac.invOK = true ∧ acceptsUnitSq work1583.out = true := by
  norm_num [work1583, contact1583, tau1583, center1583, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1583 : CellCertificate where
  tauBall := tau1583
  contactCenter := center1583
  contactBall := contact1583
  work := work1583
  center_sq := center_sq1583
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1583.1
  jac_ok := checks1583.2.1
  accepted := checks1583.2.2

def cells : List CellCertificate := [cell1576, cell1577, cell1578, cell1579, cell1580, cell1581, cell1582, cell1583]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197

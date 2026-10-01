import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1568 : RatBall :=
  ⟨⟨9/320, -117/320⟩, 3/640⟩
def center1568 : GaussianRat :=
  ⟨4524341/200000000, -53192453/200000000⟩
def contact1568 : RatBall := localContactBall tau1568 center1568
def work1568 : RoundedTauEval :=
  evalTau precision tau1568 contact1568 logTwoBall

theorem center_sq1568 : (center1568.re : ℝ)^2 +
    (center1568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1568 : work1568.theta.ok = true ∧
    work1568.jac.invOK = true ∧ acceptsUnitSq work1568.out = true := by
  norm_num [work1568, contact1568, tau1568, center1568, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1568 : CellCertificate where
  tauBall := tau1568
  contactCenter := center1568
  contactBall := contact1568
  work := work1568
  center_sq := center_sq1568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1568.1
  jac_ok := checks1568.2.1
  accepted := checks1568.2.2

def tau1569 : RatBall :=
  ⟨⟨11/320, -117/320⟩, 3/640⟩
def center1569 : GaussianRat :=
  ⟨863803/31250000, -33228071/125000000⟩
def contact1569 : RatBall := localContactBall tau1569 center1569
def work1569 : RoundedTauEval :=
  evalTau precision tau1569 contact1569 logTwoBall

theorem center_sq1569 : (center1569.re : ℝ)^2 +
    (center1569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1569 : work1569.theta.ok = true ∧
    work1569.jac.invOK = true ∧ acceptsUnitSq work1569.out = true := by
  norm_num [work1569, contact1569, tau1569, center1569, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1569 : CellCertificate where
  tauBall := tau1569
  contactCenter := center1569
  contactBall := contact1569
  work := work1569
  center_sq := center_sq1569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1569.1
  jac_ok := checks1569.2.1
  accepted := checks1569.2.2

def tau1570 : RatBall :=
  ⟨⟨13/320, -119/320⟩, 3/640⟩
def center1570 : GaussianRat :=
  ⟨32838611/1000000000, -135343343/500000000⟩
def contact1570 : RatBall := localContactBall tau1570 center1570
def work1570 : RoundedTauEval :=
  evalTau precision tau1570 contact1570 logTwoBall

theorem center_sq1570 : (center1570.re : ℝ)^2 +
    (center1570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1570 : work1570.theta.ok = true ∧
    work1570.jac.invOK = true ∧ acceptsUnitSq work1570.out = true := by
  norm_num [work1570, contact1570, tau1570, center1570, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1570 : CellCertificate where
  tauBall := tau1570
  contactCenter := center1570
  contactBall := contact1570
  work := work1570
  center_sq := center_sq1570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1570.1
  jac_ok := checks1570.2.1
  accepted := checks1570.2.2

def tau1571 : RatBall :=
  ⟨⟨3/64, -119/320⟩, 3/640⟩
def center1571 : GaussianRat :=
  ⟨18938457/500000000, -5409781/20000000⟩
def contact1571 : RatBall := localContactBall tau1571 center1571
def work1571 : RoundedTauEval :=
  evalTau precision tau1571 contact1571 logTwoBall

theorem center_sq1571 : (center1571.re : ℝ)^2 +
    (center1571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1571 : work1571.theta.ok = true ∧
    work1571.jac.invOK = true ∧ acceptsUnitSq work1571.out = true := by
  norm_num [work1571, contact1571, tau1571, center1571, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1571 : CellCertificate where
  tauBall := tau1571
  contactCenter := center1571
  contactBall := contact1571
  work := work1571
  center_sq := center_sq1571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1571.1
  jac_ok := checks1571.2.1
  accepted := checks1571.2.2

def tau1572 : RatBall :=
  ⟨⟨13/320, -117/320⟩, 3/640⟩
def center1572 : GaussianRat :=
  ⟨6531493/200000000, -265659553/1000000000⟩
def contact1572 : RatBall := localContactBall tau1572 center1572
def work1572 : RoundedTauEval :=
  evalTau precision tau1572 contact1572 logTwoBall

theorem center_sq1572 : (center1572.re : ℝ)^2 +
    (center1572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1572 : work1572.theta.ok = true ∧
    work1572.jac.invOK = true ∧ acceptsUnitSq work1572.out = true := by
  norm_num [work1572, contact1572, tau1572, center1572, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1572 : CellCertificate where
  tauBall := tau1572
  contactCenter := center1572
  contactBall := contact1572
  work := work1572
  center_sq := center_sq1572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1572.1
  jac_ok := checks1572.2.1
  accepted := checks1572.2.2

def tau1573 : RatBall :=
  ⟨⟨3/64, -117/320⟩, 3/640⟩
def center1573 : GaussianRat :=
  ⟨18834129/500000000, -13273367/50000000⟩
def contact1573 : RatBall := localContactBall tau1573 center1573
def work1573 : RoundedTauEval :=
  evalTau precision tau1573 contact1573 logTwoBall

theorem center_sq1573 : (center1573.re : ℝ)^2 +
    (center1573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1573 : work1573.theta.ok = true ∧
    work1573.jac.invOK = true ∧ acceptsUnitSq work1573.out = true := by
  norm_num [work1573, contact1573, tau1573, center1573, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1573 : CellCertificate where
  tauBall := tau1573
  contactCenter := center1573
  contactBall := contact1573
  work := work1573
  center_sq := center_sq1573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1573.1
  jac_ok := checks1573.2.1
  accepted := checks1573.2.2

def tau1574 : RatBall :=
  ⟨⟨9/320, -23/64⟩, 3/640⟩
def center1574 : GaussianRat :=
  ⟨22499417/1000000000, -260954001/1000000000⟩
def contact1574 : RatBall := localContactBall tau1574 center1574
def work1574 : RoundedTauEval :=
  evalTau precision tau1574 contact1574 logTwoBall

theorem center_sq1574 : (center1574.re : ℝ)^2 +
    (center1574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1574 : work1574.theta.ok = true ∧
    work1574.jac.invOK = true ∧ acceptsUnitSq work1574.out = true := by
  norm_num [work1574, contact1574, tau1574, center1574, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1574 : CellCertificate where
  tauBall := tau1574
  contactCenter := center1574
  contactBall := contact1574
  work := work1574
  center_sq := center_sq1574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1574.1
  jac_ok := checks1574.2.1
  accepted := checks1574.2.2

def tau1575 : RatBall :=
  ⟨⟨11/320, -23/64⟩, 3/640⟩
def center1575 : GaussianRat :=
  ⟨27492413/1000000000, -2037657/7812500⟩
def contact1575 : RatBall := localContactBall tau1575 center1575
def work1575 : RoundedTauEval :=
  evalTau precision tau1575 contact1575 logTwoBall

theorem center_sq1575 : (center1575.re : ℝ)^2 +
    (center1575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1575 : work1575.theta.ok = true ∧
    work1575.jac.invOK = true ∧ acceptsUnitSq work1575.out = true := by
  norm_num [work1575, contact1575, tau1575, center1575, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1575 : CellCertificate where
  tauBall := tau1575
  contactCenter := center1575
  contactBall := contact1575
  work := work1575
  center_sq := center_sq1575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1575.1
  jac_ok := checks1575.2.1
  accepted := checks1575.2.2

def cells : List CellCertificate := [cell1568, cell1569, cell1570, cell1571, cell1572, cell1573, cell1574, cell1575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196

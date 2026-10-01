import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0199

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1592 : RatBall :=
  ⟨⟨23/320, -117/320⟩, 3/640⟩
def center1592 : GaussianRat :=
  ⟨57646751/1000000000, -52885917/200000000⟩
def contact1592 : RatBall := localContactBall tau1592 center1592
def work1592 : RoundedTauEval :=
  evalTau precision tau1592 contact1592 logTwoBall

theorem center_sq1592 : (center1592.re : ℝ)^2 +
    (center1592.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1592]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1592 : work1592.theta.ok = true ∧
    work1592.jac.invOK = true ∧ acceptsUnitSq work1592.out = true := by
  norm_num [work1592, contact1592, tau1592, center1592, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1592 : CellCertificate where
  tauBall := tau1592
  contactCenter := center1592
  contactBall := contact1592
  work := work1592
  center_sq := center_sq1592
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1592.1
  jac_ok := checks1592.2.1
  accepted := checks1592.2.2

def tau1593 : RatBall :=
  ⟨⟨17/320, -23/64⟩, 3/640⟩
def center1593 : GaussianRat :=
  ⟨5305473/125000000, -65064861/250000000⟩
def contact1593 : RatBall := localContactBall tau1593 center1593
def work1593 : RoundedTauEval :=
  evalTau precision tau1593 contact1593 logTwoBall

theorem center_sq1593 : (center1593.re : ℝ)^2 +
    (center1593.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1593]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1593 : work1593.theta.ok = true ∧
    work1593.jac.invOK = true ∧ acceptsUnitSq work1593.out = true := by
  norm_num [work1593, contact1593, tau1593, center1593, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1593 : CellCertificate where
  tauBall := tau1593
  contactCenter := center1593
  contactBall := contact1593
  work := work1593
  center_sq := center_sq1593
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1593.1
  jac_ok := checks1593.2.1
  accepted := checks1593.2.2

def tau1594 : RatBall :=
  ⟨⟨19/320, -23/64⟩, 3/640⟩
def center1594 : GaussianRat :=
  ⟨47415929/1000000000, -260020027/1000000000⟩
def contact1594 : RatBall := localContactBall tau1594 center1594
def work1594 : RoundedTauEval :=
  evalTau precision tau1594 contact1594 logTwoBall

theorem center_sq1594 : (center1594.re : ℝ)^2 +
    (center1594.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1594]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1594 : work1594.theta.ok = true ∧
    work1594.jac.invOK = true ∧ acceptsUnitSq work1594.out = true := by
  norm_num [work1594, contact1594, tau1594, center1594, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1594 : CellCertificate where
  tauBall := tau1594
  contactCenter := center1594
  contactBall := contact1594
  work := work1594
  center_sq := center_sq1594
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1594.1
  jac_ok := checks1594.2.1
  accepted := checks1594.2.2

def tau1595 : RatBall :=
  ⟨⟨17/320, -113/320⟩, 3/640⟩
def center1595 : GaussianRat :=
  ⟨42220551/1000000000, -25529699/100000000⟩
def contact1595 : RatBall := localContactBall tau1595 center1595
def work1595 : RoundedTauEval :=
  evalTau precision tau1595 contact1595 logTwoBall

theorem center_sq1595 : (center1595.re : ℝ)^2 +
    (center1595.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1595]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1595 : work1595.theta.ok = true ∧
    work1595.jac.invOK = true ∧ acceptsUnitSq work1595.out = true := by
  norm_num [work1595, contact1595, tau1595, center1595, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1595 : CellCertificate where
  tauBall := tau1595
  contactCenter := center1595
  contactBall := contact1595
  work := work1595
  center_sq := center_sq1595
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1595.1
  jac_ok := checks1595.2.1
  accepted := checks1595.2.2

def tau1596 : RatBall :=
  ⟨⟨19/320, -113/320⟩, 3/640⟩
def center1596 : GaussianRat :=
  ⟨47166967/1000000000, -255064157/1000000000⟩
def contact1596 : RatBall := localContactBall tau1596 center1596
def work1596 : RoundedTauEval :=
  evalTau precision tau1596 contact1596 logTwoBall

theorem center_sq1596 : (center1596.re : ℝ)^2 +
    (center1596.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1596]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1596 : work1596.theta.ok = true ∧
    work1596.jac.invOK = true ∧ acceptsUnitSq work1596.out = true := by
  norm_num [work1596, contact1596, tau1596, center1596, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1596 : CellCertificate where
  tauBall := tau1596
  contactCenter := center1596
  contactBall := contact1596
  work := work1596
  center_sq := center_sq1596
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1596.1
  jac_ok := checks1596.2.1
  accepted := checks1596.2.2

def tau1597 : RatBall :=
  ⟨⟨21/320, -23/64⟩, 3/640⟩
def center1597 : GaussianRat :=
  ⟨6547631/125000000, -64938653/250000000⟩
def contact1597 : RatBall := localContactBall tau1597 center1597
def work1597 : RoundedTauEval :=
  evalTau precision tau1597 contact1597 logTwoBall

theorem center_sq1597 : (center1597.re : ℝ)^2 +
    (center1597.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1597]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1597 : work1597.theta.ok = true ∧
    work1597.jac.invOK = true ∧ acceptsUnitSq work1597.out = true := by
  norm_num [work1597, contact1597, tau1597, center1597, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1597 : CellCertificate where
  tauBall := tau1597
  contactCenter := center1597
  contactBall := contact1597
  work := work1597
  center_sq := center_sq1597
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1597.1
  jac_ok := checks1597.2.1
  accepted := checks1597.2.2

def tau1598 : RatBall :=
  ⟨⟨23/320, -23/64⟩, 3/640⟩
def center1598 : GaussianRat :=
  ⟨5733843/100000000, -129731693/500000000⟩
def contact1598 : RatBall := localContactBall tau1598 center1598
def work1598 : RoundedTauEval :=
  evalTau precision tau1598 contact1598 logTwoBall

theorem center_sq1598 : (center1598.re : ℝ)^2 +
    (center1598.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1598]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1598 : work1598.theta.ok = true ∧
    work1598.jac.invOK = true ∧ acceptsUnitSq work1598.out = true := by
  norm_num [work1598, contact1598, tau1598, center1598, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1598 : CellCertificate where
  tauBall := tau1598
  contactCenter := center1598
  contactBall := contact1598
  work := work1598
  center_sq := center_sq1598
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1598.1
  jac_ok := checks1598.2.1
  accepted := checks1598.2.2

def tau1599 : RatBall :=
  ⟨⟨21/320, -113/320⟩, 3/640⟩
def center1599 : GaussianRat :=
  ⟨13026633/250000000, -254806033/1000000000⟩
def contact1599 : RatBall := localContactBall tau1599 center1599
def work1599 : RoundedTauEval :=
  evalTau precision tau1599 contact1599 logTwoBall

theorem center_sq1599 : (center1599.re : ℝ)^2 +
    (center1599.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1599]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1599 : work1599.theta.ok = true ∧
    work1599.jac.invOK = true ∧ acceptsUnitSq work1599.out = true := by
  norm_num [work1599, contact1599, tau1599, center1599, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1599 : CellCertificate where
  tauBall := tau1599
  contactCenter := center1599
  contactBall := contact1599
  work := work1599
  center_sq := center_sq1599
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1599.1
  jac_ok := checks1599.2.1
  accepted := checks1599.2.2

def cells : List CellCertificate := [cell1592, cell1593, cell1594, cell1595, cell1596, cell1597, cell1598, cell1599]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0199

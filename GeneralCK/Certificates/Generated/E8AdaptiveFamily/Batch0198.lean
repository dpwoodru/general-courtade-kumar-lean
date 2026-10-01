import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1584 : RatBall :=
  ⟨⟨21/320, -121/320⟩, 3/640⟩
def center1584 : GaussianRat :=
  ⟨53251841/1000000000, -54951623/200000000⟩
def contact1584 : RatBall := localContactBall tau1584 center1584
def work1584 : RoundedTauEval :=
  evalTau precision tau1584 contact1584 logTwoBall

theorem center_sq1584 : (center1584.re : ℝ)^2 +
    (center1584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1584 : work1584.theta.ok = true ∧
    work1584.jac.invOK = true ∧ acceptsUnitSq work1584.out = true := by
  norm_num [work1584, contact1584, tau1584, center1584, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1584 : CellCertificate where
  tauBall := tau1584
  contactCenter := center1584
  contactBall := contact1584
  work := work1584
  center_sq := center_sq1584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1584.1
  jac_ok := checks1584.2.1
  accepted := checks1584.2.2

def tau1585 : RatBall :=
  ⟨⟨17/320, -119/320⟩, 3/640⟩
def center1585 : GaussianRat :=
  ⟨42909337/1000000000, -135131799/500000000⟩
def contact1585 : RatBall := localContactBall tau1585 center1585
def work1585 : RoundedTauEval :=
  evalTau precision tau1585 contact1585 logTwoBall

theorem center_sq1585 : (center1585.re : ℝ)^2 +
    (center1585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1585 : work1585.theta.ok = true ∧
    work1585.jac.invOK = true ∧ acceptsUnitSq work1585.out = true := by
  norm_num [work1585, contact1585, tau1585, center1585, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1585 : CellCertificate where
  tauBall := tau1585
  contactCenter := center1585
  contactBall := contact1585
  work := work1585
  center_sq := center_sq1585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1585.1
  jac_ok := checks1585.2.1
  accepted := checks1585.2.2

def tau1586 : RatBall :=
  ⟨⟨19/320, -119/320⟩, 3/640⟩
def center1586 : GaussianRat :=
  ⟨47935117/1000000000, -2109457/7812500⟩
def contact1586 : RatBall := localContactBall tau1586 center1586
def work1586 : RoundedTauEval :=
  evalTau precision tau1586 contact1586 logTwoBall

theorem center_sq1586 : (center1586.re : ℝ)^2 +
    (center1586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1586 : work1586.theta.ok = true ∧
    work1586.jac.invOK = true ∧ acceptsUnitSq work1586.out = true := by
  norm_num [work1586, contact1586, tau1586, center1586, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1586 : CellCertificate where
  tauBall := tau1586
  contactCenter := center1586
  contactBall := contact1586
  work := work1586
  center_sq := center_sq1586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1586.1
  jac_ok := checks1586.2.1
  accepted := checks1586.2.2

def tau1587 : RatBall :=
  ⟨⟨17/320, -117/320⟩, 3/640⟩
def center1587 : GaussianRat :=
  ⟨10668331/250000000, -265248069/1000000000⟩
def contact1587 : RatBall := localContactBall tau1587 center1587
def work1587 : RoundedTauEval :=
  evalTau precision tau1587 contact1587 logTwoBall

theorem center_sq1587 : (center1587.re : ℝ)^2 +
    (center1587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1587 : work1587.theta.ok = true ∧
    work1587.jac.invOK = true ∧ acceptsUnitSq work1587.out = true := by
  norm_num [work1587, contact1587, tau1587, center1587, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1587 : CellCertificate where
  tauBall := tau1587
  contactCenter := center1587
  contactBall := contact1587
  work := work1587
  center_sq := center_sq1587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1587.1
  jac_ok := checks1587.2.1
  accepted := checks1587.2.2

def tau1588 : RatBall :=
  ⟨⟨19/320, -117/320⟩, 3/640⟩
def center1588 : GaussianRat :=
  ⟨23835959/500000000, -265001899/1000000000⟩
def contact1588 : RatBall := localContactBall tau1588 center1588
def work1588 : RoundedTauEval :=
  evalTau precision tau1588 contact1588 logTwoBall

theorem center_sq1588 : (center1588.re : ℝ)^2 +
    (center1588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1588 : work1588.theta.ok = true ∧
    work1588.jac.invOK = true ∧ acceptsUnitSq work1588.out = true := by
  norm_num [work1588, contact1588, tau1588, center1588, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1588 : CellCertificate where
  tauBall := tau1588
  contactCenter := center1588
  contactBall := contact1588
  work := work1588
  center_sq := center_sq1588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1588.1
  jac_ok := checks1588.2.1
  accepted := checks1588.2.2

def tau1589 : RatBall :=
  ⟨⟨21/320, -119/320⟩, 3/640⟩
def center1589 : GaussianRat :=
  ⟨26476749/500000000, -33716241/125000000⟩
def contact1589 : RatBall := localContactBall tau1589 center1589
def work1589 : RoundedTauEval :=
  evalTau precision tau1589 contact1589 logTwoBall

theorem center_sq1589 : (center1589.re : ℝ)^2 +
    (center1589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1589 : work1589.theta.ok = true ∧
    work1589.jac.invOK = true ∧ acceptsUnitSq work1589.out = true := by
  norm_num [work1589, contact1589, tau1589, center1589, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1589 : CellCertificate where
  tauBall := tau1589
  contactCenter := center1589
  contactBall := contact1589
  work := work1589
  center_sq := center_sq1589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1589.1
  jac_ok := checks1589.2.1
  accepted := checks1589.2.2

def tau1590 : RatBall :=
  ⟨⟨23/320, -119/320⟩, 3/640⟩
def center1590 : GaussianRat :=
  ⟨14490933/250000000, -269422101/1000000000⟩
def contact1590 : RatBall := localContactBall tau1590 center1590
def work1590 : RoundedTauEval :=
  evalTau precision tau1590 contact1590 logTwoBall

theorem center_sq1590 : (center1590.re : ℝ)^2 +
    (center1590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1590 : work1590.theta.ok = true ∧
    work1590.jac.invOK = true ∧ acceptsUnitSq work1590.out = true := by
  norm_num [work1590, contact1590, tau1590, center1590, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1590 : CellCertificate where
  tauBall := tau1590
  contactCenter := center1590
  contactBall := contact1590
  work := work1590
  center_sq := center_sq1590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1590.1
  jac_ok := checks1590.2.1
  accepted := checks1590.2.2

def tau1591 : RatBall :=
  ⟨⟨21/320, -117/320⟩, 3/640⟩
def center1591 : GaussianRat :=
  ⟨52663303/1000000000, -52945801/200000000⟩
def contact1591 : RatBall := localContactBall tau1591 center1591
def work1591 : RoundedTauEval :=
  evalTau precision tau1591 contact1591 logTwoBall

theorem center_sq1591 : (center1591.re : ℝ)^2 +
    (center1591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1591 : work1591.theta.ok = true ∧
    work1591.jac.invOK = true ∧ acceptsUnitSq work1591.out = true := by
  norm_num [work1591, contact1591, tau1591, center1591, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1591 : CellCertificate where
  tauBall := tau1591
  contactCenter := center1591
  contactBall := contact1591
  work := work1591
  center_sq := center_sq1591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1591.1
  jac_ok := checks1591.2.1
  accepted := checks1591.2.2

def cells : List CellCertificate := [cell1584, cell1585, cell1586, cell1587, cell1588, cell1589, cell1590, cell1591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198

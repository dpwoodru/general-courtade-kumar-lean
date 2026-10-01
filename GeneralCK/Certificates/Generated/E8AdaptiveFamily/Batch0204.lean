import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1632 : RatBall :=
  ⟨⟨39/320, -117/320⟩, 3/640⟩
def center1632 : GaussianRat :=
  ⟨97144261/1000000000, -261108469/1000000000⟩
def contact1632 : RatBall := localContactBall tau1632 center1632
def work1632 : RoundedTauEval :=
  evalTau precision tau1632 contact1632 logTwoBall

theorem center_sq1632 : (center1632.re : ℝ)^2 +
    (center1632.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1632]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1632 : work1632.theta.ok = true ∧
    work1632.jac.invOK = true ∧ acceptsUnitSq work1632.out = true := by
  norm_num [work1632, contact1632, tau1632, center1632, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1632 : CellCertificate where
  tauBall := tau1632
  contactCenter := center1632
  contactBall := contact1632
  work := work1632
  center_sq := center_sq1632
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1632.1
  jac_ok := checks1632.2.1
  accepted := checks1632.2.2

def tau1633 : RatBall :=
  ⟨⟨33/320, -23/64⟩, 3/640⟩
def center1633 : GaussianRat :=
  ⟨40992501/500000000, -257627847/1000000000⟩
def contact1633 : RatBall := localContactBall tau1633 center1633
def work1633 : RoundedTauEval :=
  evalTau precision tau1633 contact1633 logTwoBall

theorem center_sq1633 : (center1633.re : ℝ)^2 +
    (center1633.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1633]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1633 : work1633.theta.ok = true ∧
    work1633.jac.invOK = true ∧ acceptsUnitSq work1633.out = true := by
  norm_num [work1633, contact1633, tau1633, center1633, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1633 : CellCertificate where
  tauBall := tau1633
  contactCenter := center1633
  contactBall := contact1633
  work := work1633
  center_sq := center_sq1633
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1633.1
  jac_ok := checks1633.2.1
  accepted := checks1633.2.2

def tau1634 : RatBall :=
  ⟨⟨7/64, -23/64⟩, 3/640⟩
def center1634 : GaussianRat :=
  ⟨43440767/500000000, -257186633/1000000000⟩
def contact1634 : RatBall := localContactBall tau1634 center1634
def work1634 : RoundedTauEval :=
  evalTau precision tau1634 contact1634 logTwoBall

theorem center_sq1634 : (center1634.re : ℝ)^2 +
    (center1634.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1634]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1634 : work1634.theta.ok = true ∧
    work1634.jac.invOK = true ∧ acceptsUnitSq work1634.out = true := by
  norm_num [work1634, contact1634, tau1634, center1634, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1634 : CellCertificate where
  tauBall := tau1634
  contactCenter := center1634
  contactBall := contact1634
  work := work1634
  center_sq := center_sq1634
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1634.1
  jac_ok := checks1634.2.1
  accepted := checks1634.2.2

def tau1635 : RatBall :=
  ⟨⟨33/320, -113/320⟩, 3/640⟩
def center1635 : GaussianRat :=
  ⟨16312353/200000000, -252737367/1000000000⟩
def contact1635 : RatBall := localContactBall tau1635 center1635
def work1635 : RoundedTauEval :=
  evalTau precision tau1635 contact1635 logTwoBall

theorem center_sq1635 : (center1635.re : ℝ)^2 +
    (center1635.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1635]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1635 : work1635.theta.ok = true ∧
    work1635.jac.invOK = true ∧ acceptsUnitSq work1635.out = true := by
  norm_num [work1635, contact1635, tau1635, center1635, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1635 : CellCertificate where
  tauBall := tau1635
  contactCenter := center1635
  contactBall := contact1635
  work := work1635
  center_sq := center_sq1635
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1635.1
  jac_ok := checks1635.2.1
  accepted := checks1635.2.2

def tau1636 : RatBall :=
  ⟨⟨7/64, -113/320⟩, 3/640⟩
def center1636 : GaussianRat :=
  ⟨86434423/1000000000, -50461627/200000000⟩
def contact1636 : RatBall := localContactBall tau1636 center1636
def work1636 : RoundedTauEval :=
  evalTau precision tau1636 contact1636 logTwoBall

theorem center_sq1636 : (center1636.re : ℝ)^2 +
    (center1636.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1636]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1636 : work1636.theta.ok = true ∧
    work1636.jac.invOK = true ∧ acceptsUnitSq work1636.out = true := by
  norm_num [work1636, contact1636, tau1636, center1636, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1636 : CellCertificate where
  tauBall := tau1636
  contactCenter := center1636
  contactBall := contact1636
  work := work1636
  center_sq := center_sq1636
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1636.1
  jac_ok := checks1636.2.1
  accepted := checks1636.2.2

def tau1637 : RatBall :=
  ⟨⟨37/320, -23/64⟩, 3/640⟩
def center1637 : GaussianRat :=
  ⟨91765617/1000000000, -12836069/50000000⟩
def contact1637 : RatBall := localContactBall tau1637 center1637
def work1637 : RoundedTauEval :=
  evalTau precision tau1637 contact1637 logTwoBall

theorem center_sq1637 : (center1637.re : ℝ)^2 +
    (center1637.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1637]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1637 : work1637.theta.ok = true ∧
    work1637.jac.invOK = true ∧ acceptsUnitSq work1637.out = true := by
  norm_num [work1637, contact1637, tau1637, center1637, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1637 : CellCertificate where
  tauBall := tau1637
  contactCenter := center1637
  contactBall := contact1637
  work := work1637
  center_sq := center_sq1637
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1637.1
  jac_ok := checks1637.2.1
  accepted := checks1637.2.2

def tau1638 : RatBall :=
  ⟨⟨39/320, -23/64⟩, 3/640⟩
def center1638 : GaussianRat :=
  ⟨773093/8000000, -128116201/500000000⟩
def contact1638 : RatBall := localContactBall tau1638 center1638
def work1638 : RoundedTauEval :=
  evalTau precision tau1638 contact1638 logTwoBall

theorem center_sq1638 : (center1638.re : ℝ)^2 +
    (center1638.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1638]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1638 : work1638.theta.ok = true ∧
    work1638.jac.invOK = true ∧ acceptsUnitSq work1638.out = true := by
  norm_num [work1638, contact1638, tau1638, center1638, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1638 : CellCertificate where
  tauBall := tau1638
  contactCenter := center1638
  contactBall := contact1638
  work := work1638
  center_sq := center_sq1638
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1638.1
  jac_ok := checks1638.2.1
  accepted := checks1638.2.2

def tau1639 : RatBall :=
  ⟨⟨37/320, -113/320⟩, 3/640⟩
def center1639 : GaussianRat :=
  ⟨45647467/500000000, -62963873/250000000⟩
def contact1639 : RatBall := localContactBall tau1639 center1639
def work1639 : RoundedTauEval :=
  evalTau precision tau1639 contact1639 logTwoBall

theorem center_sq1639 : (center1639.re : ℝ)^2 +
    (center1639.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1639]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1639 : work1639.theta.ok = true ∧
    work1639.jac.invOK = true ∧ acceptsUnitSq work1639.out = true := by
  norm_num [work1639, contact1639, tau1639, center1639, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1639 : CellCertificate where
  tauBall := tau1639
  contactCenter := center1639
  contactBall := contact1639
  work := work1639
  center_sq := center_sq1639
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1639.1
  jac_ok := checks1639.2.1
  accepted := checks1639.2.2

def cells : List CellCertificate := [cell1632, cell1633, cell1634, cell1635, cell1636, cell1637, cell1638, cell1639]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204

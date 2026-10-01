import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1712 : RatBall :=
  ⟨⟨63/320, -21/64⟩, 3/640⟩
def center1712 : GaussianRat :=
  ⟨75163641/500000000, -225566837/1000000000⟩
def contact1712 : RatBall := localContactBall tau1712 center1712
def work1712 : RoundedTauEval :=
  evalTau precision tau1712 contact1712 logTwoBall

theorem center_sq1712 : (center1712.re : ℝ)^2 +
    (center1712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1712 : work1712.theta.ok = true ∧
    work1712.jac.invOK = true ∧ acceptsUnitSq work1712.out = true := by
  norm_num [work1712, contact1712, tau1712, center1712, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1712 : CellCertificate where
  tauBall := tau1712
  contactCenter := center1712
  contactBall := contact1712
  work := work1712
  center_sq := center_sq1712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1712.1
  jac_ok := checks1712.2.1
  accepted := checks1712.2.2

def tau1713 : RatBall :=
  ⟨⟨49/320, -103/320⟩, 3/640⟩
def center1713 : GaussianRat :=
  ⟨117379261/1000000000, -56270573/250000000⟩
def contact1713 : RatBall := localContactBall tau1713 center1713
def work1713 : RoundedTauEval :=
  evalTau precision tau1713 contact1713 logTwoBall

theorem center_sq1713 : (center1713.re : ℝ)^2 +
    (center1713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1713 : work1713.theta.ok = true ∧
    work1713.jac.invOK = true ∧ acceptsUnitSq work1713.out = true := by
  norm_num [work1713, contact1713, tau1713, center1713, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1713 : CellCertificate where
  tauBall := tau1713
  contactCenter := center1713
  contactBall := contact1713
  work := work1713
  center_sq := center_sq1713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1713.1
  jac_ok := checks1713.2.1
  accepted := checks1713.2.2

def tau1714 : RatBall :=
  ⟨⟨51/320, -103/320⟩, 3/640⟩
def center1714 : GaussianRat :=
  ⟨7627513/62500000, -224552577/1000000000⟩
def contact1714 : RatBall := localContactBall tau1714 center1714
def work1714 : RoundedTauEval :=
  evalTau precision tau1714 contact1714 logTwoBall

theorem center_sq1714 : (center1714.re : ℝ)^2 +
    (center1714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1714 : work1714.theta.ok = true ∧
    work1714.jac.invOK = true ∧ acceptsUnitSq work1714.out = true := by
  norm_num [work1714, contact1714, tau1714, center1714, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1714 : CellCertificate where
  tauBall := tau1714
  contactCenter := center1714
  contactBall := contact1714
  work := work1714
  center_sq := center_sq1714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1714.1
  jac_ok := checks1714.2.1
  accepted := checks1714.2.2

def tau1715 : RatBall :=
  ⟨⟨49/320, -101/320⟩, 3/640⟩
def center1715 : GaussianRat :=
  ⟨3652061/31250000, -220423219/1000000000⟩
def contact1715 : RatBall := localContactBall tau1715 center1715
def work1715 : RoundedTauEval :=
  evalTau precision tau1715 contact1715 logTwoBall

theorem center_sq1715 : (center1715.re : ℝ)^2 +
    (center1715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1715 : work1715.theta.ok = true ∧
    work1715.jac.invOK = true ∧ acceptsUnitSq work1715.out = true := by
  norm_num [work1715, contact1715, tau1715, center1715, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1715 : CellCertificate where
  tauBall := tau1715
  contactCenter := center1715
  contactBall := contact1715
  work := work1715
  center_sq := center_sq1715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1715.1
  jac_ok := checks1715.2.1
  accepted := checks1715.2.2

def tau1716 : RatBall :=
  ⟨⟨51/320, -101/320⟩, 3/640⟩
def center1716 : GaussianRat :=
  ⟨30377187/250000000, -6872127/31250000⟩
def contact1716 : RatBall := localContactBall tau1716 center1716
def work1716 : RoundedTauEval :=
  evalTau precision tau1716 contact1716 logTwoBall

theorem center_sq1716 : (center1716.re : ℝ)^2 +
    (center1716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1716 : work1716.theta.ok = true ∧
    work1716.jac.invOK = true ∧ acceptsUnitSq work1716.out = true := by
  norm_num [work1716, contact1716, tau1716, center1716, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1716 : CellCertificate where
  tauBall := tau1716
  contactCenter := center1716
  contactBall := contact1716
  work := work1716
  center_sq := center_sq1716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1716.1
  jac_ok := checks1716.2.1
  accepted := checks1716.2.2

def tau1717 : RatBall :=
  ⟨⟨53/320, -103/320⟩, 3/640⟩
def center1717 : GaussianRat :=
  ⟨126686203/1000000000, -224004631/1000000000⟩
def contact1717 : RatBall := localContactBall tau1717 center1717
def work1717 : RoundedTauEval :=
  evalTau precision tau1717 contact1717 logTwoBall

theorem center_sq1717 : (center1717.re : ℝ)^2 +
    (center1717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1717 : work1717.theta.ok = true ∧
    work1717.jac.invOK = true ∧ acceptsUnitSq work1717.out = true := by
  norm_num [work1717, contact1717, tau1717, center1717, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1717 : CellCertificate where
  tauBall := tau1717
  contactCenter := center1717
  contactBall := contact1717
  work := work1717
  center_sq := center_sq1717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1717.1
  jac_ok := checks1717.2.1
  accepted := checks1717.2.2

def tau1718 : RatBall :=
  ⟨⟨11/64, -103/320⟩, 3/640⟩
def center1718 : GaussianRat :=
  ⟨8207299/62500000, -8937551/40000000⟩
def contact1718 : RatBall := localContactBall tau1718 center1718
def work1718 : RoundedTauEval :=
  evalTau precision tau1718 contact1718 logTwoBall

theorem center_sq1718 : (center1718.re : ℝ)^2 +
    (center1718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1718 : work1718.theta.ok = true ∧
    work1718.jac.invOK = true ∧ acceptsUnitSq work1718.out = true := by
  norm_num [work1718, contact1718, tau1718, center1718, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1718 : CellCertificate where
  tauBall := tau1718
  contactCenter := center1718
  contactBall := contact1718
  work := work1718
  center_sq := center_sq1718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1718.1
  jac_ok := checks1718.2.1
  accepted := checks1718.2.2

def tau1719 : RatBall :=
  ⟨⟨53/320, -101/320⟩, 3/640⟩
def center1719 : GaussianRat :=
  ⟨15767113/125000000, -219375147/1000000000⟩
def contact1719 : RatBall := localContactBall tau1719 center1719
def work1719 : RoundedTauEval :=
  evalTau precision tau1719 contact1719 logTwoBall

theorem center_sq1719 : (center1719.re : ℝ)^2 +
    (center1719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1719 : work1719.theta.ok = true ∧
    work1719.jac.invOK = true ∧ acceptsUnitSq work1719.out = true := by
  norm_num [work1719, contact1719, tau1719, center1719, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1719 : CellCertificate where
  tauBall := tau1719
  contactCenter := center1719
  contactBall := contact1719
  work := work1719
  center_sq := center_sq1719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1719.1
  jac_ok := checks1719.2.1
  accepted := checks1719.2.2

def cells : List CellCertificate := [cell1712, cell1713, cell1714, cell1715, cell1716, cell1717, cell1718, cell1719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214

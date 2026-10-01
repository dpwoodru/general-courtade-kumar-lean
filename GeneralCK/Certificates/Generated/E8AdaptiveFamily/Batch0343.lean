import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0343

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2744 : RatBall :=
  ⟨⟨-61/640, -241/640⟩, 3/1280⟩
def center2744 : GaussianRat :=
  ⟨-38493039/500000000, -67940497/250000000⟩
def contact2744 : RatBall := localContactBall tau2744 center2744
def work2744 : RoundedTauEval :=
  evalTau precision tau2744 contact2744 logTwoBall

theorem center_sq2744 : (center2744.re : ℝ)^2 +
    (center2744.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2744]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2744 : work2744.theta.ok = true ∧
    work2744.jac.invOK = true ∧ acceptsUnitSq work2744.out = true := by
  norm_num [work2744, contact2744, tau2744, center2744, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2744 : CellCertificate where
  tauBall := tau2744
  contactCenter := center2744
  contactBall := contact2744
  work := work2744
  center_sq := center_sq2744
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2744.1
  jac_ok := checks2744.2.1
  accepted := checks2744.2.2

def tau2745 : RatBall :=
  ⟨⟨-59/640, -243/640⟩, 3/1280⟩
def center2745 : GaussianRat :=
  ⟨-74700643/1000000000, -13723671/50000000⟩
def contact2745 : RatBall := localContactBall tau2745 center2745
def work2745 : RoundedTauEval :=
  evalTau precision tau2745 contact2745 logTwoBall

theorem center_sq2745 : (center2745.re : ℝ)^2 +
    (center2745.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2745]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2745 : work2745.theta.ok = true ∧
    work2745.jac.invOK = true ∧ acceptsUnitSq work2745.out = true := by
  norm_num [work2745, contact2745, tau2745, center2745, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2745 : CellCertificate where
  tauBall := tau2745
  contactCenter := center2745
  contactBall := contact2745
  work := work2745
  center_sq := center_sq2745
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2745.1
  jac_ok := checks2745.2.1
  accepted := checks2745.2.2

def tau2746 : RatBall :=
  ⟨⟨-57/640, -243/640⟩, 3/1280⟩
def center2746 : GaussianRat :=
  ⟨-72195957/1000000000, -1716757/6250000⟩
def contact2746 : RatBall := localContactBall tau2746 center2746
def work2746 : RoundedTauEval :=
  evalTau precision tau2746 contact2746 logTwoBall

theorem center_sq2746 : (center2746.re : ℝ)^2 +
    (center2746.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2746]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2746 : work2746.theta.ok = true ∧
    work2746.jac.invOK = true ∧ acceptsUnitSq work2746.out = true := by
  norm_num [work2746, contact2746, tau2746, center2746, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2746 : CellCertificate where
  tauBall := tau2746
  contactCenter := center2746
  contactBall := contact2746
  work := work2746
  center_sq := center_sq2746
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2746.1
  jac_ok := checks2746.2.1
  accepted := checks2746.2.2

def tau2747 : RatBall :=
  ⟨⟨-59/640, -241/640⟩, 3/1280⟩
def center2747 : GaussianRat :=
  ⟨-37245497/500000000, -8499173/31250000⟩
def contact2747 : RatBall := localContactBall tau2747 center2747
def work2747 : RoundedTauEval :=
  evalTau precision tau2747 contact2747 logTwoBall

theorem center_sq2747 : (center2747.re : ℝ)^2 +
    (center2747.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2747]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2747 : work2747.theta.ok = true ∧
    work2747.jac.invOK = true ∧ acceptsUnitSq work2747.out = true := by
  norm_num [work2747, contact2747, tau2747, center2747, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2747 : CellCertificate where
  tauBall := tau2747
  contactCenter := center2747
  contactBall := contact2747
  work := work2747
  center_sq := center_sq2747
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2747.1
  jac_ok := checks2747.2.1
  accepted := checks2747.2.2

def tau2748 : RatBall :=
  ⟨⟨-57/640, -241/640⟩, 3/1280⟩
def center2748 : GaussianRat :=
  ⟨-1439861/20000000, -68044601/250000000⟩
def contact2748 : RatBall := localContactBall tau2748 center2748
def work2748 : RoundedTauEval :=
  evalTau precision tau2748 contact2748 logTwoBall

theorem center_sq2748 : (center2748.re : ℝ)^2 +
    (center2748.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2748]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2748 : work2748.theta.ok = true ∧
    work2748.jac.invOK = true ∧ acceptsUnitSq work2748.out = true := by
  norm_num [work2748, contact2748, tau2748, center2748, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2748 : CellCertificate where
  tauBall := tau2748
  contactCenter := center2748
  contactBall := contact2748
  work := work2748
  center_sq := center_sq2748
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2748.1
  jac_ok := checks2748.2.1
  accepted := checks2748.2.2

def tau2749 : RatBall :=
  ⟨⟨-11/128, -247/640⟩, 3/1280⟩
def center2749 : GaussianRat :=
  ⟨-70088901/1000000000, -139956777/500000000⟩
def contact2749 : RatBall := localContactBall tau2749 center2749
def work2749 : RoundedTauEval :=
  evalTau precision tau2749 contact2749 logTwoBall

theorem center_sq2749 : (center2749.re : ℝ)^2 +
    (center2749.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2749]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2749 : work2749.theta.ok = true ∧
    work2749.jac.invOK = true ∧ acceptsUnitSq work2749.out = true := by
  norm_num [work2749, contact2749, tau2749, center2749, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2749 : CellCertificate where
  tauBall := tau2749
  contactCenter := center2749
  contactBall := contact2749
  work := work2749
  center_sq := center_sq2749
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2749.1
  jac_ok := checks2749.2.1
  accepted := checks2749.2.2

def tau2750 : RatBall :=
  ⟨⟨-53/640, -247/640⟩, 3/1280⟩
def center2750 : GaussianRat :=
  ⟨-33782393/500000000, -56022603/200000000⟩
def contact2750 : RatBall := localContactBall tau2750 center2750
def work2750 : RoundedTauEval :=
  evalTau precision tau2750 contact2750 logTwoBall

theorem center_sq2750 : (center2750.re : ℝ)^2 +
    (center2750.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2750]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2750 : work2750.theta.ok = true ∧
    work2750.jac.invOK = true ∧ acceptsUnitSq work2750.out = true := by
  norm_num [work2750, contact2750, tau2750, center2750, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2750 : CellCertificate where
  tauBall := tau2750
  contactCenter := center2750
  contactBall := contact2750
  work := work2750
  center_sq := center_sq2750
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2750.1
  jac_ok := checks2750.2.1
  accepted := checks2750.2.2

def tau2751 : RatBall :=
  ⟨⟨-11/128, -49/128⟩, 3/1280⟩
def center2751 : GaussianRat :=
  ⟨-69887307/1000000000, -277394317/1000000000⟩
def contact2751 : RatBall := localContactBall tau2751 center2751
def work2751 : RoundedTauEval :=
  evalTau precision tau2751 contact2751 logTwoBall

theorem center_sq2751 : (center2751.re : ℝ)^2 +
    (center2751.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2751]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2751 : work2751.theta.ok = true ∧
    work2751.jac.invOK = true ∧ acceptsUnitSq work2751.out = true := by
  norm_num [work2751, contact2751, tau2751, center2751, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2751 : CellCertificate where
  tauBall := tau2751
  contactCenter := center2751
  contactBall := contact2751
  work := work2751
  center_sq := center_sq2751
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2751.1
  jac_ok := checks2751.2.1
  accepted := checks2751.2.2

def cells : List CellCertificate := [cell2744, cell2745, cell2746, cell2747, cell2748, cell2749, cell2750, cell2751]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0343

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2536 : RatBall :=
  ⟨⟨73/320, 97/320⟩, 3/640⟩
def center2536 : GaussianRat :=
  ⟨42539121/250000000, 204268971/1000000000⟩
def contact2536 : RatBall := localContactBall tau2536 center2536
def work2536 : RoundedTauEval :=
  evalTau precision tau2536 contact2536 logTwoBall

theorem center_sq2536 : (center2536.re : ℝ)^2 +
    (center2536.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2536]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2536 : work2536.theta.ok = true ∧
    work2536.jac.invOK = true ∧ acceptsUnitSq work2536.out = true := by
  norm_num [work2536, contact2536, tau2536, center2536, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2536 : CellCertificate where
  tauBall := tau2536
  contactCenter := center2536
  contactBall := contact2536
  work := work2536
  center_sq := center_sq2536
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2536.1
  jac_ok := checks2536.2.1
  accepted := checks2536.2.2

def tau2537 : RatBall :=
  ⟨⟨15/64, 97/320⟩, 3/640⟩
def center2537 : GaussianRat :=
  ⟨87284451/500000000, 101799907/500000000⟩
def contact2537 : RatBall := localContactBall tau2537 center2537
def work2537 : RoundedTauEval :=
  evalTau precision tau2537 contact2537 logTwoBall

theorem center_sq2537 : (center2537.re : ℝ)^2 +
    (center2537.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2537]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2537 : work2537.theta.ok = true ∧
    work2537.jac.invOK = true ∧ acceptsUnitSq work2537.out = true := by
  norm_num [work2537, contact2537, tau2537, center2537, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2537 : CellCertificate where
  tauBall := tau2537
  contactCenter := center2537
  contactBall := contact2537
  work := work2537
  center_sq := center_sq2537
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2537.1
  jac_ok := checks2537.2.1
  accepted := checks2537.2.2

def tau2538 : RatBall :=
  ⟨⟨73/320, 99/320⟩, 3/640⟩
def center2538 : GaussianRat :=
  ⟨42707047/250000000, 20869737/100000000⟩
def contact2538 : RatBall := localContactBall tau2538 center2538
def work2538 : RoundedTauEval :=
  evalTau precision tau2538 contact2538 logTwoBall

theorem center_sq2538 : (center2538.re : ℝ)^2 +
    (center2538.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2538]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2538 : work2538.theta.ok = true ∧
    work2538.jac.invOK = true ∧ acceptsUnitSq work2538.out = true := by
  norm_num [work2538, contact2538, tau2538, center2538, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2538 : CellCertificate where
  tauBall := tau2538
  contactCenter := center2538
  contactBall := contact2538
  work := work2538
  center_sq := center_sq2538
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2538.1
  jac_ok := checks2538.2.1
  accepted := checks2538.2.2

def tau2539 : RatBall :=
  ⟨⟨15/64, 99/320⟩, 3/640⟩
def center2539 : GaussianRat :=
  ⟨35050807/200000000, 8320383/40000000⟩
def contact2539 : RatBall := localContactBall tau2539 center2539
def work2539 : RoundedTauEval :=
  evalTau precision tau2539 contact2539 logTwoBall

theorem center_sq2539 : (center2539.re : ℝ)^2 +
    (center2539.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2539]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2539 : work2539.theta.ok = true ∧
    work2539.jac.invOK = true ∧ acceptsUnitSq work2539.out = true := by
  norm_num [work2539, contact2539, tau2539, center2539, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2539 : CellCertificate where
  tauBall := tau2539
  contactCenter := center2539
  contactBall := contact2539
  work := work2539
  center_sq := center_sq2539
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2539.1
  jac_ok := checks2539.2.1
  accepted := checks2539.2.2

def tau2540 : RatBall :=
  ⟨⟨77/320, 97/320⟩, 3/640⟩
def center2540 : GaussianRat :=
  ⟨35792539/200000000, 40583511/200000000⟩
def contact2540 : RatBall := localContactBall tau2540 center2540
def work2540 : RoundedTauEval :=
  evalTau precision tau2540 contact2540 logTwoBall

theorem center_sq2540 : (center2540.re : ℝ)^2 +
    (center2540.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2540]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2540 : work2540.theta.ok = true ∧
    work2540.jac.invOK = true ∧ acceptsUnitSq work2540.out = true := by
  norm_num [work2540, contact2540, tau2540, center2540, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2540 : CellCertificate where
  tauBall := tau2540
  contactCenter := center2540
  contactBall := contact2540
  work := work2540
  center_sq := center_sq2540
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2540.1
  jac_ok := checks2540.2.1
  accepted := checks2540.2.2

def tau2541 : RatBall :=
  ⟨⟨79/320, 97/320⟩, 3/640⟩
def center2541 : GaussianRat :=
  ⟨183337559/1000000000, 202222527/1000000000⟩
def contact2541 : RatBall := localContactBall tau2541 center2541
def work2541 : RoundedTauEval :=
  evalTau precision tau2541 contact2541 logTwoBall

theorem center_sq2541 : (center2541.re : ℝ)^2 +
    (center2541.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2541]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2541 : work2541.theta.ok = true ∧
    work2541.jac.invOK = true ∧ acceptsUnitSq work2541.out = true := by
  norm_num [work2541, contact2541, tau2541, center2541, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2541 : CellCertificate where
  tauBall := tau2541
  contactCenter := center2541
  contactBall := contact2541
  work := work2541
  center_sq := center_sq2541
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2541.1
  jac_ok := checks2541.2.1
  accepted := checks2541.2.2

def tau2542 : RatBall :=
  ⟨⟨77/320, 99/320⟩, 3/640⟩
def center2542 : GaussianRat :=
  ⟨179660917/1000000000, 207308367/1000000000⟩
def contact2542 : RatBall := localContactBall tau2542 center2542
def work2542 : RoundedTauEval :=
  evalTau precision tau2542 contact2542 logTwoBall

theorem center_sq2542 : (center2542.re : ℝ)^2 +
    (center2542.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2542]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2542 : work2542.theta.ok = true ∧
    work2542.jac.invOK = true ∧ acceptsUnitSq work2542.out = true := by
  norm_num [work2542, contact2542, tau2542, center2542, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2542 : CellCertificate where
  tauBall := tau2542
  contactCenter := center2542
  contactBall := contact2542
  work := work2542
  center_sq := center_sq2542
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2542.1
  jac_ok := checks2542.2.1
  accepted := checks2542.2.2

def tau2543 : RatBall :=
  ⟨⟨79/320, 99/320⟩, 3/640⟩
def center2543 : GaussianRat :=
  ⟨184048527/1000000000, 206594091/1000000000⟩
def contact2543 : RatBall := localContactBall tau2543 center2543
def work2543 : RoundedTauEval :=
  evalTau precision tau2543 contact2543 logTwoBall

theorem center_sq2543 : (center2543.re : ℝ)^2 +
    (center2543.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2543]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2543 : work2543.theta.ok = true ∧
    work2543.jac.invOK = true ∧ acceptsUnitSq work2543.out = true := by
  norm_num [work2543, contact2543, tau2543, center2543, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2543 : CellCertificate where
  tauBall := tau2543
  contactCenter := center2543
  contactBall := contact2543
  work := work2543
  center_sq := center_sq2543
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2543.1
  jac_ok := checks2543.2.1
  accepted := checks2543.2.2

def cells : List CellCertificate := [cell2536, cell2537, cell2538, cell2539, cell2540, cell2541, cell2542, cell2543]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0317

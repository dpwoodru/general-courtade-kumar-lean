import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0358

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2864 : RatBall :=
  ⟨⟨-11/640, -251/640⟩, 3/1280⟩
def center2864 : GaussianRat :=
  ⟨-14171307/1000000000, -287759727/1000000000⟩
def contact2864 : RatBall := localContactBall tau2864 center2864
def work2864 : RoundedTauEval :=
  evalTau precision tau2864 contact2864 logTwoBall

theorem center_sq2864 : (center2864.re : ℝ)^2 +
    (center2864.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2864]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2864 : work2864.theta.ok = true ∧
    work2864.jac.invOK = true ∧ acceptsUnitSq work2864.out = true := by
  norm_num [work2864, contact2864, tau2864, center2864, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2864 : CellCertificate where
  tauBall := tau2864
  contactCenter := center2864
  contactBall := contact2864
  work := work2864
  center_sq := center_sq2864
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2864.1
  jac_ok := checks2864.2.1
  accepted := checks2864.2.2

def tau2865 : RatBall :=
  ⟨⟨-9/640, -251/640⟩, 3/1280⟩
def center2865 : GaussianRat :=
  ⟨-5797759/500000000, -28779857/100000000⟩
def contact2865 : RatBall := localContactBall tau2865 center2865
def work2865 : RoundedTauEval :=
  evalTau precision tau2865 contact2865 logTwoBall

theorem center_sq2865 : (center2865.re : ℝ)^2 +
    (center2865.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2865]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2865 : work2865.theta.ok = true ∧
    work2865.jac.invOK = true ∧ acceptsUnitSq work2865.out = true := by
  norm_num [work2865, contact2865, tau2865, center2865, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2865 : CellCertificate where
  tauBall := tau2865
  contactCenter := center2865
  contactBall := contact2865
  work := work2865
  center_sq := center_sq2865
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2865.1
  jac_ok := checks2865.2.1
  accepted := checks2865.2.2

def tau2866 : RatBall :=
  ⟨⟨-11/640, -249/640⟩, 3/1280⟩
def center2866 : GaussianRat :=
  ⟨-14128883/1000000000, -11407523/40000000⟩
def contact2866 : RatBall := localContactBall tau2866 center2866
def work2866 : RoundedTauEval :=
  evalTau precision tau2866 contact2866 logTwoBall

theorem center_sq2866 : (center2866.re : ℝ)^2 +
    (center2866.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2866]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2866 : work2866.theta.ok = true ∧
    work2866.jac.invOK = true ∧ acceptsUnitSq work2866.out = true := by
  norm_num [work2866, contact2866, tau2866, center2866, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2866 : CellCertificate where
  tauBall := tau2866
  contactCenter := center2866
  contactBall := contact2866
  work := work2866
  center_sq := center_sq2866
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2866.1
  jac_ok := checks2866.2.1
  accepted := checks2866.2.2

def tau2867 : RatBall :=
  ⟨⟨-9/640, -249/640⟩, 3/1280⟩
def center2867 : GaussianRat :=
  ⟨-2890199/250000000, -14261319/50000000⟩
def contact2867 : RatBall := localContactBall tau2867 center2867
def work2867 : RoundedTauEval :=
  evalTau precision tau2867 contact2867 logTwoBall

theorem center_sq2867 : (center2867.re : ℝ)^2 +
    (center2867.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2867]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2867 : work2867.theta.ok = true ∧
    work2867.jac.invOK = true ∧ acceptsUnitSq work2867.out = true := by
  norm_num [work2867, contact2867, tau2867, center2867, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2867 : CellCertificate where
  tauBall := tau2867
  contactCenter := center2867
  contactBall := contact2867
  work := work2867
  center_sq := center_sq2867
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2867.1
  jac_ok := checks2867.2.1
  accepted := checks2867.2.2

def tau2868 : RatBall :=
  ⟨⟨-7/640, -51/128⟩, 3/1280⟩
def center2868 : GaussianRat :=
  ⟨-9074409/1000000000, -292998297/1000000000⟩
def contact2868 : RatBall := localContactBall tau2868 center2868
def work2868 : RoundedTauEval :=
  evalTau precision tau2868 contact2868 logTwoBall

theorem center_sq2868 : (center2868.re : ℝ)^2 +
    (center2868.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2868]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2868 : work2868.theta.ok = true ∧
    work2868.jac.invOK = true ∧ acceptsUnitSq work2868.out = true := by
  norm_num [work2868, contact2868, tau2868, center2868, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2868 : CellCertificate where
  tauBall := tau2868
  contactCenter := center2868
  contactBall := contact2868
  work := work2868
  center_sq := center_sq2868
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2868.1
  jac_ok := checks2868.2.1
  accepted := checks2868.2.2

def tau2869 : RatBall :=
  ⟨⟨-1/128, -51/128⟩, 3/1280⟩
def center2869 : GaussianRat :=
  ⟨-6481999/1000000000, -146511137/500000000⟩
def contact2869 : RatBall := localContactBall tau2869 center2869
def work2869 : RoundedTauEval :=
  evalTau precision tau2869 contact2869 logTwoBall

theorem center_sq2869 : (center2869.re : ℝ)^2 +
    (center2869.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2869]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2869 : work2869.theta.ok = true ∧
    work2869.jac.invOK = true ∧ acceptsUnitSq work2869.out = true := by
  norm_num [work2869, contact2869, tau2869, center2869, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2869 : CellCertificate where
  tauBall := tau2869
  contactCenter := center2869
  contactBall := contact2869
  work := work2869
  center_sq := center_sq2869
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2869.1
  jac_ok := checks2869.2.1
  accepted := checks2869.2.2

def tau2870 : RatBall :=
  ⟨⟨-7/640, -253/640⟩, 3/1280⟩
def center2870 : GaussianRat :=
  ⟨-9046633/1000000000, -145205019/500000000⟩
def contact2870 : RatBall := localContactBall tau2870 center2870
def work2870 : RoundedTauEval :=
  evalTau precision tau2870 contact2870 logTwoBall

theorem center_sq2870 : (center2870.re : ℝ)^2 +
    (center2870.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2870]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2870 : work2870.theta.ok = true ∧
    work2870.jac.invOK = true ∧ acceptsUnitSq work2870.out = true := by
  norm_num [work2870, contact2870, tau2870, center2870, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2870 : CellCertificate where
  tauBall := tau2870
  contactCenter := center2870
  contactBall := contact2870
  work := work2870
  center_sq := center_sq2870
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2870.1
  jac_ok := checks2870.2.1
  accepted := checks2870.2.2

def tau2871 : RatBall :=
  ⟨⟨-1/128, -253/640⟩, 3/1280⟩
def center2871 : GaussianRat :=
  ⟨-1292431/200000000, -290433683/1000000000⟩
def contact2871 : RatBall := localContactBall tau2871 center2871
def work2871 : RoundedTauEval :=
  evalTau precision tau2871 contact2871 logTwoBall

theorem center_sq2871 : (center2871.re : ℝ)^2 +
    (center2871.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2871]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2871 : work2871.theta.ok = true ∧
    work2871.jac.invOK = true ∧ acceptsUnitSq work2871.out = true := by
  norm_num [work2871, contact2871, tau2871, center2871, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2871 : CellCertificate where
  tauBall := tau2871
  contactCenter := center2871
  contactBall := contact2871
  work := work2871
  center_sq := center_sq2871
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2871.1
  jac_ok := checks2871.2.1
  accepted := checks2871.2.2

def cells : List CellCertificate := [cell2864, cell2865, cell2866, cell2867, cell2868, cell2869, cell2870, cell2871]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0358

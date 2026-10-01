import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0864 : RatBall :=
  ⟨⟨-9/32, 37/160⟩, 3/320⟩
def center0864 : GaussianRat :=
  ⟨-199541503/1000000000, 74944839/500000000⟩
def contact0864 : RatBall := localContactBall tau0864 center0864
def work0864 : RoundedTauEval :=
  evalTau precision tau0864 contact0864 logTwoBall

theorem center_sq0864 : (center0864.re : ℝ)^2 +
    (center0864.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0864]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0864 : work0864.theta.ok = true ∧
    work0864.jac.invOK = true ∧ acceptsUnitSq work0864.out = true := by
  norm_num [work0864, contact0864, tau0864, center0864, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0864 : CellCertificate where
  tauBall := tau0864
  contactCenter := center0864
  contactBall := contact0864
  work := work0864
  center_sq := center_sq0864
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0864.1
  jac_ok := checks0864.2.1
  accepted := checks0864.2.2

def tau0865 : RatBall :=
  ⟨⟨-9/32, 39/160⟩, 3/320⟩
def center0865 : GaussianRat :=
  ⟨-200670971/1000000000, 79101837/500000000⟩
def contact0865 : RatBall := localContactBall tau0865 center0865
def work0865 : RoundedTauEval :=
  evalTau precision tau0865 contact0865 logTwoBall

theorem center_sq0865 : (center0865.re : ℝ)^2 +
    (center0865.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0865]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0865 : work0865.theta.ok = true ∧
    work0865.jac.invOK = true ∧ acceptsUnitSq work0865.out = true := by
  norm_num [work0865, contact0865, tau0865, center0865, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0865 : CellCertificate where
  tauBall := tau0865
  contactCenter := center0865
  contactBall := contact0865
  work := work0865
  center_sq := center_sq0865
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0865.1
  jac_ok := checks0865.2.1
  accepted := checks0865.2.2

def tau0866 : RatBall :=
  ⟨⟨-43/160, 37/160⟩, 3/320⟩
def center0866 : GaussianRat :=
  ⟨-191209303/1000000000, 1887097/12500000⟩
def contact0866 : RatBall := localContactBall tau0866 center0866
def work0866 : RoundedTauEval :=
  evalTau precision tau0866 contact0866 logTwoBall

theorem center_sq0866 : (center0866.re : ℝ)^2 +
    (center0866.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0866]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0866 : work0866.theta.ok = true ∧
    work0866.jac.invOK = true ∧ acceptsUnitSq work0866.out = true := by
  norm_num [work0866, contact0866, tau0866, center0866, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0866 : CellCertificate where
  tauBall := tau0866
  contactCenter := center0866
  contactBall := contact0866
  work := work0866
  center_sq := center_sq0866
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0866.1
  jac_ok := checks0866.2.1
  accepted := checks0866.2.2

def tau0867 : RatBall :=
  ⟨⟨-41/160, 37/160⟩, 3/320⟩
def center0867 : GaussianRat :=
  ⟨-182809387/1000000000, 76006029/500000000⟩
def contact0867 : RatBall := localContactBall tau0867 center0867
def work0867 : RoundedTauEval :=
  evalTau precision tau0867 contact0867 logTwoBall

theorem center_sq0867 : (center0867.re : ℝ)^2 +
    (center0867.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0867]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0867 : work0867.theta.ok = true ∧
    work0867.jac.invOK = true ∧ acceptsUnitSq work0867.out = true := by
  norm_num [work0867, contact0867, tau0867, center0867, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0867 : CellCertificate where
  tauBall := tau0867
  contactCenter := center0867
  contactBall := contact0867
  work := work0867
  center_sq := center_sq0867
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0867.1
  jac_ok := checks0867.2.1
  accepted := checks0867.2.2

def tau0868 : RatBall :=
  ⟨⟨-43/160, 39/160⟩, 3/320⟩
def center0868 : GaussianRat :=
  ⟨-96152483/500000000, 159351351/1000000000⟩
def contact0868 : RatBall := localContactBall tau0868 center0868
def work0868 : RoundedTauEval :=
  evalTau precision tau0868 contact0868 logTwoBall

theorem center_sq0868 : (center0868.re : ℝ)^2 +
    (center0868.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0868]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0868 : work0868.theta.ok = true ∧
    work0868.jac.invOK = true ∧ acceptsUnitSq work0868.out = true := by
  norm_num [work0868, contact0868, tau0868, center0868, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0868 : CellCertificate where
  tauBall := tau0868
  contactCenter := center0868
  contactBall := contact0868
  work := work0868
  center_sq := center_sq0868
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0868.1
  jac_ok := checks0868.2.1
  accepted := checks0868.2.2

def tau0869 : RatBall :=
  ⟨⟨-41/160, 39/160⟩, 3/320⟩
def center0869 : GaussianRat :=
  ⟨-91934683/500000000, 80231659/500000000⟩
def contact0869 : RatBall := localContactBall tau0869 center0869
def work0869 : RoundedTauEval :=
  evalTau precision tau0869 contact0869 logTwoBall

theorem center_sq0869 : (center0869.re : ℝ)^2 +
    (center0869.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0869]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0869 : work0869.theta.ok = true ∧
    work0869.jac.invOK = true ∧ acceptsUnitSq work0869.out = true := by
  norm_num [work0869, contact0869, tau0869, center0869, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0869 : CellCertificate where
  tauBall := tau0869
  contactCenter := center0869
  contactBall := contact0869
  work := work0869
  center_sq := center_sq0869
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0869.1
  jac_ok := checks0869.2.1
  accepted := checks0869.2.2

def tau0870 : RatBall :=
  ⟨⟨-39/160, 33/160⟩, 3/320⟩
def center0870 : GaussianRat :=
  ⟨-172488051/1000000000, 136096987/1000000000⟩
def contact0870 : RatBall := localContactBall tau0870 center0870
def work0870 : RoundedTauEval :=
  evalTau precision tau0870 contact0870 logTwoBall

theorem center_sq0870 : (center0870.re : ℝ)^2 +
    (center0870.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0870]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0870 : work0870.theta.ok = true ∧
    work0870.jac.invOK = true ∧ acceptsUnitSq work0870.out = true := by
  norm_num [work0870, contact0870, tau0870, center0870, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0870 : CellCertificate where
  tauBall := tau0870
  contactCenter := center0870
  contactBall := contact0870
  work := work0870
  center_sq := center_sq0870
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0870.1
  jac_ok := checks0870.2.1
  accepted := checks0870.2.2

def tau0871 : RatBall :=
  ⟨⟨-37/160, 33/160⟩, 3/320⟩
def center0871 : GaussianRat :=
  ⟨-164030831/1000000000, 3423667/25000000⟩
def contact0871 : RatBall := localContactBall tau0871 center0871
def work0871 : RoundedTauEval :=
  evalTau precision tau0871 contact0871 logTwoBall

theorem center_sq0871 : (center0871.re : ℝ)^2 +
    (center0871.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0871]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0871 : work0871.theta.ok = true ∧
    work0871.jac.invOK = true ∧ acceptsUnitSq work0871.out = true := by
  norm_num [work0871, contact0871, tau0871, center0871, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0871 : CellCertificate where
  tauBall := tau0871
  contactCenter := center0871
  contactBall := contact0871
  work := work0871
  center_sq := center_sq0871
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0871.1
  jac_ok := checks0871.2.1
  accepted := checks0871.2.2

def cells : List CellCertificate := [cell0864, cell0865, cell0866, cell0867, cell0868, cell0869, cell0870, cell0871]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108

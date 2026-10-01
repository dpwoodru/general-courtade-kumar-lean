import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0880 : RatBall :=
  ⟨⟨-39/160, 39/160⟩, 3/320⟩
def center0880 : GaussianRat :=
  ⟨-7014647/40000000, 32307527/200000000⟩
def contact0880 : RatBall := localContactBall tau0880 center0880
def work0880 : RoundedTauEval :=
  evalTau precision tau0880 contact0880 logTwoBall

theorem center_sq0880 : (center0880.re : ℝ)^2 +
    (center0880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0880 : work0880.theta.ok = true ∧
    work0880.jac.invOK = true ∧ acceptsUnitSq work0880.out = true := by
  norm_num [work0880, contact0880, tau0880, center0880, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0880 : CellCertificate where
  tauBall := tau0880
  contactCenter := center0880
  contactBall := contact0880
  work := work0880
  center_sq := center_sq0880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0880.1
  jac_ok := checks0880.2.1
  accepted := checks0880.2.2

def tau0881 : RatBall :=
  ⟨⟨-37/160, 39/160⟩, 3/320⟩
def center0881 : GaussianRat :=
  ⟨-83398769/500000000, 20321547/125000000⟩
def contact0881 : RatBall := localContactBall tau0881 center0881
def work0881 : RoundedTauEval :=
  evalTau precision tau0881 contact0881 logTwoBall

theorem center_sq0881 : (center0881.re : ℝ)^2 +
    (center0881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0881 : work0881.theta.ok = true ∧
    work0881.jac.invOK = true ∧ acceptsUnitSq work0881.out = true := by
  norm_num [work0881, contact0881, tau0881, center0881, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0881 : CellCertificate where
  tauBall := tau0881
  contactCenter := center0881
  contactBall := contact0881
  work := work0881
  center_sq := center_sq0881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0881.1
  jac_ok := checks0881.2.1
  accepted := checks0881.2.2

def tau0882 : RatBall :=
  ⟨⟨-7/32, 37/160⟩, 3/320⟩
def center0882 : GaussianRat :=
  ⟨-78611951/500000000, 154924327/1000000000⟩
def contact0882 : RatBall := localContactBall tau0882 center0882
def work0882 : RoundedTauEval :=
  evalTau precision tau0882 contact0882 logTwoBall

theorem center_sq0882 : (center0882.re : ℝ)^2 +
    (center0882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0882 : work0882.theta.ok = true ∧
    work0882.jac.invOK = true ∧ acceptsUnitSq work0882.out = true := by
  norm_num [work0882, contact0882, tau0882, center0882, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0882 : CellCertificate where
  tauBall := tau0882
  contactCenter := center0882
  contactBall := contact0882
  work := work0882
  center_sq := center_sq0882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0882.1
  jac_ok := checks0882.2.1
  accepted := checks0882.2.2

def tau0883 : RatBall :=
  ⟨⟨-33/160, 37/160⟩, 3/320⟩
def center0883 : GaussianRat :=
  ⟨-148574359/1000000000, 31163137/200000000⟩
def contact0883 : RatBall := localContactBall tau0883 center0883
def work0883 : RoundedTauEval :=
  evalTau precision tau0883 contact0883 logTwoBall

theorem center_sq0883 : (center0883.re : ℝ)^2 +
    (center0883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0883 : work0883.theta.ok = true ∧
    work0883.jac.invOK = true ∧ acceptsUnitSq work0883.out = true := by
  norm_num [work0883, contact0883, tau0883, center0883, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0883 : CellCertificate where
  tauBall := tau0883
  contactCenter := center0883
  contactBall := contact0883
  work := work0883
  center_sq := center_sq0883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0883.1
  jac_ok := checks0883.2.1
  accepted := checks0883.2.2

def tau0884 : RatBall :=
  ⟨⟨-7/32, 39/160⟩, 3/320⟩
def center0884 : GaussianRat :=
  ⟨-9885359/62500000, 81782823/500000000⟩
def contact0884 : RatBall := localContactBall tau0884 center0884
def work0884 : RoundedTauEval :=
  evalTau precision tau0884 contact0884 logTwoBall

theorem center_sq0884 : (center0884.re : ℝ)^2 +
    (center0884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0884 : work0884.theta.ok = true ∧
    work0884.jac.invOK = true ∧ acceptsUnitSq work0884.out = true := by
  norm_num [work0884, contact0884, tau0884, center0884, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0884 : CellCertificate where
  tauBall := tau0884
  contactCenter := center0884
  contactBall := contact0884
  work := work0884
  center_sq := center_sq0884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0884.1
  jac_ok := checks0884.2.1
  accepted := checks0884.2.2

def tau0885 : RatBall :=
  ⟨⟨-33/160, 39/160⟩, 3/320⟩
def center0885 : GaussianRat :=
  ⟨-18684153/125000000, 164515579/1000000000⟩
def contact0885 : RatBall := localContactBall tau0885 center0885
def work0885 : RoundedTauEval :=
  evalTau precision tau0885 contact0885 logTwoBall

theorem center_sq0885 : (center0885.re : ℝ)^2 +
    (center0885.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0885]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0885 : work0885.theta.ok = true ∧
    work0885.jac.invOK = true ∧ acceptsUnitSq work0885.out = true := by
  norm_num [work0885, contact0885, tau0885, center0885, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0885 : CellCertificate where
  tauBall := tau0885
  contactCenter := center0885
  contactBall := contact0885
  work := work0885
  center_sq := center_sq0885
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0885.1
  jac_ok := checks0885.2.1
  accepted := checks0885.2.2

def tau0886 : RatBall :=
  ⟨⟨-43/160, 41/160⟩, 3/320⟩
def center0886 : GaussianRat :=
  ⟨-193470247/1000000000, 167770653/1000000000⟩
def contact0886 : RatBall := localContactBall tau0886 center0886
def work0886 : RoundedTauEval :=
  evalTau precision tau0886 contact0886 logTwoBall

theorem center_sq0886 : (center0886.re : ℝ)^2 +
    (center0886.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0886]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0886 : work0886.theta.ok = true ∧
    work0886.jac.invOK = true ∧ acceptsUnitSq work0886.out = true := by
  norm_num [work0886, contact0886, tau0886, center0886, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0886 : CellCertificate where
  tauBall := tau0886
  contactCenter := center0886
  contactBall := contact0886
  work := work0886
  center_sq := center_sq0886
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0886.1
  jac_ok := checks0886.2.1
  accepted := checks0886.2.2

def tau0887 : RatBall :=
  ⟨⟨-41/160, 41/160⟩, 3/320⟩
def center0887 : GaussianRat :=
  ⟨-184996961/1000000000, 21119029/125000000⟩
def contact0887 : RatBall := localContactBall tau0887 center0887
def work0887 : RoundedTauEval :=
  evalTau precision tau0887 contact0887 logTwoBall

theorem center_sq0887 : (center0887.re : ℝ)^2 +
    (center0887.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0887]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0887 : work0887.theta.ok = true ∧
    work0887.jac.invOK = true ∧ acceptsUnitSq work0887.out = true := by
  norm_num [work0887, contact0887, tau0887, center0887, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0887 : CellCertificate where
  tauBall := tau0887
  contactCenter := center0887
  contactBall := contact0887
  work := work0887
  center_sq := center_sq0887
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0887.1
  jac_ok := checks0887.2.1
  accepted := checks0887.2.2

def cells : List CellCertificate := [cell0880, cell0881, cell0882, cell0883, cell0884, cell0885, cell0886, cell0887]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

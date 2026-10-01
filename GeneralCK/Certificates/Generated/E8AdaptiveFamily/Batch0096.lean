import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0768 : RatBall :=
  ⟨⟨61/160, -7/160⟩, 3/320⟩
def center0768 : GaussianRat :=
  ⟨252422417/1000000000, -13171007/500000000⟩
def contact0768 : RatBall := localContactBall tau0768 center0768
def work0768 : RoundedTauEval :=
  evalTau precision tau0768 contact0768 logTwoBall

theorem center_sq0768 : (center0768.re : ℝ)^2 +
    (center0768.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0768]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0768 : work0768.theta.ok = true ∧
    work0768.jac.invOK = true ∧ acceptsUnitSq work0768.out = true := by
  norm_num [work0768, contact0768, tau0768, center0768, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0768 : CellCertificate where
  tauBall := tau0768
  contactCenter := center0768
  contactBall := contact0768
  work := work0768
  center_sq := center_sq0768
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0768.1
  jac_ok := checks0768.2.1
  accepted := checks0768.2.2

def tau0769 : RatBall :=
  ⟨⟨63/160, -7/160⟩, 3/320⟩
def center0769 : GaussianRat :=
  ⟨64979987/250000000, -3263977/125000000⟩
def contact0769 : RatBall := localContactBall tau0769 center0769
def work0769 : RoundedTauEval :=
  evalTau precision tau0769 contact0769 logTwoBall

theorem center_sq0769 : (center0769.re : ℝ)^2 +
    (center0769.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0769]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0769 : work0769.theta.ok = true ∧
    work0769.jac.invOK = true ∧ acceptsUnitSq work0769.out = true := by
  norm_num [work0769, contact0769, tau0769, center0769, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0769 : CellCertificate where
  tauBall := tau0769
  contactCenter := center0769
  contactBall := contact0769
  work := work0769
  center_sq := center_sq0769
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0769.1
  jac_ok := checks0769.2.1
  accepted := checks0769.2.2

def tau0770 : RatBall :=
  ⟨⟨61/160, -1/32⟩, 3/320⟩
def center0770 : GaussianRat :=
  ⟨25222673/100000000, -18813147/1000000000⟩
def contact0770 : RatBall := localContactBall tau0770 center0770
def work0770 : RoundedTauEval :=
  evalTau precision tau0770 contact0770 logTwoBall

theorem center_sq0770 : (center0770.re : ℝ)^2 +
    (center0770.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0770]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0770 : work0770.theta.ok = true ∧
    work0770.jac.invOK = true ∧ acceptsUnitSq work0770.out = true := by
  norm_num [work0770, contact0770, tau0770, center0770, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0770 : CellCertificate where
  tauBall := tau0770
  contactCenter := center0770
  contactBall := contact0770
  work := work0770
  center_sq := center_sq0770
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0770.1
  jac_ok := checks0770.2.1
  accepted := checks0770.2.2

def tau0771 : RatBall :=
  ⟨⟨63/160, -1/32⟩, 3/320⟩
def center0771 : GaussianRat :=
  ⟨259721291/1000000000, -466223/25000000⟩
def contact0771 : RatBall := localContactBall tau0771 center0771
def work0771 : RoundedTauEval :=
  evalTau precision tau0771 contact0771 logTwoBall

theorem center_sq0771 : (center0771.re : ℝ)^2 +
    (center0771.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0771]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0771 : work0771.theta.ok = true ∧
    work0771.jac.invOK = true ∧ acceptsUnitSq work0771.out = true := by
  norm_num [work0771, contact0771, tau0771, center0771, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0771 : CellCertificate where
  tauBall := tau0771
  contactCenter := center0771
  contactBall := contact0771
  work := work0771
  center_sq := center_sq0771
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0771.1
  jac_ok := checks0771.2.1
  accepted := checks0771.2.2

def tau0772 : RatBall :=
  ⟨⟨-63/160, 1/32⟩, 3/320⟩
def center0772 : GaussianRat :=
  ⟨-259721291/1000000000, 466223/25000000⟩
def contact0772 : RatBall := localContactBall tau0772 center0772
def work0772 : RoundedTauEval :=
  evalTau precision tau0772 contact0772 logTwoBall

theorem center_sq0772 : (center0772.re : ℝ)^2 +
    (center0772.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0772]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0772 : work0772.theta.ok = true ∧
    work0772.jac.invOK = true ∧ acceptsUnitSq work0772.out = true := by
  norm_num [work0772, contact0772, tau0772, center0772, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0772 : CellCertificate where
  tauBall := tau0772
  contactCenter := center0772
  contactBall := contact0772
  work := work0772
  center_sq := center_sq0772
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0772.1
  jac_ok := checks0772.2.1
  accepted := checks0772.2.2

def tau0773 : RatBall :=
  ⟨⟨-61/160, 1/32⟩, 3/320⟩
def center0773 : GaussianRat :=
  ⟨-25222673/100000000, 18813147/1000000000⟩
def contact0773 : RatBall := localContactBall tau0773 center0773
def work0773 : RoundedTauEval :=
  evalTau precision tau0773 contact0773 logTwoBall

theorem center_sq0773 : (center0773.re : ℝ)^2 +
    (center0773.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0773 : work0773.theta.ok = true ∧
    work0773.jac.invOK = true ∧ acceptsUnitSq work0773.out = true := by
  norm_num [work0773, contact0773, tau0773, center0773, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0773 : CellCertificate where
  tauBall := tau0773
  contactCenter := center0773
  contactBall := contact0773
  work := work0773
  center_sq := center_sq0773
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0773.1
  jac_ok := checks0773.2.1
  accepted := checks0773.2.2

def tau0774 : RatBall :=
  ⟨⟨-63/160, 7/160⟩, 3/320⟩
def center0774 : GaussianRat :=
  ⟨-64979987/250000000, 3263977/125000000⟩
def contact0774 : RatBall := localContactBall tau0774 center0774
def work0774 : RoundedTauEval :=
  evalTau precision tau0774 contact0774 logTwoBall

theorem center_sq0774 : (center0774.re : ℝ)^2 +
    (center0774.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0774]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0774 : work0774.theta.ok = true ∧
    work0774.jac.invOK = true ∧ acceptsUnitSq work0774.out = true := by
  norm_num [work0774, contact0774, tau0774, center0774, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0774 : CellCertificate where
  tauBall := tau0774
  contactCenter := center0774
  contactBall := contact0774
  work := work0774
  center_sq := center_sq0774
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0774.1
  jac_ok := checks0774.2.1
  accepted := checks0774.2.2

def tau0775 : RatBall :=
  ⟨⟨-61/160, 7/160⟩, 3/320⟩
def center0775 : GaussianRat :=
  ⟨-252422417/1000000000, 13171007/500000000⟩
def contact0775 : RatBall := localContactBall tau0775 center0775
def work0775 : RoundedTauEval :=
  evalTau precision tau0775 contact0775 logTwoBall

theorem center_sq0775 : (center0775.re : ℝ)^2 +
    (center0775.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0775]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0775 : work0775.theta.ok = true ∧
    work0775.jac.invOK = true ∧ acceptsUnitSq work0775.out = true := by
  norm_num [work0775, contact0775, tau0775, center0775, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0775 : CellCertificate where
  tauBall := tau0775
  contactCenter := center0775
  contactBall := contact0775
  work := work0775
  center_sq := center_sq0775
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0775.1
  jac_ok := checks0775.2.1
  accepted := checks0775.2.2

def cells : List CellCertificate := [cell0768, cell0769, cell0770, cell0771, cell0772, cell0773, cell0774, cell0775]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

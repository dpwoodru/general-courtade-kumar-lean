import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0728 : RatBall :=
  ⟨⟨57/160, -27/160⟩, 3/320⟩
def center0728 : GaussianRat :=
  ⟨242691133/1000000000, -103792249/1000000000⟩
def contact0728 : RatBall := localContactBall tau0728 center0728
def work0728 : RoundedTauEval :=
  evalTau precision tau0728 contact0728 logTwoBall

theorem center_sq0728 : (center0728.re : ℝ)^2 +
    (center0728.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0728]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0728 : work0728.theta.ok = true ∧
    work0728.jac.invOK = true ∧ acceptsUnitSq work0728.out = true := by
  norm_num [work0728, contact0728, tau0728, center0728, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0728 : CellCertificate where
  tauBall := tau0728
  contactCenter := center0728
  contactBall := contact0728
  work := work0728
  center_sq := center_sq0728
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0728.1
  jac_ok := checks0728.2.1
  accepted := checks0728.2.2

def tau0729 : RatBall :=
  ⟨⟨59/160, -27/160⟩, 3/320⟩
def center0729 : GaussianRat :=
  ⟨6260393/25000000, -51450627/500000000⟩
def contact0729 : RatBall := localContactBall tau0729 center0729
def work0729 : RoundedTauEval :=
  evalTau precision tau0729 contact0729 logTwoBall

theorem center_sq0729 : (center0729.re : ℝ)^2 +
    (center0729.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0729]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0729 : work0729.theta.ok = true ∧
    work0729.jac.invOK = true ∧ acceptsUnitSq work0729.out = true := by
  norm_num [work0729, contact0729, tau0729, center0729, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0729 : CellCertificate where
  tauBall := tau0729
  contactCenter := center0729
  contactBall := contact0729
  work := work0729
  center_sq := center_sq0729
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0729.1
  jac_ok := checks0729.2.1
  accepted := checks0729.2.2

def tau0730 : RatBall :=
  ⟨⟨57/160, -5/32⟩, 3/320⟩
def center0730 : GaussianRat :=
  ⟨7557593/31250000, -96039881/1000000000⟩
def contact0730 : RatBall := localContactBall tau0730 center0730
def work0730 : RoundedTauEval :=
  evalTau precision tau0730 contact0730 logTwoBall

theorem center_sq0730 : (center0730.re : ℝ)^2 +
    (center0730.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0730]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0730 : work0730.theta.ok = true ∧
    work0730.jac.invOK = true ∧ acceptsUnitSq work0730.out = true := by
  norm_num [work0730, contact0730, tau0730, center0730, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0730 : CellCertificate where
  tauBall := tau0730
  contactCenter := center0730
  contactBall := contact0730
  work := work0730
  center_sq := center_sq0730
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0730.1
  jac_ok := checks0730.2.1
  accepted := checks0730.2.2

def tau0731 : RatBall :=
  ⟨⟨59/160, -5/32⟩, 3/320⟩
def center0731 : GaussianRat :=
  ⟨1996423/8000000, -19043899/200000000⟩
def contact0731 : RatBall := localContactBall tau0731 center0731
def work0731 : RoundedTauEval :=
  evalTau precision tau0731 contact0731 logTwoBall

theorem center_sq0731 : (center0731.re : ℝ)^2 +
    (center0731.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0731]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0731 : work0731.theta.ok = true ∧
    work0731.jac.invOK = true ∧ acceptsUnitSq work0731.out = true := by
  norm_num [work0731, contact0731, tau0731, center0731, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0731 : CellCertificate where
  tauBall := tau0731
  contactCenter := center0731
  contactBall := contact0731
  work := work0731
  center_sq := center_sq0731
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0731.1
  jac_ok := checks0731.2.1
  accepted := checks0731.2.2

def tau0732 : RatBall :=
  ⟨⟨49/160, -23/160⟩, 3/320⟩
def center0732 : GaussianRat :=
  ⟨209607093/1000000000, -22790011/250000000⟩
def contact0732 : RatBall := localContactBall tau0732 center0732
def work0732 : RoundedTauEval :=
  evalTau precision tau0732 contact0732 logTwoBall

theorem center_sq0732 : (center0732.re : ℝ)^2 +
    (center0732.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0732]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0732 : work0732.theta.ok = true ∧
    work0732.jac.invOK = true ∧ acceptsUnitSq work0732.out = true := by
  norm_num [work0732, contact0732, tau0732, center0732, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0732 : CellCertificate where
  tauBall := tau0732
  contactCenter := center0732
  contactBall := contact0732
  work := work0732
  center_sq := center_sq0732
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0732.1
  jac_ok := checks0732.2.1
  accepted := checks0732.2.2

def tau0733 : RatBall :=
  ⟨⟨51/160, -23/160⟩, 3/320⟩
def center0733 : GaussianRat :=
  ⟨6799051/31250000, -90469443/1000000000⟩
def contact0733 : RatBall := localContactBall tau0733 center0733
def work0733 : RoundedTauEval :=
  evalTau precision tau0733 contact0733 logTwoBall

theorem center_sq0733 : (center0733.re : ℝ)^2 +
    (center0733.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0733]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0733 : work0733.theta.ok = true ∧
    work0733.jac.invOK = true ∧ acceptsUnitSq work0733.out = true := by
  norm_num [work0733, contact0733, tau0733, center0733, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0733 : CellCertificate where
  tauBall := tau0733
  contactCenter := center0733
  contactBall := contact0733
  work := work0733
  center_sq := center_sq0733
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0733.1
  jac_ok := checks0733.2.1
  accepted := checks0733.2.2

def tau0734 : RatBall :=
  ⟨⟨49/160, -21/160⟩, 3/320⟩
def center0734 : GaussianRat :=
  ⟨41791301/200000000, -41587123/500000000⟩
def contact0734 : RatBall := localContactBall tau0734 center0734
def work0734 : RoundedTauEval :=
  evalTau precision tau0734 contact0734 logTwoBall

theorem center_sq0734 : (center0734.re : ℝ)^2 +
    (center0734.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0734]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0734 : work0734.theta.ok = true ∧
    work0734.jac.invOK = true ∧ acceptsUnitSq work0734.out = true := by
  norm_num [work0734, contact0734, tau0734, center0734, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0734 : CellCertificate where
  tauBall := tau0734
  contactCenter := center0734
  contactBall := contact0734
  work := work0734
  center_sq := center_sq0734
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0734.1
  jac_ok := checks0734.2.1
  accepted := checks0734.2.2

def tau0735 : RatBall :=
  ⟨⟨51/160, -21/160⟩, 3/320⟩
def center0735 : GaussianRat :=
  ⟨216902699/1000000000, -20636751/250000000⟩
def contact0735 : RatBall := localContactBall tau0735 center0735
def work0735 : RoundedTauEval :=
  evalTau precision tau0735 contact0735 logTwoBall

theorem center_sq0735 : (center0735.re : ℝ)^2 +
    (center0735.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0735]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0735 : work0735.theta.ok = true ∧
    work0735.jac.invOK = true ∧ acceptsUnitSq work0735.out = true := by
  norm_num [work0735, contact0735, tau0735, center0735, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0735 : CellCertificate where
  tauBall := tau0735
  contactCenter := center0735
  contactBall := contact0735
  work := work0735
  center_sq := center_sq0735
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0735.1
  jac_ok := checks0735.2.1
  accepted := checks0735.2.2

def cells : List CellCertificate := [cell0728, cell0729, cell0730, cell0731, cell0732, cell0733, cell0734, cell0735]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091

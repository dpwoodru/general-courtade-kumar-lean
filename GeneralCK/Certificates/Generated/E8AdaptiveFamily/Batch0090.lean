import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0720 : RatBall :=
  ⟨⟨51/160, -27/160⟩, 3/320⟩
def center0720 : GaussianRat :=
  ⟨219098349/1000000000, -53182749/500000000⟩
def contact0720 : RatBall := localContactBall tau0720 center0720
def work0720 : RoundedTauEval :=
  evalTau precision tau0720 contact0720 logTwoBall

theorem center_sq0720 : (center0720.re : ℝ)^2 +
    (center0720.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0720]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0720 : work0720.theta.ok = true ∧
    work0720.jac.invOK = true ∧ acceptsUnitSq work0720.out = true := by
  norm_num [work0720, contact0720, tau0720, center0720, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0720 : CellCertificate where
  tauBall := tau0720
  contactCenter := center0720
  contactBall := contact0720
  work := work0720
  center_sq := center_sq0720
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0720.1
  jac_ok := checks0720.2.1
  accepted := checks0720.2.2

def tau0721 : RatBall :=
  ⟨⟨49/160, -5/32⟩, 3/320⟩
def center0721 : GaussianRat :=
  ⟨52580197/250000000, -1239543/12500000⟩
def contact0721 : RatBall := localContactBall tau0721 center0721
def work0721 : RoundedTauEval :=
  evalTau precision tau0721 contact0721 logTwoBall

theorem center_sq0721 : (center0721.re : ℝ)^2 +
    (center0721.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0721]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0721 : work0721.theta.ok = true ∧
    work0721.jac.invOK = true ∧ acceptsUnitSq work0721.out = true := by
  norm_num [work0721, contact0721, tau0721, center0721, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0721 : CellCertificate where
  tauBall := tau0721
  contactCenter := center0721
  contactBall := contact0721
  work := work0721
  center_sq := center_sq0721
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0721.1
  jac_ok := checks0721.2.1
  accepted := checks0721.2.2

def tau0722 : RatBall :=
  ⟨⟨51/160, -5/32⟩, 3/320⟩
def center0722 : GaussianRat :=
  ⟨5457529/25000000, -49204231/500000000⟩
def contact0722 : RatBall := localContactBall tau0722 center0722
def work0722 : RoundedTauEval :=
  evalTau precision tau0722 contact0722 logTwoBall

theorem center_sq0722 : (center0722.re : ℝ)^2 +
    (center0722.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0722]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0722 : work0722.theta.ok = true ∧
    work0722.jac.invOK = true ∧ acceptsUnitSq work0722.out = true := by
  norm_num [work0722, contact0722, tau0722, center0722, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0722 : CellCertificate where
  tauBall := tau0722
  contactCenter := center0722
  contactBall := contact0722
  work := work0722
  center_sq := center_sq0722
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0722.1
  jac_ok := checks0722.2.1
  accepted := checks0722.2.2

def tau0723 : RatBall :=
  ⟨⟨53/160, -27/160⟩, 3/320⟩
def center0723 : GaussianRat :=
  ⟨113515613/500000000, -13190697/125000000⟩
def contact0723 : RatBall := localContactBall tau0723 center0723
def work0723 : RoundedTauEval :=
  evalTau precision tau0723 contact0723 logTwoBall

theorem center_sq0723 : (center0723.re : ℝ)^2 +
    (center0723.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0723]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0723 : work0723.theta.ok = true ∧
    work0723.jac.invOK = true ∧ acceptsUnitSq work0723.out = true := by
  norm_num [work0723, contact0723, tau0723, center0723, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0723 : CellCertificate where
  tauBall := tau0723
  contactCenter := center0723
  contactBall := contact0723
  work := work0723
  center_sq := center_sq0723
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0723.1
  jac_ok := checks0723.2.1
  accepted := checks0723.2.2

def tau0724 : RatBall :=
  ⟨⟨11/32, -27/160⟩, 3/320⟩
def center0724 : GaussianRat :=
  ⟨234895911/1000000000, -52333711/500000000⟩
def contact0724 : RatBall := localContactBall tau0724 center0724
def work0724 : RoundedTauEval :=
  evalTau precision tau0724 contact0724 logTwoBall

theorem center_sq0724 : (center0724.re : ℝ)^2 +
    (center0724.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0724]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0724 : work0724.theta.ok = true ∧
    work0724.jac.invOK = true ∧ acceptsUnitSq work0724.out = true := by
  norm_num [work0724, contact0724, tau0724, center0724, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0724 : CellCertificate where
  tauBall := tau0724
  contactCenter := center0724
  contactBall := contact0724
  work := work0724
  center_sq := center_sq0724
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0724.1
  jac_ok := checks0724.2.1
  accepted := checks0724.2.2

def tau0725 : RatBall :=
  ⟨⟨53/160, -5/32⟩, 3/320⟩
def center0725 : GaussianRat :=
  ⟨226215887/1000000000, -24408867/250000000⟩
def contact0725 : RatBall := localContactBall tau0725 center0725
def work0725 : RoundedTauEval :=
  evalTau precision tau0725 contact0725 logTwoBall

theorem center_sq0725 : (center0725.re : ℝ)^2 +
    (center0725.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0725]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0725 : work0725.theta.ok = true ∧
    work0725.jac.invOK = true ∧ acceptsUnitSq work0725.out = true := by
  norm_num [work0725, contact0725, tau0725, center0725, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0725 : CellCertificate where
  tauBall := tau0725
  contactCenter := center0725
  contactBall := contact0725
  work := work0725
  center_sq := center_sq0725
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0725.1
  jac_ok := checks0725.2.1
  accepted := checks0725.2.2

def tau0726 : RatBall :=
  ⟨⟨11/32, -5/32⟩, 3/320⟩
def center0726 : GaussianRat :=
  ⟨234063587/1000000000, -96845571/1000000000⟩
def contact0726 : RatBall := localContactBall tau0726 center0726
def work0726 : RoundedTauEval :=
  evalTau precision tau0726 contact0726 logTwoBall

theorem center_sq0726 : (center0726.re : ℝ)^2 +
    (center0726.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0726]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0726 : work0726.theta.ok = true ∧
    work0726.jac.invOK = true ∧ acceptsUnitSq work0726.out = true := by
  norm_num [work0726, contact0726, tau0726, center0726, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0726 : CellCertificate where
  tauBall := tau0726
  contactCenter := center0726
  contactBall := contact0726
  work := work0726
  center_sq := center_sq0726
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0726.1
  jac_ok := checks0726.2.1
  accepted := checks0726.2.2

def tau0727 : RatBall :=
  ⟨⟨57/160, -29/160⟩, 3/320⟩
def center0727 : GaussianRat :=
  ⟨243609941/1000000000, -22312087/200000000⟩
def contact0727 : RatBall := localContactBall tau0727 center0727
def work0727 : RoundedTauEval :=
  evalTau precision tau0727 contact0727 logTwoBall

theorem center_sq0727 : (center0727.re : ℝ)^2 +
    (center0727.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0727]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0727 : work0727.theta.ok = true ∧
    work0727.jac.invOK = true ∧ acceptsUnitSq work0727.out = true := by
  norm_num [work0727, contact0727, tau0727, center0727, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0727 : CellCertificate where
  tauBall := tau0727
  contactCenter := center0727
  contactBall := contact0727
  work := work0727
  center_sq := center_sq0727
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0727.1
  jac_ok := checks0727.2.1
  accepted := checks0727.2.2

def cells : List CellCertificate := [cell0720, cell0721, cell0722, cell0723, cell0724, cell0725, cell0726, cell0727]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0784 : RatBall :=
  ⟨⟨-59/160, 13/160⟩, 3/320⟩
def center0784 : GaussianRat :=
  ⟨-245825343/1000000000, 12344447/250000000⟩
def contact0784 : RatBall := localContactBall tau0784 center0784
def work0784 : RoundedTauEval :=
  evalTau precision tau0784 contact0784 logTwoBall

theorem center_sq0784 : (center0784.re : ℝ)^2 +
    (center0784.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0784]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0784 : work0784.theta.ok = true ∧
    work0784.jac.invOK = true ∧ acceptsUnitSq work0784.out = true := by
  norm_num [work0784, contact0784, tau0784, center0784, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0784 : CellCertificate where
  tauBall := tau0784
  contactCenter := center0784
  contactBall := contact0784
  work := work0784
  center_sq := center_sq0784
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0784.1
  jac_ok := checks0784.2.1
  accepted := checks0784.2.2

def tau0785 : RatBall :=
  ⟨⟨-57/160, 13/160⟩, 3/320⟩
def center0785 : GaussianRat :=
  ⟨-238180443/1000000000, 24897027/500000000⟩
def contact0785 : RatBall := localContactBall tau0785 center0785
def work0785 : RoundedTauEval :=
  evalTau precision tau0785 contact0785 logTwoBall

theorem center_sq0785 : (center0785.re : ℝ)^2 +
    (center0785.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0785]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0785 : work0785.theta.ok = true ∧
    work0785.jac.invOK = true ∧ acceptsUnitSq work0785.out = true := by
  norm_num [work0785, contact0785, tau0785, center0785, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0785 : CellCertificate where
  tauBall := tau0785
  contactCenter := center0785
  contactBall := contact0785
  work := work0785
  center_sq := center_sq0785
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0785.1
  jac_ok := checks0785.2.1
  accepted := checks0785.2.2

def tau0786 : RatBall :=
  ⟨⟨-59/160, 3/32⟩, 3/320⟩
def center0786 : GaussianRat :=
  ⟨-246278271/1000000000, 56993771/1000000000⟩
def contact0786 : RatBall := localContactBall tau0786 center0786
def work0786 : RoundedTauEval :=
  evalTau precision tau0786 contact0786 logTwoBall

theorem center_sq0786 : (center0786.re : ℝ)^2 +
    (center0786.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0786]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0786 : work0786.theta.ok = true ∧
    work0786.jac.invOK = true ∧ acceptsUnitSq work0786.out = true := by
  norm_num [work0786, contact0786, tau0786, center0786, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0786 : CellCertificate where
  tauBall := tau0786
  contactCenter := center0786
  contactBall := contact0786
  work := work0786
  center_sq := center_sq0786
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0786.1
  jac_ok := checks0786.2.1
  accepted := checks0786.2.2

def tau0787 : RatBall :=
  ⟨⟨-57/160, 3/32⟩, 3/320⟩
def center0787 : GaussianRat :=
  ⟨-11931267/50000000, 14368881/250000000⟩
def contact0787 : RatBall := localContactBall tau0787 center0787
def work0787 : RoundedTauEval :=
  evalTau precision tau0787 contact0787 logTwoBall

theorem center_sq0787 : (center0787.re : ℝ)^2 +
    (center0787.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0787]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0787 : work0787.theta.ok = true ∧
    work0787.jac.invOK = true ∧ acceptsUnitSq work0787.out = true := by
  norm_num [work0787, contact0787, tau0787, center0787, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0787 : CellCertificate where
  tauBall := tau0787
  contactCenter := center0787
  contactBall := contact0787
  work := work0787
  center_sq := center_sq0787
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0787.1
  jac_ok := checks0787.2.1
  accepted := checks0787.2.2

def tau0788 : RatBall :=
  ⟨⟨-61/160, 17/160⟩, 3/320⟩
def center0788 : GaussianRat :=
  ⟨-254392641/1000000000, 20019/312500⟩
def contact0788 : RatBall := localContactBall tau0788 center0788
def work0788 : RoundedTauEval :=
  evalTau precision tau0788 contact0788 logTwoBall

theorem center_sq0788 : (center0788.re : ℝ)^2 +
    (center0788.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0788]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0788 : work0788.theta.ok = true ∧
    work0788.jac.invOK = true ∧ acceptsUnitSq work0788.out = true := by
  norm_num [work0788, contact0788, tau0788, center0788, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0788 : CellCertificate where
  tauBall := tau0788
  contactCenter := center0788
  contactBall := contact0788
  work := work0788
  center_sq := center_sq0788
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0788.1
  jac_ok := checks0788.2.1
  accepted := checks0788.2.2

def tau0789 : RatBall :=
  ⟨⟨-61/160, 19/160⟩, 3/320⟩
def center0789 : GaussianRat :=
  ⟨-31873559/125000000, 7162653/100000000⟩
def contact0789 : RatBall := localContactBall tau0789 center0789
def work0789 : RoundedTauEval :=
  evalTau precision tau0789 contact0789 logTwoBall

theorem center_sq0789 : (center0789.re : ℝ)^2 +
    (center0789.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0789]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0789 : work0789.theta.ok = true ∧
    work0789.jac.invOK = true ∧ acceptsUnitSq work0789.out = true := by
  norm_num [work0789, contact0789, tau0789, center0789, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0789 : CellCertificate where
  tauBall := tau0789
  contactCenter := center0789
  contactBall := contact0789
  work := work0789
  center_sq := center_sq0789
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0789.1
  jac_ok := checks0789.2.1
  accepted := checks0789.2.2

def tau0790 : RatBall :=
  ⟨⟨-59/160, 17/160⟩, 3/320⟩
def center0790 : GaussianRat :=
  ⟨-15424847/62500000, 32309019/500000000⟩
def contact0790 : RatBall := localContactBall tau0790 center0790
def work0790 : RoundedTauEval :=
  evalTau precision tau0790 contact0790 logTwoBall

theorem center_sq0790 : (center0790.re : ℝ)^2 +
    (center0790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0790 : work0790.theta.ok = true ∧
    work0790.jac.invOK = true ∧ acceptsUnitSq work0790.out = true := by
  norm_num [work0790, contact0790, tau0790, center0790, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0790 : CellCertificate where
  tauBall := tau0790
  contactCenter := center0790
  contactBall := contact0790
  work := work0790
  center_sq := center_sq0790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0790.1
  jac_ok := checks0790.2.1
  accepted := checks0790.2.2

def tau0791 : RatBall :=
  ⟨⟨-57/160, 17/160⟩, 3/320⟩
def center0791 : GaussianRat :=
  ⟨-119567729/500000000, 32582953/500000000⟩
def contact0791 : RatBall := localContactBall tau0791 center0791
def work0791 : RoundedTauEval :=
  evalTau precision tau0791 contact0791 logTwoBall

theorem center_sq0791 : (center0791.re : ℝ)^2 +
    (center0791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0791 : work0791.theta.ok = true ∧
    work0791.jac.invOK = true ∧ acceptsUnitSq work0791.out = true := by
  norm_num [work0791, contact0791, tau0791, center0791, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0791 : CellCertificate where
  tauBall := tau0791
  contactCenter := center0791
  contactBall := contact0791
  work := work0791
  center_sq := center_sq0791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0791.1
  jac_ok := checks0791.2.1
  accepted := checks0791.2.2

def cells : List CellCertificate := [cell0784, cell0785, cell0786, cell0787, cell0788, cell0789, cell0790, cell0791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098

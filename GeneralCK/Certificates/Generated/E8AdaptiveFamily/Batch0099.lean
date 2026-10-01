import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0792 : RatBall :=
  ⟨⟨-59/160, 19/160⟩, 3/320⟩
def center0792 : GaussianRat :=
  ⟨-247383851/1000000000, 72251673/1000000000⟩
def contact0792 : RatBall := localContactBall tau0792 center0792
def work0792 : RoundedTauEval :=
  evalTau precision tau0792 contact0792 logTwoBall

theorem center_sq0792 : (center0792.re : ℝ)^2 +
    (center0792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0792 : work0792.theta.ok = true ∧
    work0792.jac.invOK = true ∧ acceptsUnitSq work0792.out = true := by
  norm_num [work0792, contact0792, tau0792, center0792, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0792 : CellCertificate where
  tauBall := tau0792
  contactCenter := center0792
  contactBall := contact0792
  work := work0792
  center_sq := center_sq0792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0792.1
  jac_ok := checks0792.2.1
  accepted := checks0792.2.2

def tau0793 : RatBall :=
  ⟨⟨-57/160, 19/160⟩, 3/320⟩
def center0793 : GaussianRat :=
  ⟨-239711471/1000000000, 72866371/1000000000⟩
def contact0793 : RatBall := localContactBall tau0793 center0793
def work0793 : RoundedTauEval :=
  evalTau precision tau0793 contact0793 logTwoBall

theorem center_sq0793 : (center0793.re : ℝ)^2 +
    (center0793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0793 : work0793.theta.ok = true ∧
    work0793.jac.invOK = true ∧ acceptsUnitSq work0793.out = true := by
  norm_num [work0793, contact0793, tau0793, center0793, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0793 : CellCertificate where
  tauBall := tau0793
  contactCenter := center0793
  contactBall := contact0793
  work := work0793
  center_sq := center_sq0793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0793.1
  jac_ok := checks0793.2.1
  accepted := checks0793.2.2

def tau0794 : RatBall :=
  ⟨⟨-61/160, 21/160⟩, 3/320⟩
def center0794 : GaussianRat :=
  ⟨-15978319/62500000, 79201909/1000000000⟩
def contact0794 : RatBall := localContactBall tau0794 center0794
def work0794 : RoundedTauEval :=
  evalTau precision tau0794 contact0794 logTwoBall

theorem center_sq0794 : (center0794.re : ℝ)^2 +
    (center0794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0794 : work0794.theta.ok = true ∧
    work0794.jac.invOK = true ∧ acceptsUnitSq work0794.out = true := by
  norm_num [work0794, contact0794, tau0794, center0794, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0794 : CellCertificate where
  tauBall := tau0794
  contactCenter := center0794
  contactBall := contact0794
  work := work0794
  center_sq := center_sq0794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0794.1
  jac_ok := checks0794.2.1
  accepted := checks0794.2.2

def tau0795 : RatBall :=
  ⟨⟨-61/160, 23/160⟩, 3/320⟩
def center0795 : GaussianRat :=
  ⟨-64096843/250000000, 86787913/1000000000⟩
def contact0795 : RatBall := localContactBall tau0795 center0795
def work0795 : RoundedTauEval :=
  evalTau precision tau0795 contact0795 logTwoBall

theorem center_sq0795 : (center0795.re : ℝ)^2 +
    (center0795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0795 : work0795.theta.ok = true ∧
    work0795.jac.invOK = true ∧ acceptsUnitSq work0795.out = true := by
  norm_num [work0795, contact0795, tau0795, center0795, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0795 : CellCertificate where
  tauBall := tau0795
  contactCenter := center0795
  contactBall := contact0795
  work := work0795
  center_sq := center_sq0795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0795.1
  jac_ok := checks0795.2.1
  accepted := checks0795.2.2

def tau0796 : RatBall :=
  ⟨⟨-59/160, 21/160⟩, 3/320⟩
def center0796 : GaussianRat :=
  ⟨-124018963/500000000, 79895753/1000000000⟩
def contact0796 : RatBall := localContactBall tau0796 center0796
def work0796 : RoundedTauEval :=
  evalTau precision tau0796 contact0796 logTwoBall

theorem center_sq0796 : (center0796.re : ℝ)^2 +
    (center0796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0796 : work0796.theta.ok = true ∧
    work0796.jac.invOK = true ∧ acceptsUnitSq work0796.out = true := by
  norm_num [work0796, contact0796, tau0796, center0796, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0796 : CellCertificate where
  tauBall := tau0796
  contactCenter := center0796
  contactBall := contact0796
  work := work0796
  center_sq := center_sq0796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0796.1
  jac_ok := checks0796.2.1
  accepted := checks0796.2.2

def tau0797 : RatBall :=
  ⟨⟨-57/160, 21/160⟩, 3/320⟩
def center0797 : GaussianRat :=
  ⟨-120177071/500000000, 16115617/200000000⟩
def contact0797 : RatBall := localContactBall tau0797 center0797
def work0797 : RoundedTauEval :=
  evalTau precision tau0797 contact0797 logTwoBall

theorem center_sq0797 : (center0797.re : ℝ)^2 +
    (center0797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0797 : work0797.theta.ok = true ∧
    work0797.jac.invOK = true ∧ acceptsUnitSq work0797.out = true := by
  norm_num [work0797, contact0797, tau0797, center0797, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0797 : CellCertificate where
  tauBall := tau0797
  contactCenter := center0797
  contactBall := contact0797
  work := work0797
  center_sq := center_sq0797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0797.1
  jac_ok := checks0797.2.1
  accepted := checks0797.2.2

def tau0798 : RatBall :=
  ⟨⟨-59/160, 23/160⟩, 3/320⟩
def center0798 : GaussianRat :=
  ⟨-248760621/1000000000, 43775671/500000000⟩
def contact0798 : RatBall := localContactBall tau0798 center0798
def work0798 : RoundedTauEval :=
  evalTau precision tau0798 contact0798 logTwoBall

theorem center_sq0798 : (center0798.re : ℝ)^2 +
    (center0798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0798 : work0798.theta.ok = true ∧
    work0798.jac.invOK = true ∧ acceptsUnitSq work0798.out = true := by
  norm_num [work0798, contact0798, tau0798, center0798, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0798 : CellCertificate where
  tauBall := tau0798
  contactCenter := center0798
  contactBall := contact0798
  work := work0798
  center_sq := center_sq0798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0798.1
  jac_ok := checks0798.2.1
  accepted := checks0798.2.2

def tau0799 : RatBall :=
  ⟨⟨-57/160, 23/160⟩, 3/320⟩
def center0799 : GaussianRat :=
  ⟨-30133041/125000000, 17660441/200000000⟩
def contact0799 : RatBall := localContactBall tau0799 center0799
def work0799 : RoundedTauEval :=
  evalTau precision tau0799 contact0799 logTwoBall

theorem center_sq0799 : (center0799.re : ℝ)^2 +
    (center0799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0799 : work0799.theta.ok = true ∧
    work0799.jac.invOK = true ∧ acceptsUnitSq work0799.out = true := by
  norm_num [work0799, contact0799, tau0799, center0799, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0799 : CellCertificate where
  tauBall := tau0799
  contactCenter := center0799
  contactBall := contact0799
  work := work0799
  center_sq := center_sq0799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0799.1
  jac_ok := checks0799.2.1
  accepted := checks0799.2.2

def cells : List CellCertificate := [cell0792, cell0793, cell0794, cell0795, cell0796, cell0797, cell0798, cell0799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

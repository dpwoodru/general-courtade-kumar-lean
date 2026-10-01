import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0552 : RatBall :=
  ⟨⟨-63/160, -9/160⟩, 3/320⟩
def center0552 : GaussianRat :=
  ⟨-65046299/250000000, -6715607/200000000⟩
def contact0552 : RatBall := localContactBall tau0552 center0552
def work0552 : RoundedTauEval :=
  evalTau precision tau0552 contact0552 logTwoBall

theorem center_sq0552 : (center0552.re : ℝ)^2 +
    (center0552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0552 : work0552.theta.ok = true ∧
    work0552.jac.invOK = true ∧ acceptsUnitSq work0552.out = true := by
  norm_num [work0552, contact0552, tau0552, center0552, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0552 : CellCertificate where
  tauBall := tau0552
  contactCenter := center0552
  contactBall := contact0552
  work := work0552
  center_sq := center_sq0552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0552.1
  jac_ok := checks0552.2.1
  accepted := checks0552.2.2

def tau0553 : RatBall :=
  ⟨⟨-61/160, -9/160⟩, 3/320⟩
def center0553 : GaussianRat :=
  ⟨-252683709/1000000000, -6774897/200000000⟩
def contact0553 : RatBall := localContactBall tau0553 center0553
def work0553 : RoundedTauEval :=
  evalTau precision tau0553 contact0553 logTwoBall

theorem center_sq0553 : (center0553.re : ℝ)^2 +
    (center0553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0553 : work0553.theta.ok = true ∧
    work0553.jac.invOK = true ∧ acceptsUnitSq work0553.out = true := by
  norm_num [work0553, contact0553, tau0553, center0553, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0553 : CellCertificate where
  tauBall := tau0553
  contactCenter := center0553
  contactBall := contact0553
  work := work0553
  center_sq := center_sq0553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0553.1
  jac_ok := checks0553.2.1
  accepted := checks0553.2.2

def tau0554 : RatBall :=
  ⟨⟨-63/160, -7/160⟩, 3/320⟩
def center0554 : GaussianRat :=
  ⟨-64979987/250000000, -3263977/125000000⟩
def contact0554 : RatBall := localContactBall tau0554 center0554
def work0554 : RoundedTauEval :=
  evalTau precision tau0554 contact0554 logTwoBall

theorem center_sq0554 : (center0554.re : ℝ)^2 +
    (center0554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0554 : work0554.theta.ok = true ∧
    work0554.jac.invOK = true ∧ acceptsUnitSq work0554.out = true := by
  norm_num [work0554, contact0554, tau0554, center0554, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0554 : CellCertificate where
  tauBall := tau0554
  contactCenter := center0554
  contactBall := contact0554
  work := work0554
  center_sq := center_sq0554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0554.1
  jac_ok := checks0554.2.1
  accepted := checks0554.2.2

def tau0555 : RatBall :=
  ⟨⟨-61/160, -7/160⟩, 3/320⟩
def center0555 : GaussianRat :=
  ⟨-252422417/1000000000, -13171007/500000000⟩
def contact0555 : RatBall := localContactBall tau0555 center0555
def work0555 : RoundedTauEval :=
  evalTau precision tau0555 contact0555 logTwoBall

theorem center_sq0555 : (center0555.re : ℝ)^2 +
    (center0555.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0555]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0555 : work0555.theta.ok = true ∧
    work0555.jac.invOK = true ∧ acceptsUnitSq work0555.out = true := by
  norm_num [work0555, contact0555, tau0555, center0555, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0555 : CellCertificate where
  tauBall := tau0555
  contactCenter := center0555
  contactBall := contact0555
  work := work0555
  center_sq := center_sq0555
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0555.1
  jac_ok := checks0555.2.1
  accepted := checks0555.2.2

def tau0556 : RatBall :=
  ⟨⟨-63/160, -1/32⟩, 3/320⟩
def center0556 : GaussianRat :=
  ⟨-259721291/1000000000, -466223/25000000⟩
def contact0556 : RatBall := localContactBall tau0556 center0556
def work0556 : RoundedTauEval :=
  evalTau precision tau0556 contact0556 logTwoBall

theorem center_sq0556 : (center0556.re : ℝ)^2 +
    (center0556.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0556]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0556 : work0556.theta.ok = true ∧
    work0556.jac.invOK = true ∧ acceptsUnitSq work0556.out = true := by
  norm_num [work0556, contact0556, tau0556, center0556, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0556 : CellCertificate where
  tauBall := tau0556
  contactCenter := center0556
  contactBall := contact0556
  work := work0556
  center_sq := center_sq0556
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0556.1
  jac_ok := checks0556.2.1
  accepted := checks0556.2.2

def tau0557 : RatBall :=
  ⟨⟨-61/160, -1/32⟩, 3/320⟩
def center0557 : GaussianRat :=
  ⟨-25222673/100000000, -18813147/1000000000⟩
def contact0557 : RatBall := localContactBall tau0557 center0557
def work0557 : RoundedTauEval :=
  evalTau precision tau0557 contact0557 logTwoBall

theorem center_sq0557 : (center0557.re : ℝ)^2 +
    (center0557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0557 : work0557.theta.ok = true ∧
    work0557.jac.invOK = true ∧ acceptsUnitSq work0557.out = true := by
  norm_num [work0557, contact0557, tau0557, center0557, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0557 : CellCertificate where
  tauBall := tau0557
  contactCenter := center0557
  contactBall := contact0557
  work := work0557
  center_sq := center_sq0557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0557.1
  jac_ok := checks0557.2.1
  accepted := checks0557.2.2

def tau0558 : RatBall :=
  ⟨⟨1/160, -57/160⟩, 3/320⟩
def center0558 : GaussianRat :=
  ⟨311809/62500000, -5174291/20000000⟩
def contact0558 : RatBall := localContactBall tau0558 center0558
def work0558 : RoundedTauEval :=
  evalTau precision tau0558 contact0558 logTwoBall

theorem center_sq0558 : (center0558.re : ℝ)^2 +
    (center0558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0558 : work0558.theta.ok = true ∧
    work0558.jac.invOK = true ∧ acceptsUnitSq work0558.out = true := by
  norm_num [work0558, contact0558, tau0558, center0558, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0558 : CellCertificate where
  tauBall := tau0558
  contactCenter := center0558
  contactBall := contact0558
  work := work0558
  center_sq := center_sq0558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0558.1
  jac_ok := checks0558.2.1
  accepted := checks0558.2.2

def tau0559 : RatBall :=
  ⟨⟨1/160, -11/32⟩, 3/320⟩
def center0559 : GaussianRat :=
  ⟨617179/125000000, -248789139/1000000000⟩
def contact0559 : RatBall := localContactBall tau0559 center0559
def work0559 : RoundedTauEval :=
  evalTau precision tau0559 contact0559 logTwoBall

theorem center_sq0559 : (center0559.re : ℝ)^2 +
    (center0559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0559 : work0559.theta.ok = true ∧
    work0559.jac.invOK = true ∧ acceptsUnitSq work0559.out = true := by
  norm_num [work0559, contact0559, tau0559, center0559, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0559 : CellCertificate where
  tauBall := tau0559
  contactCenter := center0559
  contactBall := contact0559
  work := work0559
  center_sq := center_sq0559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0559.1
  jac_ok := checks0559.2.1
  accepted := checks0559.2.2

def cells : List CellCertificate := [cell0552, cell0553, cell0554, cell0555, cell0556, cell0557, cell0558, cell0559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

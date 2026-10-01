import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0712 : RatBall :=
  ⟨⟨51/160, -31/160⟩, 3/320⟩
def center0712 : GaussianRat :=
  ⟨110447247/500000000, -61169673/500000000⟩
def contact0712 : RatBall := localContactBall tau0712 center0712
def work0712 : RoundedTauEval :=
  evalTau precision tau0712 contact0712 logTwoBall

theorem center_sq0712 : (center0712.re : ℝ)^2 +
    (center0712.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0712]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0712 : work0712.theta.ok = true ∧
    work0712.jac.invOK = true ∧ acceptsUnitSq work0712.out = true := by
  norm_num [work0712, contact0712, tau0712, center0712, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0712 : CellCertificate where
  tauBall := tau0712
  contactCenter := center0712
  contactBall := contact0712
  work := work0712
  center_sq := center_sq0712
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0712.1
  jac_ok := checks0712.2.1
  accepted := checks0712.2.2

def tau0713 : RatBall :=
  ⟨⟨49/160, -29/160⟩, 3/320⟩
def center0713 : GaussianRat :=
  ⟨52985469/250000000, -115229173/1000000000⟩
def contact0713 : RatBall := localContactBall tau0713 center0713
def work0713 : RoundedTauEval :=
  evalTau precision tau0713 contact0713 logTwoBall

theorem center_sq0713 : (center0713.re : ℝ)^2 +
    (center0713.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0713 : work0713.theta.ok = true ∧
    work0713.jac.invOK = true ∧ acceptsUnitSq work0713.out = true := by
  norm_num [work0713, contact0713, tau0713, center0713, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0713 : CellCertificate where
  tauBall := tau0713
  contactCenter := center0713
  contactBall := contact0713
  work := work0713
  center_sq := center_sq0713
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0713.1
  jac_ok := checks0713.2.1
  accepted := checks0713.2.2

def tau0714 : RatBall :=
  ⟨⟨51/160, -29/160⟩, 3/320⟩
def center0714 : GaussianRat :=
  ⟨429614/1953125, -114341983/1000000000⟩
def contact0714 : RatBall := localContactBall tau0714 center0714
def work0714 : RoundedTauEval :=
  evalTau precision tau0714 contact0714 logTwoBall

theorem center_sq0714 : (center0714.re : ℝ)^2 +
    (center0714.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0714]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0714 : work0714.theta.ok = true ∧
    work0714.jac.invOK = true ∧ acceptsUnitSq work0714.out = true := by
  norm_num [work0714, contact0714, tau0714, center0714, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0714 : CellCertificate where
  tauBall := tau0714
  contactCenter := center0714
  contactBall := contact0714
  work := work0714
  center_sq := center_sq0714
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0714.1
  jac_ok := checks0714.2.1
  accepted := checks0714.2.2

def tau0715 : RatBall :=
  ⟨⟨53/160, -31/160⟩, 3/320⟩
def center0715 : GaussianRat :=
  ⟨114433899/500000000, -30340451/250000000⟩
def contact0715 : RatBall := localContactBall tau0715 center0715
def work0715 : RoundedTauEval :=
  evalTau precision tau0715 contact0715 logTwoBall

theorem center_sq0715 : (center0715.re : ℝ)^2 +
    (center0715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0715 : work0715.theta.ok = true ∧
    work0715.jac.invOK = true ∧ acceptsUnitSq work0715.out = true := by
  norm_num [work0715, contact0715, tau0715, center0715, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0715 : CellCertificate where
  tauBall := tau0715
  contactCenter := center0715
  contactBall := contact0715
  work := work0715
  center_sq := center_sq0715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0715.1
  jac_ok := checks0715.2.1
  accepted := checks0715.2.2

def tau0716 : RatBall :=
  ⟨⟨11/32, -31/160⟩, 3/320⟩
def center0716 : GaussianRat :=
  ⟨47354053/200000000, -30090849/250000000⟩
def contact0716 : RatBall := localContactBall tau0716 center0716
def work0716 : RoundedTauEval :=
  evalTau precision tau0716 contact0716 logTwoBall

theorem center_sq0716 : (center0716.re : ℝ)^2 +
    (center0716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0716 : work0716.theta.ok = true ∧
    work0716.jac.invOK = true ∧ acceptsUnitSq work0716.out = true := by
  norm_num [work0716, contact0716, tau0716, center0716, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0716 : CellCertificate where
  tauBall := tau0716
  contactCenter := center0716
  contactBall := contact0716
  work := work0716
  center_sq := center_sq0716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0716.1
  jac_ok := checks0716.2.1
  accepted := checks0716.2.2

def tau0717 : RatBall :=
  ⟨⟨53/160, -29/160⟩, 3/320⟩
def center0717 : GaussianRat :=
  ⟨227914773/1000000000, -56716957/500000000⟩
def contact0717 : RatBall := localContactBall tau0717 center0717
def work0717 : RoundedTauEval :=
  evalTau precision tau0717 contact0717 logTwoBall

theorem center_sq0717 : (center0717.re : ℝ)^2 +
    (center0717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0717 : work0717.theta.ok = true ∧
    work0717.jac.invOK = true ∧ acceptsUnitSq work0717.out = true := by
  norm_num [work0717, contact0717, tau0717, center0717, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0717 : CellCertificate where
  tauBall := tau0717
  contactCenter := center0717
  contactBall := contact0717
  work := work0717
  center_sq := center_sq0717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0717.1
  jac_ok := checks0717.2.1
  accepted := checks0717.2.2

def tau0718 : RatBall :=
  ⟨⟨11/32, -29/160⟩, 3/320⟩
def center0718 : GaussianRat :=
  ⟨117898859/500000000, -112506293/1000000000⟩
def contact0718 : RatBall := localContactBall tau0718 center0718
def work0718 : RoundedTauEval :=
  evalTau precision tau0718 contact0718 logTwoBall

theorem center_sq0718 : (center0718.re : ℝ)^2 +
    (center0718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0718 : work0718.theta.ok = true ∧
    work0718.jac.invOK = true ∧ acceptsUnitSq work0718.out = true := by
  norm_num [work0718, contact0718, tau0718, center0718, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0718 : CellCertificate where
  tauBall := tau0718
  contactCenter := center0718
  contactBall := contact0718
  work := work0718
  center_sq := center_sq0718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0718.1
  jac_ok := checks0718.2.1
  accepted := checks0718.2.2

def tau0719 : RatBall :=
  ⟨⟨49/160, -27/160⟩, 3/320⟩
def center0719 : GaussianRat :=
  ⟨211098659/1000000000, -10718597/100000000⟩
def contact0719 : RatBall := localContactBall tau0719 center0719
def work0719 : RoundedTauEval :=
  evalTau precision tau0719 contact0719 logTwoBall

theorem center_sq0719 : (center0719.re : ℝ)^2 +
    (center0719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0719 : work0719.theta.ok = true ∧
    work0719.jac.invOK = true ∧ acceptsUnitSq work0719.out = true := by
  norm_num [work0719, contact0719, tau0719, center0719, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0719 : CellCertificate where
  tauBall := tau0719
  contactCenter := center0719
  contactBall := contact0719
  work := work0719
  center_sq := center_sq0719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0719.1
  jac_ok := checks0719.2.1
  accepted := checks0719.2.2

def cells : List CellCertificate := [cell0712, cell0713, cell0714, cell0715, cell0716, cell0717, cell0718, cell0719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089

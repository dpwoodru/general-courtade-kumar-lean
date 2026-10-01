import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0584 : RatBall :=
  ⟨⟨13/160, -51/160⟩, 3/320⟩
def center0584 : GaussianRat :=
  ⟨2508961/40000000, -56843321/250000000⟩
def contact0584 : RatBall := localContactBall tau0584 center0584
def work0584 : RoundedTauEval :=
  evalTau precision tau0584 contact0584 logTwoBall

theorem center_sq0584 : (center0584.re : ℝ)^2 +
    (center0584.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0584]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0584 : work0584.theta.ok = true ∧
    work0584.jac.invOK = true ∧ acceptsUnitSq work0584.out = true := by
  norm_num [work0584, contact0584, tau0584, center0584, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0584 : CellCertificate where
  tauBall := tau0584
  contactCenter := center0584
  contactBall := contact0584
  work := work0584
  center_sq := center_sq0584
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0584.1
  jac_ok := checks0584.2.1
  accepted := checks0584.2.2

def tau0585 : RatBall :=
  ⟨⟨3/32, -51/160⟩, 3/320⟩
def center0585 : GaussianRat :=
  ⟨18071427/250000000, -113380411/500000000⟩
def contact0585 : RatBall := localContactBall tau0585 center0585
def work0585 : RoundedTauEval :=
  evalTau precision tau0585 contact0585 logTwoBall

theorem center_sq0585 : (center0585.re : ℝ)^2 +
    (center0585.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0585]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0585 : work0585.theta.ok = true ∧
    work0585.jac.invOK = true ∧ acceptsUnitSq work0585.out = true := by
  norm_num [work0585, contact0585, tau0585, center0585, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0585 : CellCertificate where
  tauBall := tau0585
  contactCenter := center0585
  contactBall := contact0585
  work := work0585
  center_sq := center_sq0585
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0585.1
  jac_ok := checks0585.2.1
  accepted := checks0585.2.2

def tau0586 : RatBall :=
  ⟨⟨13/160, -49/160⟩, 3/320⟩
def center0586 : GaussianRat :=
  ⟨3885599/62500000, -6807377/31250000⟩
def contact0586 : RatBall := localContactBall tau0586 center0586
def work0586 : RoundedTauEval :=
  evalTau precision tau0586 contact0586 logTwoBall

theorem center_sq0586 : (center0586.re : ℝ)^2 +
    (center0586.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0586]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0586 : work0586.theta.ok = true ∧
    work0586.jac.invOK = true ∧ acceptsUnitSq work0586.out = true := by
  norm_num [work0586, contact0586, tau0586, center0586, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0586 : CellCertificate where
  tauBall := tau0586
  contactCenter := center0586
  contactBall := contact0586
  work := work0586
  center_sq := center_sq0586
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0586.1
  jac_ok := checks0586.2.1
  accepted := checks0586.2.2

def tau0587 : RatBall :=
  ⟨⟨3/32, -49/160⟩, 3/320⟩
def center0587 : GaussianRat :=
  ⟨14329959/200000000, -108628837/500000000⟩
def contact0587 : RatBall := localContactBall tau0587 center0587
def work0587 : RoundedTauEval :=
  evalTau precision tau0587 contact0587 logTwoBall

theorem center_sq0587 : (center0587.re : ℝ)^2 +
    (center0587.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0587]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0587 : work0587.theta.ok = true ∧
    work0587.jac.invOK = true ∧ acceptsUnitSq work0587.out = true := by
  norm_num [work0587, contact0587, tau0587, center0587, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0587 : CellCertificate where
  tauBall := tau0587
  contactCenter := center0587
  contactBall := contact0587
  work := work0587
  center_sq := center_sq0587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0587.1
  jac_ok := checks0587.2.1
  accepted := checks0587.2.2

def tau0588 : RatBall :=
  ⟨⟨17/160, -53/160⟩, 3/320⟩
def center0588 : GaussianRat :=
  ⟨82567747/1000000000, -117805603/500000000⟩
def contact0588 : RatBall := localContactBall tau0588 center0588
def work0588 : RoundedTauEval :=
  evalTau precision tau0588 contact0588 logTwoBall

theorem center_sq0588 : (center0588.re : ℝ)^2 +
    (center0588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0588 : work0588.theta.ok = true ∧
    work0588.jac.invOK = true ∧ acceptsUnitSq work0588.out = true := by
  norm_num [work0588, contact0588, tau0588, center0588, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0588 : CellCertificate where
  tauBall := tau0588
  contactCenter := center0588
  contactBall := contact0588
  work := work0588
  center_sq := center_sq0588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0588.1
  jac_ok := checks0588.2.1
  accepted := checks0588.2.2

def tau0589 : RatBall :=
  ⟨⟨17/160, -51/160⟩, 3/320⟩
def center0589 : GaussianRat :=
  ⟨40905123/500000000, -113032697/500000000⟩
def contact0589 : RatBall := localContactBall tau0589 center0589
def work0589 : RoundedTauEval :=
  evalTau precision tau0589 contact0589 logTwoBall

theorem center_sq0589 : (center0589.re : ℝ)^2 +
    (center0589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0589 : work0589.theta.ok = true ∧
    work0589.jac.invOK = true ∧ acceptsUnitSq work0589.out = true := by
  norm_num [work0589, contact0589, tau0589, center0589, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0589 : CellCertificate where
  tauBall := tau0589
  contactCenter := center0589
  contactBall := contact0589
  work := work0589
  center_sq := center_sq0589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0589.1
  jac_ok := checks0589.2.1
  accepted := checks0589.2.2

def tau0590 : RatBall :=
  ⟨⟨19/160, -51/160⟩, 3/320⟩
def center0590 : GaussianRat :=
  ⟨18258621/200000000, -56322187/250000000⟩
def contact0590 : RatBall := localContactBall tau0590 center0590
def work0590 : RoundedTauEval :=
  evalTau precision tau0590 contact0590 logTwoBall

theorem center_sq0590 : (center0590.re : ℝ)^2 +
    (center0590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0590 : work0590.theta.ok = true ∧
    work0590.jac.invOK = true ∧ acceptsUnitSq work0590.out = true := by
  norm_num [work0590, contact0590, tau0590, center0590, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0590 : CellCertificate where
  tauBall := tau0590
  contactCenter := center0590
  contactBall := contact0590
  work := work0590
  center_sq := center_sq0590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0590.1
  jac_ok := checks0590.2.1
  accepted := checks0590.2.2

def tau0591 : RatBall :=
  ⟨⟨17/160, -49/160⟩, 3/320⟩
def center0591 : GaussianRat :=
  ⟨5068403/62500000, -846097/3906250⟩
def contact0591 : RatBall := localContactBall tau0591 center0591
def work0591 : RoundedTauEval :=
  evalTau precision tau0591 contact0591 logTwoBall

theorem center_sq0591 : (center0591.re : ℝ)^2 +
    (center0591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0591 : work0591.theta.ok = true ∧
    work0591.jac.invOK = true ∧ acceptsUnitSq work0591.out = true := by
  norm_num [work0591, contact0591, tau0591, center0591, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0591 : CellCertificate where
  tauBall := tau0591
  contactCenter := center0591
  contactBall := contact0591
  work := work0591
  center_sq := center_sq0591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0591.1
  jac_ok := checks0591.2.1
  accepted := checks0591.2.2

def cells : List CellCertificate := [cell0584, cell0585, cell0586, cell0587, cell0588, cell0589, cell0590, cell0591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073

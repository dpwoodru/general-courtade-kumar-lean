import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0664 : RatBall :=
  ⟨⟨37/160, -37/160⟩, 3/320⟩
def center0664 : GaussianRat :=
  ⟨33162899/200000000, -153992113/1000000000⟩
def contact0664 : RatBall := localContactBall tau0664 center0664
def work0664 : RoundedTauEval :=
  evalTau precision tau0664 contact0664 logTwoBall

theorem center_sq0664 : (center0664.re : ℝ)^2 +
    (center0664.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0664]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0664 : work0664.theta.ok = true ∧
    work0664.jac.invOK = true ∧ acceptsUnitSq work0664.out = true := by
  norm_num [work0664, contact0664, tau0664, center0664, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0664 : CellCertificate where
  tauBall := tau0664
  contactCenter := center0664
  contactBall := contact0664
  work := work0664
  center_sq := center_sq0664
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0664.1
  jac_ok := checks0664.2.1
  accepted := checks0664.2.2

def tau0665 : RatBall :=
  ⟨⟨39/160, -37/160⟩, 3/320⟩
def center0665 : GaussianRat :=
  ⟨174343743/1000000000, -153020771/1000000000⟩
def contact0665 : RatBall := localContactBall tau0665 center0665
def work0665 : RoundedTauEval :=
  evalTau precision tau0665 contact0665 logTwoBall

theorem center_sq0665 : (center0665.re : ℝ)^2 +
    (center0665.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0665]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0665 : work0665.theta.ok = true ∧
    work0665.jac.invOK = true ∧ acceptsUnitSq work0665.out = true := by
  norm_num [work0665, contact0665, tau0665, center0665, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0665 : CellCertificate where
  tauBall := tau0665
  contactCenter := center0665
  contactBall := contact0665
  work := work0665
  center_sq := center_sq0665
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0665.1
  jac_ok := checks0665.2.1
  accepted := checks0665.2.2

def tau0666 : RatBall :=
  ⟨⟨33/160, -7/32⟩, 3/320⟩
def center0666 : GaussianRat :=
  ⟨7386597/50000000, -7357917/50000000⟩
def contact0666 : RatBall := localContactBall tau0666 center0666
def work0666 : RoundedTauEval :=
  evalTau precision tau0666 contact0666 logTwoBall

theorem center_sq0666 : (center0666.re : ℝ)^2 +
    (center0666.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0666]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0666 : work0666.theta.ok = true ∧
    work0666.jac.invOK = true ∧ acceptsUnitSq work0666.out = true := by
  norm_num [work0666, contact0666, tau0666, center0666, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0666 : CellCertificate where
  tauBall := tau0666
  contactCenter := center0666
  contactBall := contact0666
  work := work0666
  center_sq := center_sq0666
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0666.1
  jac_ok := checks0666.2.1
  accepted := checks0666.2.2

def tau0667 : RatBall :=
  ⟨⟨7/32, -7/32⟩, 3/320⟩
def center0667 : GaussianRat :=
  ⟨78170517/500000000, -14632387/100000000⟩
def contact0667 : RatBall := localContactBall tau0667 center0667
def work0667 : RoundedTauEval :=
  evalTau precision tau0667 contact0667 logTwoBall

theorem center_sq0667 : (center0667.re : ℝ)^2 +
    (center0667.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0667]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0667 : work0667.theta.ok = true ∧
    work0667.jac.invOK = true ∧ acceptsUnitSq work0667.out = true := by
  norm_num [work0667, contact0667, tau0667, center0667, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0667 : CellCertificate where
  tauBall := tau0667
  contactCenter := center0667
  contactBall := contact0667
  work := work0667
  center_sq := center_sq0667
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0667.1
  jac_ok := checks0667.2.1
  accepted := checks0667.2.2

def tau0668 : RatBall :=
  ⟨⟨33/160, -33/160⟩, 3/320⟩
def center0668 : GaussianRat :=
  ⟨73472183/500000000, -69270487/500000000⟩
def contact0668 : RatBall := localContactBall tau0668 center0668
def work0668 : RoundedTauEval :=
  evalTau precision tau0668 contact0668 logTwoBall

theorem center_sq0668 : (center0668.re : ℝ)^2 +
    (center0668.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0668]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0668 : work0668.theta.ok = true ∧
    work0668.jac.invOK = true ∧ acceptsUnitSq work0668.out = true := by
  norm_num [work0668, contact0668, tau0668, center0668, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0668 : CellCertificate where
  tauBall := tau0668
  contactCenter := center0668
  contactBall := contact0668
  work := work0668
  center_sq := center_sq0668
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0668.1
  jac_ok := checks0668.2.1
  accepted := checks0668.2.2

def tau0669 : RatBall :=
  ⟨⟨7/32, -33/160⟩, 3/320⟩
def center0669 : GaussianRat :=
  ⟨31103099/200000000, -137761833/1000000000⟩
def contact0669 : RatBall := localContactBall tau0669 center0669
def work0669 : RoundedTauEval :=
  evalTau precision tau0669 contact0669 logTwoBall

theorem center_sq0669 : (center0669.re : ℝ)^2 +
    (center0669.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0669]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0669 : work0669.theta.ok = true ∧
    work0669.jac.invOK = true ∧ acceptsUnitSq work0669.out = true := by
  norm_num [work0669, contact0669, tau0669, center0669, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0669 : CellCertificate where
  tauBall := tau0669
  contactCenter := center0669
  contactBall := contact0669
  work := work0669
  center_sq := center_sq0669
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0669.1
  jac_ok := checks0669.2.1
  accepted := checks0669.2.2

def tau0670 : RatBall :=
  ⟨⟨37/160, -7/32⟩, 3/320⟩
def center0670 : GaussianRat :=
  ⟨164892819/1000000000, -29090197/200000000⟩
def contact0670 : RatBall := localContactBall tau0670 center0670
def work0670 : RoundedTauEval :=
  evalTau precision tau0670 contact0670 logTwoBall

theorem center_sq0670 : (center0670.re : ℝ)^2 +
    (center0670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0670 : work0670.theta.ok = true ∧
    work0670.jac.invOK = true ∧ acceptsUnitSq work0670.out = true := by
  norm_num [work0670, contact0670, tau0670, center0670, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0670 : CellCertificate where
  tauBall := tau0670
  contactCenter := center0670
  contactBall := contact0670
  work := work0670
  center_sq := center_sq0670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0670.1
  jac_ok := checks0670.2.1
  accepted := checks0670.2.2

def tau0671 : RatBall :=
  ⟨⟨39/160, -7/32⟩, 3/320⟩
def center0671 : GaussianRat :=
  ⟨173384937/1000000000, -144541281/1000000000⟩
def contact0671 : RatBall := localContactBall tau0671 center0671
def work0671 : RoundedTauEval :=
  evalTau precision tau0671 contact0671 logTwoBall

theorem center_sq0671 : (center0671.re : ℝ)^2 +
    (center0671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0671 : work0671.theta.ok = true ∧
    work0671.jac.invOK = true ∧ acceptsUnitSq work0671.out = true := by
  norm_num [work0671, contact0671, tau0671, center0671, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0671 : CellCertificate where
  tauBall := tau0671
  contactCenter := center0671
  contactBall := contact0671
  work := work0671
  center_sq := center_sq0671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0671.1
  jac_ok := checks0671.2.1
  accepted := checks0671.2.2

def cells : List CellCertificate := [cell0664, cell0665, cell0666, cell0667, cell0668, cell0669, cell0670, cell0671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083

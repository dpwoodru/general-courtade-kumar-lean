import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0704 : RatBall :=
  ⟨⟨47/160, -31/160⟩, 3/320⟩
def center0704 : GaussianRat :=
  ⟨40948189/200000000, -124226081/1000000000⟩
def contact0704 : RatBall := localContactBall tau0704 center0704
def work0704 : RoundedTauEval :=
  evalTau precision tau0704 contact0704 logTwoBall

theorem center_sq0704 : (center0704.re : ℝ)^2 +
    (center0704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0704 : work0704.theta.ok = true ∧
    work0704.jac.invOK = true ∧ acceptsUnitSq work0704.out = true := by
  norm_num [work0704, contact0704, tau0704, center0704, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0704 : CellCertificate where
  tauBall := tau0704
  contactCenter := center0704
  contactBall := contact0704
  work := work0704
  center_sq := center_sq0704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0704.1
  jac_ok := checks0704.2.1
  accepted := checks0704.2.2

def tau0705 : RatBall :=
  ⟨⟨9/32, -29/160⟩, 3/320⟩
def center0705 : GaussianRat :=
  ⟨97851331/500000000, -116935591/1000000000⟩
def contact0705 : RatBall := localContactBall tau0705 center0705
def work0705 : RoundedTauEval :=
  evalTau precision tau0705 contact0705 logTwoBall

theorem center_sq0705 : (center0705.re : ℝ)^2 +
    (center0705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0705 : work0705.theta.ok = true ∧
    work0705.jac.invOK = true ∧ acceptsUnitSq work0705.out = true := by
  norm_num [work0705, contact0705, tau0705, center0705, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0705 : CellCertificate where
  tauBall := tau0705
  contactCenter := center0705
  contactBall := contact0705
  work := work0705
  center_sq := center_sq0705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0705.1
  jac_ok := checks0705.2.1
  accepted := checks0705.2.2

def tau0706 : RatBall :=
  ⟨⟨47/160, -29/160⟩, 3/320⟩
def center0706 : GaussianRat :=
  ⟨25481847/125000000, -58047077/500000000⟩
def contact0706 : RatBall := localContactBall tau0706 center0706
def work0706 : RoundedTauEval :=
  evalTau precision tau0706 contact0706 logTwoBall

theorem center_sq0706 : (center0706.re : ℝ)^2 +
    (center0706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0706 : work0706.theta.ok = true ∧
    work0706.jac.invOK = true ∧ acceptsUnitSq work0706.out = true := by
  norm_num [work0706, contact0706, tau0706, center0706, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0706 : CellCertificate where
  tauBall := tau0706
  contactCenter := center0706
  contactBall := contact0706
  work := work0706
  center_sq := center_sq0706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0706.1
  jac_ok := checks0706.2.1
  accepted := checks0706.2.2

def tau0707 : RatBall :=
  ⟨⟨9/32, -27/160⟩, 3/320⟩
def center0707 : GaussianRat :=
  ⟨194904883/1000000000, -13595459/125000000⟩
def contact0707 : RatBall := localContactBall tau0707 center0707
def work0707 : RoundedTauEval :=
  evalTau precision tau0707 contact0707 logTwoBall

theorem center_sq0707 : (center0707.re : ℝ)^2 +
    (center0707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0707 : work0707.theta.ok = true ∧
    work0707.jac.invOK = true ∧ acceptsUnitSq work0707.out = true := by
  norm_num [work0707, contact0707, tau0707, center0707, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0707 : CellCertificate where
  tauBall := tau0707
  contactCenter := center0707
  contactBall := contact0707
  work := work0707
  center_sq := center_sq0707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0707.1
  jac_ok := checks0707.2.1
  accepted := checks0707.2.2

def tau0708 : RatBall :=
  ⟨⟨47/160, -27/160⟩, 3/320⟩
def center0708 : GaussianRat :=
  ⟨5075841/25000000, -107985769/1000000000⟩
def contact0708 : RatBall := localContactBall tau0708 center0708
def work0708 : RoundedTauEval :=
  evalTau precision tau0708 contact0708 logTwoBall

theorem center_sq0708 : (center0708.re : ℝ)^2 +
    (center0708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0708 : work0708.theta.ok = true ∧
    work0708.jac.invOK = true ∧ acceptsUnitSq work0708.out = true := by
  norm_num [work0708, contact0708, tau0708, center0708, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0708 : CellCertificate where
  tauBall := tau0708
  contactCenter := center0708
  contactBall := contact0708
  work := work0708
  center_sq := center_sq0708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0708.1
  jac_ok := checks0708.2.1
  accepted := checks0708.2.2

def tau0709 : RatBall :=
  ⟨⟨9/32, -5/32⟩, 3/320⟩
def center0709 : GaussianRat :=
  ⟨194169161/1000000000, -100614871/1000000000⟩
def contact0709 : RatBall := localContactBall tau0709 center0709
def work0709 : RoundedTauEval :=
  evalTau precision tau0709 contact0709 logTwoBall

theorem center_sq0709 : (center0709.re : ℝ)^2 +
    (center0709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0709 : work0709.theta.ok = true ∧
    work0709.jac.invOK = true ∧ acceptsUnitSq work0709.out = true := by
  norm_num [work0709, contact0709, tau0709, center0709, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0709 : CellCertificate where
  tauBall := tau0709
  contactCenter := center0709
  contactBall := contact0709
  work := work0709
  center_sq := center_sq0709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0709.1
  jac_ok := checks0709.2.1
  accepted := checks0709.2.2

def tau0710 : RatBall :=
  ⟨⟨47/160, -5/32⟩, 3/320⟩
def center0710 : GaussianRat :=
  ⟨202276259/1000000000, -49949641/500000000⟩
def contact0710 : RatBall := localContactBall tau0710 center0710
def work0710 : RoundedTauEval :=
  evalTau precision tau0710 contact0710 logTwoBall

theorem center_sq0710 : (center0710.re : ℝ)^2 +
    (center0710.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0710]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0710 : work0710.theta.ok = true ∧
    work0710.jac.invOK = true ∧ acceptsUnitSq work0710.out = true := by
  norm_num [work0710, contact0710, tau0710, center0710, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0710 : CellCertificate where
  tauBall := tau0710
  contactCenter := center0710
  contactBall := contact0710
  work := work0710
  center_sq := center_sq0710
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0710.1
  jac_ok := checks0710.2.1
  accepted := checks0710.2.2

def tau0711 : RatBall :=
  ⟨⟨49/160, -31/160⟩, 3/320⟩
def center0711 : GaussianRat :=
  ⟨106425859/500000000, -123294587/1000000000⟩
def contact0711 : RatBall := localContactBall tau0711 center0711
def work0711 : RoundedTauEval :=
  evalTau precision tau0711 contact0711 logTwoBall

theorem center_sq0711 : (center0711.re : ℝ)^2 +
    (center0711.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0711]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0711 : work0711.theta.ok = true ∧
    work0711.jac.invOK = true ∧ acceptsUnitSq work0711.out = true := by
  norm_num [work0711, contact0711, tau0711, center0711, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0711 : CellCertificate where
  tauBall := tau0711
  contactCenter := center0711
  contactBall := contact0711
  work := work0711
  center_sq := center_sq0711
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0711.1
  jac_ok := checks0711.2.1
  accepted := checks0711.2.2

def cells : List CellCertificate := [cell0704, cell0705, cell0706, cell0707, cell0708, cell0709, cell0710, cell0711]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

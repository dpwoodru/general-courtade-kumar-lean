import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0832 : RatBall :=
  ⟨⟨-49/160, 31/160⟩, 3/320⟩
def center0832 : GaussianRat :=
  ⟨-106425859/500000000, 123294587/1000000000⟩
def contact0832 : RatBall := localContactBall tau0832 center0832
def work0832 : RoundedTauEval :=
  evalTau precision tau0832 contact0832 logTwoBall

theorem center_sq0832 : (center0832.re : ℝ)^2 +
    (center0832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0832 : work0832.theta.ok = true ∧
    work0832.jac.invOK = true ∧ acceptsUnitSq work0832.out = true := by
  norm_num [work0832, contact0832, tau0832, center0832, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0832 : CellCertificate where
  tauBall := tau0832
  contactCenter := center0832
  contactBall := contact0832
  work := work0832
  center_sq := center_sq0832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0832.1
  jac_ok := checks0832.2.1
  accepted := checks0832.2.2

def tau0833 : RatBall :=
  ⟨⟨-47/160, 5/32⟩, 3/320⟩
def center0833 : GaussianRat :=
  ⟨-202276259/1000000000, 49949641/500000000⟩
def contact0833 : RatBall := localContactBall tau0833 center0833
def work0833 : RoundedTauEval :=
  evalTau precision tau0833 contact0833 logTwoBall

theorem center_sq0833 : (center0833.re : ℝ)^2 +
    (center0833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0833 : work0833.theta.ok = true ∧
    work0833.jac.invOK = true ∧ acceptsUnitSq work0833.out = true := by
  norm_num [work0833, contact0833, tau0833, center0833, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0833 : CellCertificate where
  tauBall := tau0833
  contactCenter := center0833
  contactBall := contact0833
  work := work0833
  center_sq := center_sq0833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0833.1
  jac_ok := checks0833.2.1
  accepted := checks0833.2.2

def tau0834 : RatBall :=
  ⟨⟨-9/32, 5/32⟩, 3/320⟩
def center0834 : GaussianRat :=
  ⟨-194169161/1000000000, 100614871/1000000000⟩
def contact0834 : RatBall := localContactBall tau0834 center0834
def work0834 : RoundedTauEval :=
  evalTau precision tau0834 contact0834 logTwoBall

theorem center_sq0834 : (center0834.re : ℝ)^2 +
    (center0834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0834 : work0834.theta.ok = true ∧
    work0834.jac.invOK = true ∧ acceptsUnitSq work0834.out = true := by
  norm_num [work0834, contact0834, tau0834, center0834, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0834 : CellCertificate where
  tauBall := tau0834
  contactCenter := center0834
  contactBall := contact0834
  work := work0834
  center_sq := center_sq0834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0834.1
  jac_ok := checks0834.2.1
  accepted := checks0834.2.2

def tau0835 : RatBall :=
  ⟨⟨-47/160, 27/160⟩, 3/320⟩
def center0835 : GaussianRat :=
  ⟨-5075841/25000000, 107985769/1000000000⟩
def contact0835 : RatBall := localContactBall tau0835 center0835
def work0835 : RoundedTauEval :=
  evalTau precision tau0835 contact0835 logTwoBall

theorem center_sq0835 : (center0835.re : ℝ)^2 +
    (center0835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0835 : work0835.theta.ok = true ∧
    work0835.jac.invOK = true ∧ acceptsUnitSq work0835.out = true := by
  norm_num [work0835, contact0835, tau0835, center0835, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0835 : CellCertificate where
  tauBall := tau0835
  contactCenter := center0835
  contactBall := contact0835
  work := work0835
  center_sq := center_sq0835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0835.1
  jac_ok := checks0835.2.1
  accepted := checks0835.2.2

def tau0836 : RatBall :=
  ⟨⟨-9/32, 27/160⟩, 3/320⟩
def center0836 : GaussianRat :=
  ⟨-194904883/1000000000, 13595459/125000000⟩
def contact0836 : RatBall := localContactBall tau0836 center0836
def work0836 : RoundedTauEval :=
  evalTau precision tau0836 contact0836 logTwoBall

theorem center_sq0836 : (center0836.re : ℝ)^2 +
    (center0836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0836]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0836 : work0836.theta.ok = true ∧
    work0836.jac.invOK = true ∧ acceptsUnitSq work0836.out = true := by
  norm_num [work0836, contact0836, tau0836, center0836, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0836 : CellCertificate where
  tauBall := tau0836
  contactCenter := center0836
  contactBall := contact0836
  work := work0836
  center_sq := center_sq0836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0836.1
  jac_ok := checks0836.2.1
  accepted := checks0836.2.2

def tau0837 : RatBall :=
  ⟨⟨-47/160, 29/160⟩, 3/320⟩
def center0837 : GaussianRat :=
  ⟨-25481847/125000000, 58047077/500000000⟩
def contact0837 : RatBall := localContactBall tau0837 center0837
def work0837 : RoundedTauEval :=
  evalTau precision tau0837 contact0837 logTwoBall

theorem center_sq0837 : (center0837.re : ℝ)^2 +
    (center0837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0837 : work0837.theta.ok = true ∧
    work0837.jac.invOK = true ∧ acceptsUnitSq work0837.out = true := by
  norm_num [work0837, contact0837, tau0837, center0837, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0837 : CellCertificate where
  tauBall := tau0837
  contactCenter := center0837
  contactBall := contact0837
  work := work0837
  center_sq := center_sq0837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0837.1
  jac_ok := checks0837.2.1
  accepted := checks0837.2.2

def tau0838 : RatBall :=
  ⟨⟨-9/32, 29/160⟩, 3/320⟩
def center0838 : GaussianRat :=
  ⟨-97851331/500000000, 116935591/1000000000⟩
def contact0838 : RatBall := localContactBall tau0838 center0838
def work0838 : RoundedTauEval :=
  evalTau precision tau0838 contact0838 logTwoBall

theorem center_sq0838 : (center0838.re : ℝ)^2 +
    (center0838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0838 : work0838.theta.ok = true ∧
    work0838.jac.invOK = true ∧ acceptsUnitSq work0838.out = true := by
  norm_num [work0838, contact0838, tau0838, center0838, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0838 : CellCertificate where
  tauBall := tau0838
  contactCenter := center0838
  contactBall := contact0838
  work := work0838
  center_sq := center_sq0838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0838.1
  jac_ok := checks0838.2.1
  accepted := checks0838.2.2

def tau0839 : RatBall :=
  ⟨⟨-47/160, 31/160⟩, 3/320⟩
def center0839 : GaussianRat :=
  ⟨-40948189/200000000, 124226081/1000000000⟩
def contact0839 : RatBall := localContactBall tau0839 center0839
def work0839 : RoundedTauEval :=
  evalTau precision tau0839 contact0839 logTwoBall

theorem center_sq0839 : (center0839.re : ℝ)^2 +
    (center0839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0839 : work0839.theta.ok = true ∧
    work0839.jac.invOK = true ∧ acceptsUnitSq work0839.out = true := by
  norm_num [work0839, contact0839, tau0839, center0839, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0839 : CellCertificate where
  tauBall := tau0839
  contactCenter := center0839
  contactBall := contact0839
  work := work0839
  center_sq := center_sq0839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0839.1
  jac_ok := checks0839.2.1
  accepted := checks0839.2.2

def cells : List CellCertificate := [cell0832, cell0833, cell0834, cell0835, cell0836, cell0837, cell0838, cell0839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0936 : RatBall :=
  ⟨⟨-19/160, 47/160⟩, 3/320⟩
def center0936 : GaussianRat :=
  ⟨-89749431/1000000000, 206520639/1000000000⟩
def contact0936 : RatBall := localContactBall tau0936 center0936
def work0936 : RoundedTauEval :=
  evalTau precision tau0936 contact0936 logTwoBall

theorem center_sq0936 : (center0936.re : ℝ)^2 +
    (center0936.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0936]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0936 : work0936.theta.ok = true ∧
    work0936.jac.invOK = true ∧ acceptsUnitSq work0936.out = true := by
  norm_num [work0936, contact0936, tau0936, center0936, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0936 : CellCertificate where
  tauBall := tau0936
  contactCenter := center0936
  contactBall := contact0936
  work := work0936
  center_sq := center_sq0936
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0936.1
  jac_ok := checks0936.2.1
  accepted := checks0936.2.2

def tau0937 : RatBall :=
  ⟨⟨-17/160, 47/160⟩, 3/320⟩
def center0937 : GaussianRat :=
  ⟨-20104647/250000000, 10360657/50000000⟩
def contact0937 : RatBall := localContactBall tau0937 center0937
def work0937 : RoundedTauEval :=
  evalTau precision tau0937 contact0937 logTwoBall

theorem center_sq0937 : (center0937.re : ℝ)^2 +
    (center0937.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0937]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0937 : work0937.theta.ok = true ∧
    work0937.jac.invOK = true ∧ acceptsUnitSq work0937.out = true := by
  norm_num [work0937, contact0937, tau0937, center0937, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0937 : CellCertificate where
  tauBall := tau0937
  contactCenter := center0937
  contactBall := contact0937
  work := work0937
  center_sq := center_sq0937
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0937.1
  jac_ok := checks0937.2.1
  accepted := checks0937.2.2

def tau0938 : RatBall :=
  ⟨⟨-3/32, 9/32⟩, 3/320⟩
def center0938 : GaussianRat :=
  ⟨-17620809/250000000, 24810311/125000000⟩
def contact0938 : RatBall := localContactBall tau0938 center0938
def work0938 : RoundedTauEval :=
  evalTau precision tau0938 contact0938 logTwoBall

theorem center_sq0938 : (center0938.re : ℝ)^2 +
    (center0938.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0938]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0938 : work0938.theta.ok = true ∧
    work0938.jac.invOK = true ∧ acceptsUnitSq work0938.out = true := by
  norm_num [work0938, contact0938, tau0938, center0938, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0938 : CellCertificate where
  tauBall := tau0938
  contactCenter := center0938
  contactBall := contact0938
  work := work0938
  center_sq := center_sq0938
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0938.1
  jac_ok := checks0938.2.1
  accepted := checks0938.2.2

def tau0939 : RatBall :=
  ⟨⟨-13/160, 9/32⟩, 3/320⟩
def center0939 : GaussianRat :=
  ⟨-30576347/500000000, 99498463/500000000⟩
def contact0939 : RatBall := localContactBall tau0939 center0939
def work0939 : RoundedTauEval :=
  evalTau precision tau0939 contact0939 logTwoBall

theorem center_sq0939 : (center0939.re : ℝ)^2 +
    (center0939.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0939]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0939 : work0939.theta.ok = true ∧
    work0939.jac.invOK = true ∧ acceptsUnitSq work0939.out = true := by
  norm_num [work0939, contact0939, tau0939, center0939, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0939 : CellCertificate where
  tauBall := tau0939
  contactCenter := center0939
  contactBall := contact0939
  work := work0939
  center_sq := center_sq0939
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0939.1
  jac_ok := checks0939.2.1
  accepted := checks0939.2.2

def tau0940 : RatBall :=
  ⟨⟨-3/32, 47/160⟩, 3/320⟩
def center0940 : GaussianRat :=
  ⟨-71049459/1000000000, 207833009/1000000000⟩
def contact0940 : RatBall := localContactBall tau0940 center0940
def work0940 : RoundedTauEval :=
  evalTau precision tau0940 contact0940 logTwoBall

theorem center_sq0940 : (center0940.re : ℝ)^2 +
    (center0940.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0940]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0940 : work0940.theta.ok = true ∧
    work0940.jac.invOK = true ∧ acceptsUnitSq work0940.out = true := by
  norm_num [work0940, contact0940, tau0940, center0940, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0940 : CellCertificate where
  tauBall := tau0940
  contactCenter := center0940
  contactBall := contact0940
  work := work0940
  center_sq := center_sq0940
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0940.1
  jac_ok := checks0940.2.1
  accepted := checks0940.2.2

def tau0941 : RatBall :=
  ⟨⟨-13/160, 47/160⟩, 3/320⟩
def center0941 : GaussianRat :=
  ⟨-61646237/1000000000, 5209469/25000000⟩
def contact0941 : RatBall := localContactBall tau0941 center0941
def work0941 : RoundedTauEval :=
  evalTau precision tau0941 contact0941 logTwoBall

theorem center_sq0941 : (center0941.re : ℝ)^2 +
    (center0941.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0941]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0941 : work0941.theta.ok = true ∧
    work0941.jac.invOK = true ∧ acceptsUnitSq work0941.out = true := by
  norm_num [work0941, contact0941, tau0941, center0941, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0941 : CellCertificate where
  tauBall := tau0941
  contactCenter := center0941
  contactBall := contact0941
  work := work0941
  center_sq := center_sq0941
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0941.1
  jac_ok := checks0941.2.1
  accepted := checks0941.2.2

def tau0942 : RatBall :=
  ⟨⟨-11/160, 9/32⟩, 3/320⟩
def center0942 : GaussianRat :=
  ⟨-25896777/500000000, 199440199/1000000000⟩
def contact0942 : RatBall := localContactBall tau0942 center0942
def work0942 : RoundedTauEval :=
  evalTau precision tau0942 contact0942 logTwoBall

theorem center_sq0942 : (center0942.re : ℝ)^2 +
    (center0942.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0942]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0942 : work0942.theta.ok = true ∧
    work0942.jac.invOK = true ∧ acceptsUnitSq work0942.out = true := by
  norm_num [work0942, contact0942, tau0942, center0942, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0942 : CellCertificate where
  tauBall := tau0942
  contactCenter := center0942
  contactBall := contact0942
  work := work0942
  center_sq := center_sq0942
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0942.1
  jac_ok := checks0942.2.1
  accepted := checks0942.2.2

def tau0943 : RatBall :=
  ⟨⟨-9/160, 9/32⟩, 3/320⟩
def center0943 : GaussianRat :=
  ⟨-21205027/500000000, 199811247/1000000000⟩
def contact0943 : RatBall := localContactBall tau0943 center0943
def work0943 : RoundedTauEval :=
  evalTau precision tau0943 contact0943 logTwoBall

theorem center_sq0943 : (center0943.re : ℝ)^2 +
    (center0943.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0943]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0943 : work0943.theta.ok = true ∧
    work0943.jac.invOK = true ∧ acceptsUnitSq work0943.out = true := by
  norm_num [work0943, contact0943, tau0943, center0943, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0943 : CellCertificate where
  tauBall := tau0943
  contactCenter := center0943
  contactBall := contact0943
  work := work0943
  center_sq := center_sq0943
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0943.1
  jac_ok := checks0943.2.1
  accepted := checks0943.2.2

def cells : List CellCertificate := [cell0936, cell0937, cell0938, cell0939, cell0940, cell0941, cell0942, cell0943]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

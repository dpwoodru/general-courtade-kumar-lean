import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0952 : RatBall :=
  ⟨⟨-17/160, 49/160⟩, 3/320⟩
def center0952 : GaussianRat :=
  ⟨-5068403/62500000, 846097/3906250⟩
def contact0952 : RatBall := localContactBall tau0952 center0952
def work0952 : RoundedTauEval :=
  evalTau precision tau0952 contact0952 logTwoBall

theorem center_sq0952 : (center0952.re : ℝ)^2 +
    (center0952.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0952]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0952 : work0952.theta.ok = true ∧
    work0952.jac.invOK = true ∧ acceptsUnitSq work0952.out = true := by
  norm_num [work0952, contact0952, tau0952, center0952, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0952 : CellCertificate where
  tauBall := tau0952
  contactCenter := center0952
  contactBall := contact0952
  work := work0952
  center_sq := center_sq0952
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0952.1
  jac_ok := checks0952.2.1
  accepted := checks0952.2.2

def tau0953 : RatBall :=
  ⟨⟨-19/160, 51/160⟩, 3/320⟩
def center0953 : GaussianRat :=
  ⟨-18258621/200000000, 56322187/250000000⟩
def contact0953 : RatBall := localContactBall tau0953 center0953
def work0953 : RoundedTauEval :=
  evalTau precision tau0953 contact0953 logTwoBall

theorem center_sq0953 : (center0953.re : ℝ)^2 +
    (center0953.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0953]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0953 : work0953.theta.ok = true ∧
    work0953.jac.invOK = true ∧ acceptsUnitSq work0953.out = true := by
  norm_num [work0953, contact0953, tau0953, center0953, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0953 : CellCertificate where
  tauBall := tau0953
  contactCenter := center0953
  contactBall := contact0953
  work := work0953
  center_sq := center_sq0953
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0953.1
  jac_ok := checks0953.2.1
  accepted := checks0953.2.2

def tau0954 : RatBall :=
  ⟨⟨-17/160, 51/160⟩, 3/320⟩
def center0954 : GaussianRat :=
  ⟨-40905123/500000000, 113032697/500000000⟩
def contact0954 : RatBall := localContactBall tau0954 center0954
def work0954 : RoundedTauEval :=
  evalTau precision tau0954 contact0954 logTwoBall

theorem center_sq0954 : (center0954.re : ℝ)^2 +
    (center0954.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0954]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0954 : work0954.theta.ok = true ∧
    work0954.jac.invOK = true ∧ acceptsUnitSq work0954.out = true := by
  norm_num [work0954, contact0954, tau0954, center0954, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0954 : CellCertificate where
  tauBall := tau0954
  contactCenter := center0954
  contactBall := contact0954
  work := work0954
  center_sq := center_sq0954
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0954.1
  jac_ok := checks0954.2.1
  accepted := checks0954.2.2

def tau0955 : RatBall :=
  ⟨⟨-17/160, 53/160⟩, 3/320⟩
def center0955 : GaussianRat :=
  ⟨-82567747/1000000000, 117805603/500000000⟩
def contact0955 : RatBall := localContactBall tau0955 center0955
def work0955 : RoundedTauEval :=
  evalTau precision tau0955 contact0955 logTwoBall

theorem center_sq0955 : (center0955.re : ℝ)^2 +
    (center0955.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0955]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0955 : work0955.theta.ok = true ∧
    work0955.jac.invOK = true ∧ acceptsUnitSq work0955.out = true := by
  norm_num [work0955, contact0955, tau0955, center0955, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0955 : CellCertificate where
  tauBall := tau0955
  contactCenter := center0955
  contactBall := contact0955
  work := work0955
  center_sq := center_sq0955
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0955.1
  jac_ok := checks0955.2.1
  accepted := checks0955.2.2

def tau0956 : RatBall :=
  ⟨⟨-3/32, 49/160⟩, 3/320⟩
def center0956 : GaussianRat :=
  ⟨-14329959/200000000, 108628837/500000000⟩
def contact0956 : RatBall := localContactBall tau0956 center0956
def work0956 : RoundedTauEval :=
  evalTau precision tau0956 contact0956 logTwoBall

theorem center_sq0956 : (center0956.re : ℝ)^2 +
    (center0956.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0956]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0956 : work0956.theta.ok = true ∧
    work0956.jac.invOK = true ∧ acceptsUnitSq work0956.out = true := by
  norm_num [work0956, contact0956, tau0956, center0956, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0956 : CellCertificate where
  tauBall := tau0956
  contactCenter := center0956
  contactBall := contact0956
  work := work0956
  center_sq := center_sq0956
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0956.1
  jac_ok := checks0956.2.1
  accepted := checks0956.2.2

def tau0957 : RatBall :=
  ⟨⟨-13/160, 49/160⟩, 3/320⟩
def center0957 : GaussianRat :=
  ⟨-3885599/62500000, 6807377/31250000⟩
def contact0957 : RatBall := localContactBall tau0957 center0957
def work0957 : RoundedTauEval :=
  evalTau precision tau0957 contact0957 logTwoBall

theorem center_sq0957 : (center0957.re : ℝ)^2 +
    (center0957.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0957]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0957 : work0957.theta.ok = true ∧
    work0957.jac.invOK = true ∧ acceptsUnitSq work0957.out = true := by
  norm_num [work0957, contact0957, tau0957, center0957, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0957 : CellCertificate where
  tauBall := tau0957
  contactCenter := center0957
  contactBall := contact0957
  work := work0957
  center_sq := center_sq0957
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0957.1
  jac_ok := checks0957.2.1
  accepted := checks0957.2.2

def tau0958 : RatBall :=
  ⟨⟨-3/32, 51/160⟩, 3/320⟩
def center0958 : GaussianRat :=
  ⟨-18071427/250000000, 113380411/500000000⟩
def contact0958 : RatBall := localContactBall tau0958 center0958
def work0958 : RoundedTauEval :=
  evalTau precision tau0958 contact0958 logTwoBall

theorem center_sq0958 : (center0958.re : ℝ)^2 +
    (center0958.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0958]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0958 : work0958.theta.ok = true ∧
    work0958.jac.invOK = true ∧ acceptsUnitSq work0958.out = true := by
  norm_num [work0958, contact0958, tau0958, center0958, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0958 : CellCertificate where
  tauBall := tau0958
  contactCenter := center0958
  contactBall := contact0958
  work := work0958
  center_sq := center_sq0958
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0958.1
  jac_ok := checks0958.2.1
  accepted := checks0958.2.2

def tau0959 : RatBall :=
  ⟨⟨-13/160, 51/160⟩, 3/320⟩
def center0959 : GaussianRat :=
  ⟨-2508961/40000000, 56843321/250000000⟩
def contact0959 : RatBall := localContactBall tau0959 center0959
def work0959 : RoundedTauEval :=
  evalTau precision tau0959 contact0959 logTwoBall

theorem center_sq0959 : (center0959.re : ℝ)^2 +
    (center0959.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0959]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0959 : work0959.theta.ok = true ∧
    work0959.jac.invOK = true ∧ acceptsUnitSq work0959.out = true := by
  norm_num [work0959, contact0959, tau0959, center0959, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0959 : CellCertificate where
  tauBall := tau0959
  contactCenter := center0959
  contactBall := contact0959
  work := work0959
  center_sq := center_sq0959
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0959.1
  jac_ok := checks0959.2.1
  accepted := checks0959.2.2

def cells : List CellCertificate := [cell0952, cell0953, cell0954, cell0955, cell0956, cell0957, cell0958, cell0959]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119

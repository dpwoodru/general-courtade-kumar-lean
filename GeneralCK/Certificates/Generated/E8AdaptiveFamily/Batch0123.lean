import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0984 : RatBall :=
  ⟨⟨-1/160, 11/32⟩, 3/320⟩
def center0984 : GaussianRat :=
  ⟨-617179/125000000, 248789139/1000000000⟩
def contact0984 : RatBall := localContactBall tau0984 center0984
def work0984 : RoundedTauEval :=
  evalTau precision tau0984 contact0984 logTwoBall

theorem center_sq0984 : (center0984.re : ℝ)^2 +
    (center0984.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0984]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0984 : work0984.theta.ok = true ∧
    work0984.jac.invOK = true ∧ acceptsUnitSq work0984.out = true := by
  norm_num [work0984, contact0984, tau0984, center0984, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0984 : CellCertificate where
  tauBall := tau0984
  contactCenter := center0984
  contactBall := contact0984
  work := work0984
  center_sq := center_sq0984
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0984.1
  jac_ok := checks0984.2.1
  accepted := checks0984.2.2

def tau0985 : RatBall :=
  ⟨⟨-1/160, 57/160⟩, 3/320⟩
def center0985 : GaussianRat :=
  ⟨-311809/62500000, 5174291/20000000⟩
def contact0985 : RatBall := localContactBall tau0985 center0985
def work0985 : RoundedTauEval :=
  evalTau precision tau0985 contact0985 logTwoBall

theorem center_sq0985 : (center0985.re : ℝ)^2 +
    (center0985.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0985]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0985 : work0985.theta.ok = true ∧
    work0985.jac.invOK = true ∧ acceptsUnitSq work0985.out = true := by
  norm_num [work0985, contact0985, tau0985, center0985, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0985 : CellCertificate where
  tauBall := tau0985
  contactCenter := center0985
  contactBall := contact0985
  work := work0985
  center_sq := center_sq0985
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0985.1
  jac_ok := checks0985.2.1
  accepted := checks0985.2.2

def tau0986 : RatBall :=
  ⟨⟨61/160, 1/32⟩, 3/320⟩
def center0986 : GaussianRat :=
  ⟨25222673/100000000, 18813147/1000000000⟩
def contact0986 : RatBall := localContactBall tau0986 center0986
def work0986 : RoundedTauEval :=
  evalTau precision tau0986 contact0986 logTwoBall

theorem center_sq0986 : (center0986.re : ℝ)^2 +
    (center0986.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0986 : work0986.theta.ok = true ∧
    work0986.jac.invOK = true ∧ acceptsUnitSq work0986.out = true := by
  norm_num [work0986, contact0986, tau0986, center0986, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0986 : CellCertificate where
  tauBall := tau0986
  contactCenter := center0986
  contactBall := contact0986
  work := work0986
  center_sq := center_sq0986
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0986.1
  jac_ok := checks0986.2.1
  accepted := checks0986.2.2

def tau0987 : RatBall :=
  ⟨⟨63/160, 1/32⟩, 3/320⟩
def center0987 : GaussianRat :=
  ⟨259721291/1000000000, 466223/25000000⟩
def contact0987 : RatBall := localContactBall tau0987 center0987
def work0987 : RoundedTauEval :=
  evalTau precision tau0987 contact0987 logTwoBall

theorem center_sq0987 : (center0987.re : ℝ)^2 +
    (center0987.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0987]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0987 : work0987.theta.ok = true ∧
    work0987.jac.invOK = true ∧ acceptsUnitSq work0987.out = true := by
  norm_num [work0987, contact0987, tau0987, center0987, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0987 : CellCertificate where
  tauBall := tau0987
  contactCenter := center0987
  contactBall := contact0987
  work := work0987
  center_sq := center_sq0987
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0987.1
  jac_ok := checks0987.2.1
  accepted := checks0987.2.2

def tau0988 : RatBall :=
  ⟨⟨61/160, 7/160⟩, 3/320⟩
def center0988 : GaussianRat :=
  ⟨252422417/1000000000, 13171007/500000000⟩
def contact0988 : RatBall := localContactBall tau0988 center0988
def work0988 : RoundedTauEval :=
  evalTau precision tau0988 contact0988 logTwoBall

theorem center_sq0988 : (center0988.re : ℝ)^2 +
    (center0988.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0988]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0988 : work0988.theta.ok = true ∧
    work0988.jac.invOK = true ∧ acceptsUnitSq work0988.out = true := by
  norm_num [work0988, contact0988, tau0988, center0988, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0988 : CellCertificate where
  tauBall := tau0988
  contactCenter := center0988
  contactBall := contact0988
  work := work0988
  center_sq := center_sq0988
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0988.1
  jac_ok := checks0988.2.1
  accepted := checks0988.2.2

def tau0989 : RatBall :=
  ⟨⟨63/160, 7/160⟩, 3/320⟩
def center0989 : GaussianRat :=
  ⟨64979987/250000000, 3263977/125000000⟩
def contact0989 : RatBall := localContactBall tau0989 center0989
def work0989 : RoundedTauEval :=
  evalTau precision tau0989 contact0989 logTwoBall

theorem center_sq0989 : (center0989.re : ℝ)^2 +
    (center0989.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0989]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0989 : work0989.theta.ok = true ∧
    work0989.jac.invOK = true ∧ acceptsUnitSq work0989.out = true := by
  norm_num [work0989, contact0989, tau0989, center0989, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0989 : CellCertificate where
  tauBall := tau0989
  contactCenter := center0989
  contactBall := contact0989
  work := work0989
  center_sq := center_sq0989
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0989.1
  jac_ok := checks0989.2.1
  accepted := checks0989.2.2

def tau0990 : RatBall :=
  ⟨⟨61/160, 9/160⟩, 3/320⟩
def center0990 : GaussianRat :=
  ⟨252683709/1000000000, 6774897/200000000⟩
def contact0990 : RatBall := localContactBall tau0990 center0990
def work0990 : RoundedTauEval :=
  evalTau precision tau0990 contact0990 logTwoBall

theorem center_sq0990 : (center0990.re : ℝ)^2 +
    (center0990.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0990]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0990 : work0990.theta.ok = true ∧
    work0990.jac.invOK = true ∧ acceptsUnitSq work0990.out = true := by
  norm_num [work0990, contact0990, tau0990, center0990, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0990 : CellCertificate where
  tauBall := tau0990
  contactCenter := center0990
  contactBall := contact0990
  work := work0990
  center_sq := center_sq0990
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0990.1
  jac_ok := checks0990.2.1
  accepted := checks0990.2.2

def tau0991 : RatBall :=
  ⟨⟨63/160, 9/160⟩, 3/320⟩
def center0991 : GaussianRat :=
  ⟨65046299/250000000, 6715607/200000000⟩
def contact0991 : RatBall := localContactBall tau0991 center0991
def work0991 : RoundedTauEval :=
  evalTau precision tau0991 contact0991 logTwoBall

theorem center_sq0991 : (center0991.re : ℝ)^2 +
    (center0991.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0991]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0991 : work0991.theta.ok = true ∧
    work0991.jac.invOK = true ∧ acceptsUnitSq work0991.out = true := by
  norm_num [work0991, contact0991, tau0991, center0991, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0991 : CellCertificate where
  tauBall := tau0991
  contactCenter := center0991
  contactBall := contact0991
  work := work0991
  center_sq := center_sq0991
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0991.1
  jac_ok := checks0991.2.1
  accepted := checks0991.2.2

def cells : List CellCertificate := [cell0984, cell0985, cell0986, cell0987, cell0988, cell0989, cell0990, cell0991]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

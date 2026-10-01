import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1976 : RatBall :=
  ⟨⟨-69/320, 93/320⟩, 3/640⟩
def center1976 : GaussianRat :=
  ⟨-32008397/200000000, 245849/1250000⟩
def contact1976 : RatBall := localContactBall tau1976 center1976
def work1976 : RoundedTauEval :=
  evalTau precision tau1976 contact1976 logTwoBall

theorem center_sq1976 : (center1976.re : ℝ)^2 +
    (center1976.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1976]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1976 : work1976.theta.ok = true ∧
    work1976.jac.invOK = true ∧ acceptsUnitSq work1976.out = true := by
  norm_num [work1976, contact1976, tau1976, center1976, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1976 : CellCertificate where
  tauBall := tau1976
  contactCenter := center1976
  contactBall := contact1976
  work := work1976
  center_sq := center_sq1976
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1976.1
  jac_ok := checks1976.2.1
  accepted := checks1976.2.2

def tau1977 : RatBall :=
  ⟨⟨-71/320, 19/64⟩, 3/640⟩
def center1977 : GaussianRat :=
  ⟨-165085801/1000000000, 40098349/200000000⟩
def contact1977 : RatBall := localContactBall tau1977 center1977
def work1977 : RoundedTauEval :=
  evalTau precision tau1977 contact1977 logTwoBall

theorem center_sq1977 : (center1977.re : ℝ)^2 +
    (center1977.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1977]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1977 : work1977.theta.ok = true ∧
    work1977.jac.invOK = true ∧ acceptsUnitSq work1977.out = true := by
  norm_num [work1977, contact1977, tau1977, center1977, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1977 : CellCertificate where
  tauBall := tau1977
  contactCenter := center1977
  contactBall := contact1977
  work := work1977
  center_sq := center_sq1977
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1977.1
  jac_ok := checks1977.2.1
  accepted := checks1977.2.2

def tau1978 : RatBall :=
  ⟨⟨-69/320, 19/64⟩, 3/640⟩
def center1978 : GaussianRat :=
  ⟨-80325427/500000000, 201116047/1000000000⟩
def contact1978 : RatBall := localContactBall tau1978 center1978
def work1978 : RoundedTauEval :=
  evalTau precision tau1978 contact1978 logTwoBall

theorem center_sq1978 : (center1978.re : ℝ)^2 +
    (center1978.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1978]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1978 : work1978.theta.ok = true ∧
    work1978.jac.invOK = true ∧ acceptsUnitSq work1978.out = true := by
  norm_num [work1978, contact1978, tau1978, center1978, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1978 : CellCertificate where
  tauBall := tau1978
  contactCenter := center1978
  contactBall := contact1978
  work := work1978
  center_sq := center_sq1978
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1978.1
  jac_ok := checks1978.2.1
  accepted := checks1978.2.2

def tau1979 : RatBall :=
  ⟨⟨-67/320, 93/320⟩, 3/640⟩
def center1979 : GaussianRat :=
  ⟨-3112069/20000000, 197272757/1000000000⟩
def contact1979 : RatBall := localContactBall tau1979 center1979
def work1979 : RoundedTauEval :=
  evalTau precision tau1979 contact1979 logTwoBall

theorem center_sq1979 : (center1979.re : ℝ)^2 +
    (center1979.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1979]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1979 : work1979.theta.ok = true ∧
    work1979.jac.invOK = true ∧ acceptsUnitSq work1979.out = true := by
  norm_num [work1979, contact1979, tau1979, center1979, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1979 : CellCertificate where
  tauBall := tau1979
  contactCenter := center1979
  contactBall := contact1979
  work := work1979
  center_sq := center_sq1979
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1979.1
  jac_ok := checks1979.2.1
  accepted := checks1979.2.2

def tau1980 : RatBall :=
  ⟨⟨-13/64, 93/320⟩, 3/640⟩
def center1980 : GaussianRat :=
  ⟨-151148249/1000000000, 98926301/500000000⟩
def contact1980 : RatBall := localContactBall tau1980 center1980
def work1980 : RoundedTauEval :=
  evalTau precision tau1980 contact1980 logTwoBall

theorem center_sq1980 : (center1980.re : ℝ)^2 +
    (center1980.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1980]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1980 : work1980.theta.ok = true ∧
    work1980.jac.invOK = true ∧ acceptsUnitSq work1980.out = true := by
  norm_num [work1980, contact1980, tau1980, center1980, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1980 : CellCertificate where
  tauBall := tau1980
  contactCenter := center1980
  contactBall := contact1980
  work := work1980
  center_sq := center_sq1980
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1980.1
  jac_ok := checks1980.2.1
  accepted := checks1980.2.2

def tau1981 : RatBall :=
  ⟨⟨-67/320, 19/64⟩, 3/640⟩
def center1981 : GaussianRat :=
  ⟨-78099293/500000000, 100863299/500000000⟩
def contact1981 : RatBall := localContactBall tau1981 center1981
def work1981 : RoundedTauEval :=
  evalTau precision tau1981 contact1981 logTwoBall

theorem center_sq1981 : (center1981.re : ℝ)^2 +
    (center1981.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1981]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1981 : work1981.theta.ok = true ∧
    work1981.jac.invOK = true ∧ acceptsUnitSq work1981.out = true := by
  norm_num [work1981, contact1981, tau1981, center1981, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1981 : CellCertificate where
  tauBall := tau1981
  contactCenter := center1981
  contactBall := contact1981
  work := work1981
  center_sq := center_sq1981
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1981.1
  jac_ok := checks1981.2.1
  accepted := checks1981.2.2

def tau1982 : RatBall :=
  ⟨⟨-13/64, 19/64⟩, 3/640⟩
def center1982 : GaussianRat :=
  ⟨-30345869/200000000, 40464617/200000000⟩
def contact1982 : RatBall := localContactBall tau1982 center1982
def work1982 : RoundedTauEval :=
  evalTau precision tau1982 contact1982 logTwoBall

theorem center_sq1982 : (center1982.re : ℝ)^2 +
    (center1982.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1982]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1982 : work1982.theta.ok = true ∧
    work1982.jac.invOK = true ∧ acceptsUnitSq work1982.out = true := by
  norm_num [work1982, contact1982, tau1982, center1982, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1982 : CellCertificate where
  tauBall := tau1982
  contactCenter := center1982
  contactBall := contact1982
  work := work1982
  center_sq := center_sq1982
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1982.1
  jac_ok := checks1982.2.1
  accepted := checks1982.2.2

def tau1983 : RatBall :=
  ⟨⟨-17/64, 97/320⟩, 3/640⟩
def center1983 : GaussianRat :=
  ⟨-49086427/250000000, 200064207/1000000000⟩
def contact1983 : RatBall := localContactBall tau1983 center1983
def work1983 : RoundedTauEval :=
  evalTau precision tau1983 contact1983 logTwoBall

theorem center_sq1983 : (center1983.re : ℝ)^2 +
    (center1983.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1983]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1983 : work1983.theta.ok = true ∧
    work1983.jac.invOK = true ∧ acceptsUnitSq work1983.out = true := by
  norm_num [work1983, contact1983, tau1983, center1983, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1983 : CellCertificate where
  tauBall := tau1983
  contactCenter := center1983
  contactBall := contact1983
  work := work1983
  center_sq := center_sq1983
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1983.1
  jac_ok := checks1983.2.1
  accepted := checks1983.2.2

def cells : List CellCertificate := [cell1976, cell1977, cell1978, cell1979, cell1980, cell1981, cell1982, cell1983]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247

import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1968 : RatBall :=
  ⟨⟨-77/320, 93/320⟩, 3/640⟩
def center1968 : GaussianRat :=
  ⟨-44405679/250000000, 194173939/1000000000⟩
def contact1968 : RatBall := localContactBall tau1968 center1968
def work1968 : RoundedTauEval :=
  evalTau precision tau1968 contact1968 logTwoBall

theorem center_sq1968 : (center1968.re : ℝ)^2 +
    (center1968.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1968]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1968 : work1968.theta.ok = true ∧
    work1968.jac.invOK = true ∧ acceptsUnitSq work1968.out = true := by
  norm_num [work1968, contact1968, tau1968, center1968, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1968 : CellCertificate where
  tauBall := tau1968
  contactCenter := center1968
  contactBall := contact1968
  work := work1968
  center_sq := center_sq1968
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1968.1
  jac_ok := checks1968.2.1
  accepted := checks1968.2.2

def tau1969 : RatBall :=
  ⟨⟨-79/320, 19/64⟩, 3/640⟩
def center1969 : GaussianRat :=
  ⟨-91322907/500000000, 98931697/500000000⟩
def contact1969 : RatBall := localContactBall tau1969 center1969
def work1969 : RoundedTauEval :=
  evalTau precision tau1969 contact1969 logTwoBall

theorem center_sq1969 : (center1969.re : ℝ)^2 +
    (center1969.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1969]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1969 : work1969.theta.ok = true ∧
    work1969.jac.invOK = true ∧ acceptsUnitSq work1969.out = true := by
  norm_num [work1969, contact1969, tau1969, center1969, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1969 : CellCertificate where
  tauBall := tau1969
  contactCenter := center1969
  contactBall := contact1969
  work := work1969
  center_sq := center_sq1969
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1969.1
  jac_ok := checks1969.2.1
  accepted := checks1969.2.2

def tau1970 : RatBall :=
  ⟨⟨-77/320, 19/64⟩, 3/640⟩
def center1970 : GaussianRat :=
  ⟨-35656681/200000000, 198539511/1000000000⟩
def contact1970 : RatBall := localContactBall tau1970 center1970
def work1970 : RoundedTauEval :=
  evalTau precision tau1970 contact1970 logTwoBall

theorem center_sq1970 : (center1970.re : ℝ)^2 +
    (center1970.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1970]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1970 : work1970.theta.ok = true ∧
    work1970.jac.invOK = true ∧ acceptsUnitSq work1970.out = true := by
  norm_num [work1970, contact1970, tau1970, center1970, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1970 : CellCertificate where
  tauBall := tau1970
  contactCenter := center1970
  contactBall := contact1970
  work := work1970
  center_sq := center_sq1970
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1970.1
  jac_ok := checks1970.2.1
  accepted := checks1970.2.2

def tau1971 : RatBall :=
  ⟨⟨-15/64, 93/320⟩, 3/640⟩
def center1971 : GaussianRat :=
  ⟨-173254189/1000000000, 38963859/200000000⟩
def contact1971 : RatBall := localContactBall tau1971 center1971
def work1971 : RoundedTauEval :=
  evalTau precision tau1971 contact1971 logTwoBall

theorem center_sq1971 : (center1971.re : ℝ)^2 +
    (center1971.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1971]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1971 : work1971.theta.ok = true ∧
    work1971.jac.invOK = true ∧ acceptsUnitSq work1971.out = true := by
  norm_num [work1971, contact1971, tau1971, center1971, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1971 : CellCertificate where
  tauBall := tau1971
  contactCenter := center1971
  contactBall := contact1971
  work := work1971
  center_sq := center_sq1971
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1971.1
  jac_ok := checks1971.2.1
  accepted := checks1971.2.2

def tau1972 : RatBall :=
  ⟨⟨-73/320, 93/320⟩, 3/640⟩
def center1972 : GaussianRat :=
  ⟨-84433841/500000000, 195452163/1000000000⟩
def contact1972 : RatBall := localContactBall tau1972 center1972
def work1972 : RoundedTauEval :=
  evalTau precision tau1972 contact1972 logTwoBall

theorem center_sq1972 : (center1972.re : ℝ)^2 +
    (center1972.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1972]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1972 : work1972.theta.ok = true ∧
    work1972.jac.invOK = true ∧ acceptsUnitSq work1972.out = true := by
  norm_num [work1972, contact1972, tau1972, center1972, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1972 : CellCertificate where
  tauBall := tau1972
  contactCenter := center1972
  contactBall := contact1972
  work := work1972
  center_sq := center_sq1972
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1972.1
  jac_ok := checks1972.2.1
  accepted := checks1972.2.2

def tau1973 : RatBall :=
  ⟨⟨-15/64, 19/64⟩, 3/640⟩
def center1973 : GaussianRat :=
  ⟨-43475599/250000000, 199203157/1000000000⟩
def contact1973 : RatBall := localContactBall tau1973 center1973
def work1973 : RoundedTauEval :=
  evalTau precision tau1973 contact1973 logTwoBall

theorem center_sq1973 : (center1973.re : ℝ)^2 +
    (center1973.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1973]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1973 : work1973.theta.ok = true ∧
    work1973.jac.invOK = true ∧ acceptsUnitSq work1973.out = true := by
  norm_num [work1973, contact1973, tau1973, center1973, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1973 : CellCertificate where
  tauBall := tau1973
  contactCenter := center1973
  contactBall := contact1973
  work := work1973
  center_sq := center_sq1973
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1973.1
  jac_ok := checks1973.2.1
  accepted := checks1973.2.2

def tau1974 : RatBall :=
  ⟨⟨-73/320, 19/64⟩, 3/640⟩
def center1974 : GaussianRat :=
  ⟨-16950309/100000000, 199854009/1000000000⟩
def contact1974 : RatBall := localContactBall tau1974 center1974
def work1974 : RoundedTauEval :=
  evalTau precision tau1974 contact1974 logTwoBall

theorem center_sq1974 : (center1974.re : ℝ)^2 +
    (center1974.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1974]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1974 : work1974.theta.ok = true ∧
    work1974.jac.invOK = true ∧ acceptsUnitSq work1974.out = true := by
  norm_num [work1974, contact1974, tau1974, center1974, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1974 : CellCertificate where
  tauBall := tau1974
  contactCenter := center1974
  contactBall := contact1974
  work := work1974
  center_sq := center_sq1974
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1974.1
  jac_ok := checks1974.2.1
  accepted := checks1974.2.2

def tau1975 : RatBall :=
  ⟨⟨-71/320, 93/320⟩, 3/640⟩
def center1975 : GaussianRat :=
  ⟨-82231753/500000000, 98036117/500000000⟩
def contact1975 : RatBall := localContactBall tau1975 center1975
def work1975 : RoundedTauEval :=
  evalTau precision tau1975 contact1975 logTwoBall

theorem center_sq1975 : (center1975.re : ℝ)^2 +
    (center1975.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1975]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1975 : work1975.theta.ok = true ∧
    work1975.jac.invOK = true ∧ acceptsUnitSq work1975.out = true := by
  norm_num [work1975, contact1975, tau1975, center1975, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1975 : CellCertificate where
  tauBall := tau1975
  contactCenter := center1975
  contactBall := contact1975
  work := work1975
  center_sq := center_sq1975
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1975.1
  jac_ok := checks1975.2.1
  accepted := checks1975.2.2

def cells : List CellCertificate := [cell1968, cell1969, cell1970, cell1971, cell1972, cell1973, cell1974, cell1975]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246

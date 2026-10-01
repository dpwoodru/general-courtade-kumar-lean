import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1160 : RatBall :=
  ⟨⟨7/32, 37/160⟩, 3/320⟩
def center1160 : GaussianRat :=
  ⟨78611951/500000000, 154924327/1000000000⟩
def contact1160 : RatBall := localContactBall tau1160 center1160
def work1160 : RoundedTauEval :=
  evalTau precision tau1160 contact1160 logTwoBall

theorem center_sq1160 : (center1160.re : ℝ)^2 +
    (center1160.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1160]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1160 : work1160.theta.ok = true ∧
    work1160.jac.invOK = true ∧ acceptsUnitSq work1160.out = true := by
  norm_num [work1160, contact1160, tau1160, center1160, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1160 : CellCertificate where
  tauBall := tau1160
  contactCenter := center1160
  contactBall := contact1160
  work := work1160
  center_sq := center_sq1160
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1160.1
  jac_ok := checks1160.2.1
  accepted := checks1160.2.2

def tau1161 : RatBall :=
  ⟨⟨33/160, 39/160⟩, 3/320⟩
def center1161 : GaussianRat :=
  ⟨18684153/125000000, 164515579/1000000000⟩
def contact1161 : RatBall := localContactBall tau1161 center1161
def work1161 : RoundedTauEval :=
  evalTau precision tau1161 contact1161 logTwoBall

theorem center_sq1161 : (center1161.re : ℝ)^2 +
    (center1161.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1161]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1161 : work1161.theta.ok = true ∧
    work1161.jac.invOK = true ∧ acceptsUnitSq work1161.out = true := by
  norm_num [work1161, contact1161, tau1161, center1161, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1161 : CellCertificate where
  tauBall := tau1161
  contactCenter := center1161
  contactBall := contact1161
  work := work1161
  center_sq := center_sq1161
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1161.1
  jac_ok := checks1161.2.1
  accepted := checks1161.2.2

def tau1162 : RatBall :=
  ⟨⟨7/32, 39/160⟩, 3/320⟩
def center1162 : GaussianRat :=
  ⟨9885359/62500000, 81782823/500000000⟩
def contact1162 : RatBall := localContactBall tau1162 center1162
def work1162 : RoundedTauEval :=
  evalTau precision tau1162 contact1162 logTwoBall

theorem center_sq1162 : (center1162.re : ℝ)^2 +
    (center1162.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1162]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1162 : work1162.theta.ok = true ∧
    work1162.jac.invOK = true ∧ acceptsUnitSq work1162.out = true := by
  norm_num [work1162, contact1162, tau1162, center1162, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1162 : CellCertificate where
  tauBall := tau1162
  contactCenter := center1162
  contactBall := contact1162
  work := work1162
  center_sq := center_sq1162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1162.1
  jac_ok := checks1162.2.1
  accepted := checks1162.2.2

def tau1163 : RatBall :=
  ⟨⟨37/160, 37/160⟩, 3/320⟩
def center1163 : GaussianRat :=
  ⟨33162899/200000000, 153992113/1000000000⟩
def contact1163 : RatBall := localContactBall tau1163 center1163
def work1163 : RoundedTauEval :=
  evalTau precision tau1163 contact1163 logTwoBall

theorem center_sq1163 : (center1163.re : ℝ)^2 +
    (center1163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1163 : work1163.theta.ok = true ∧
    work1163.jac.invOK = true ∧ acceptsUnitSq work1163.out = true := by
  norm_num [work1163, contact1163, tau1163, center1163, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1163 : CellCertificate where
  tauBall := tau1163
  contactCenter := center1163
  contactBall := contact1163
  work := work1163
  center_sq := center_sq1163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1163.1
  jac_ok := checks1163.2.1
  accepted := checks1163.2.2

def tau1164 : RatBall :=
  ⟨⟨39/160, 37/160⟩, 3/320⟩
def center1164 : GaussianRat :=
  ⟨174343743/1000000000, 153020771/1000000000⟩
def contact1164 : RatBall := localContactBall tau1164 center1164
def work1164 : RoundedTauEval :=
  evalTau precision tau1164 contact1164 logTwoBall

theorem center_sq1164 : (center1164.re : ℝ)^2 +
    (center1164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1164 : work1164.theta.ok = true ∧
    work1164.jac.invOK = true ∧ acceptsUnitSq work1164.out = true := by
  norm_num [work1164, contact1164, tau1164, center1164, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1164 : CellCertificate where
  tauBall := tau1164
  contactCenter := center1164
  contactBall := contact1164
  work := work1164
  center_sq := center_sq1164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1164.1
  jac_ok := checks1164.2.1
  accepted := checks1164.2.2

def tau1165 : RatBall :=
  ⟨⟨37/160, 39/160⟩, 3/320⟩
def center1165 : GaussianRat :=
  ⟨83398769/500000000, 20321547/125000000⟩
def contact1165 : RatBall := localContactBall tau1165 center1165
def work1165 : RoundedTauEval :=
  evalTau precision tau1165 contact1165 logTwoBall

theorem center_sq1165 : (center1165.re : ℝ)^2 +
    (center1165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1165 : work1165.theta.ok = true ∧
    work1165.jac.invOK = true ∧ acceptsUnitSq work1165.out = true := by
  norm_num [work1165, contact1165, tau1165, center1165, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1165 : CellCertificate where
  tauBall := tau1165
  contactCenter := center1165
  contactBall := contact1165
  work := work1165
  center_sq := center_sq1165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1165.1
  jac_ok := checks1165.2.1
  accepted := checks1165.2.2

def tau1166 : RatBall :=
  ⟨⟨39/160, 39/160⟩, 3/320⟩
def center1166 : GaussianRat :=
  ⟨7014647/40000000, 32307527/200000000⟩
def contact1166 : RatBall := localContactBall tau1166 center1166
def work1166 : RoundedTauEval :=
  evalTau precision tau1166 contact1166 logTwoBall

theorem center_sq1166 : (center1166.re : ℝ)^2 +
    (center1166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1166 : work1166.theta.ok = true ∧
    work1166.jac.invOK = true ∧ acceptsUnitSq work1166.out = true := by
  norm_num [work1166, contact1166, tau1166, center1166, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1166 : CellCertificate where
  tauBall := tau1166
  contactCenter := center1166
  contactBall := contact1166
  work := work1166
  center_sq := center_sq1166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1166.1
  jac_ok := checks1166.2.1
  accepted := checks1166.2.2

def tau1167 : RatBall :=
  ⟨⟨41/160, 33/160⟩, 3/320⟩
def center1167 : GaussianRat :=
  ⟨180884951/1000000000, 135214257/1000000000⟩
def contact1167 : RatBall := localContactBall tau1167 center1167
def work1167 : RoundedTauEval :=
  evalTau precision tau1167 contact1167 logTwoBall

theorem center_sq1167 : (center1167.re : ℝ)^2 +
    (center1167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1167 : work1167.theta.ok = true ∧
    work1167.jac.invOK = true ∧ acceptsUnitSq work1167.out = true := by
  norm_num [work1167, contact1167, tau1167, center1167, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1167 : CellCertificate where
  tauBall := tau1167
  contactCenter := center1167
  contactBall := contact1167
  work := work1167
  center_sq := center_sq1167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1167.1
  jac_ok := checks1167.2.1
  accepted := checks1167.2.2

def cells : List CellCertificate := [cell1160, cell1161, cell1162, cell1163, cell1164, cell1165, cell1166, cell1167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145

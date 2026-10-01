import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0253

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2024 : RatBall :=
  ⟨⟨-13/64, 21/64⟩, 3/640⟩
def center2024 : GaussianRat :=
  ⟨-30978099/200000000, 224898511/1000000000⟩
def contact2024 : RatBall := localContactBall tau2024 center2024
def work2024 : RoundedTauEval :=
  evalTau precision tau2024 contact2024 logTwoBall

theorem center_sq2024 : (center2024.re : ℝ)^2 +
    (center2024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2024 : work2024.theta.ok = true ∧
    work2024.jac.invOK = true ∧ acceptsUnitSq work2024.out = true := by
  norm_num [work2024, contact2024, tau2024, center2024, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2024 : CellCertificate where
  tauBall := tau2024
  contactCenter := center2024
  contactBall := contact2024
  work := work2024
  center_sq := center_sq2024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2024.1
  jac_ok := checks2024.2.1
  accepted := checks2024.2.2

def tau2025 : RatBall :=
  ⟨⟨-67/320, 107/320⟩, 3/640⟩
def center2025 : GaussianRat :=
  ⟨-160137389/1000000000, 228757569/1000000000⟩
def contact2025 : RatBall := localContactBall tau2025 center2025
def work2025 : RoundedTauEval :=
  evalTau precision tau2025 contact2025 logTwoBall

theorem center_sq2025 : (center2025.re : ℝ)^2 +
    (center2025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2025 : work2025.theta.ok = true ∧
    work2025.jac.invOK = true ∧ acceptsUnitSq work2025.out = true := by
  norm_num [work2025, contact2025, tau2025, center2025, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2025 : CellCertificate where
  tauBall := tau2025
  contactCenter := center2025
  contactBall := contact2025
  work := work2025
  center_sq := center_sq2025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2025.1
  jac_ok := checks2025.2.1
  accepted := checks2025.2.2

def tau2026 : RatBall :=
  ⟨⟨-13/64, 107/320⟩, 3/640⟩
def center2026 : GaussianRat :=
  ⟨-77788111/500000000, 229460827/1000000000⟩
def contact2026 : RatBall := localContactBall tau2026 center2026
def work2026 : RoundedTauEval :=
  evalTau precision tau2026 contact2026 logTwoBall

theorem center_sq2026 : (center2026.re : ℝ)^2 +
    (center2026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2026 : work2026.theta.ok = true ∧
    work2026.jac.invOK = true ∧ acceptsUnitSq work2026.out = true := by
  norm_num [work2026, contact2026, tau2026, center2026, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2026 : CellCertificate where
  tauBall := tau2026
  contactCenter := center2026
  contactBall := contact2026
  work := work2026
  center_sq := center_sq2026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2026.1
  jac_ok := checks2026.2.1
  accepted := checks2026.2.2

def tau2027 : RatBall :=
  ⟨⟨-63/320, 97/320⟩, 3/640⟩
def center2027 : GaussianRat :=
  ⟨-147826489/1000000000, 2592583/12500000⟩
def contact2027 : RatBall := localContactBall tau2027 center2027
def work2027 : RoundedTauEval :=
  evalTau precision tau2027 contact2027 logTwoBall

theorem center_sq2027 : (center2027.re : ℝ)^2 +
    (center2027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2027 : work2027.theta.ok = true ∧
    work2027.jac.invOK = true ∧ acceptsUnitSq work2027.out = true := by
  norm_num [work2027, contact2027, tau2027, center2027, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2027 : CellCertificate where
  tauBall := tau2027
  contactCenter := center2027
  contactBall := contact2027
  work := work2027
  center_sq := center_sq2027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2027.1
  jac_ok := checks2027.2.1
  accepted := checks2027.2.2

def tau2028 : RatBall :=
  ⟨⟨-61/320, 97/320⟩, 3/640⟩
def center2028 : GaussianRat :=
  ⟨-143309371/1000000000, 103995141/500000000⟩
def contact2028 : RatBall := localContactBall tau2028 center2028
def work2028 : RoundedTauEval :=
  evalTau precision tau2028 contact2028 logTwoBall

theorem center_sq2028 : (center2028.re : ℝ)^2 +
    (center2028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2028 : work2028.theta.ok = true ∧
    work2028.jac.invOK = true ∧ acceptsUnitSq work2028.out = true := by
  norm_num [work2028, contact2028, tau2028, center2028, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2028 : CellCertificate where
  tauBall := tau2028
  contactCenter := center2028
  contactBall := contact2028
  work := work2028
  center_sq := center_sq2028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2028.1
  jac_ok := checks2028.2.1
  accepted := checks2028.2.2

def tau2029 : RatBall :=
  ⟨⟨-63/320, 99/320⟩, 3/640⟩
def center2029 : GaussianRat :=
  ⟨-148426041/1000000000, 105961569/500000000⟩
def contact2029 : RatBall := localContactBall tau2029 center2029
def work2029 : RoundedTauEval :=
  evalTau precision tau2029 contact2029 logTwoBall

theorem center_sq2029 : (center2029.re : ℝ)^2 +
    (center2029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2029 : work2029.theta.ok = true ∧
    work2029.jac.invOK = true ∧ acceptsUnitSq work2029.out = true := by
  norm_num [work2029, contact2029, tau2029, center2029, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2029 : CellCertificate where
  tauBall := tau2029
  contactCenter := center2029
  contactBall := contact2029
  work := work2029
  center_sq := center_sq2029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2029.1
  jac_ok := checks2029.2.1
  accepted := checks2029.2.2

def tau2030 : RatBall :=
  ⟨⟨-61/320, 99/320⟩, 3/640⟩
def center2030 : GaussianRat :=
  ⟨-28778703/200000000, 106261649/500000000⟩
def contact2030 : RatBall := localContactBall tau2030 center2030
def work2030 : RoundedTauEval :=
  evalTau precision tau2030 contact2030 logTwoBall

theorem center_sq2030 : (center2030.re : ℝ)^2 +
    (center2030.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2030]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2030 : work2030.theta.ok = true ∧
    work2030.jac.invOK = true ∧ acceptsUnitSq work2030.out = true := by
  norm_num [work2030, contact2030, tau2030, center2030, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2030 : CellCertificate where
  tauBall := tau2030
  contactCenter := center2030
  contactBall := contact2030
  work := work2030
  center_sq := center_sq2030
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2030.1
  jac_ok := checks2030.2.1
  accepted := checks2030.2.2

def tau2031 : RatBall :=
  ⟨⟨-59/320, 97/320⟩, 3/640⟩
def center2031 : GaussianRat :=
  ⟨-13877609/100000000, 208558553/1000000000⟩
def contact2031 : RatBall := localContactBall tau2031 center2031
def work2031 : RoundedTauEval :=
  evalTau precision tau2031 contact2031 logTwoBall

theorem center_sq2031 : (center2031.re : ℝ)^2 +
    (center2031.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2031]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2031 : work2031.theta.ok = true ∧
    work2031.jac.invOK = true ∧ acceptsUnitSq work2031.out = true := by
  norm_num [work2031, contact2031, tau2031, center2031, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2031 : CellCertificate where
  tauBall := tau2031
  contactCenter := center2031
  contactBall := contact2031
  work := work2031
  center_sq := center_sq2031
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2031.1
  jac_ok := checks2031.2.1
  accepted := checks2031.2.2

def cells : List CellCertificate := [cell2024, cell2025, cell2026, cell2027, cell2028, cell2029, cell2030, cell2031]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0253

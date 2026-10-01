import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2096 : RatBall :=
  ⟨⟨-9/64, 111/320⟩, 3/640⟩
def center2096 : GaussianRat :=
  ⟨-4402271/40000000, 122514671/500000000⟩
def contact2096 : RatBall := localContactBall tau2096 center2096
def work2096 : RoundedTauEval :=
  evalTau precision tau2096 contact2096 logTwoBall

theorem center_sq2096 : (center2096.re : ℝ)^2 +
    (center2096.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2096]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2096 : work2096.theta.ok = true ∧
    work2096.jac.invOK = true ∧ acceptsUnitSq work2096.out = true := by
  norm_num [work2096, contact2096, tau2096, center2096, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2096 : CellCertificate where
  tauBall := tau2096
  contactCenter := center2096
  contactBall := contact2096
  work := work2096
  center_sq := center_sq2096
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2096.1
  jac_ok := checks2096.2.1
  accepted := checks2096.2.2

def tau2097 : RatBall :=
  ⟨⟨-43/320, 109/320⟩, 3/640⟩
def center2097 : GaussianRat :=
  ⟨-26190451/250000000, 3762143/15625000⟩
def contact2097 : RatBall := localContactBall tau2097 center2097
def work2097 : RoundedTauEval :=
  evalTau precision tau2097 contact2097 logTwoBall

theorem center_sq2097 : (center2097.re : ℝ)^2 +
    (center2097.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2097]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2097 : work2097.theta.ok = true ∧
    work2097.jac.invOK = true ∧ acceptsUnitSq work2097.out = true := by
  norm_num [work2097, contact2097, tau2097, center2097, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2097 : CellCertificate where
  tauBall := tau2097
  contactCenter := center2097
  contactBall := contact2097
  work := work2097
  center_sq := center_sq2097
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2097.1
  jac_ok := checks2097.2.1
  accepted := checks2097.2.2

def tau2098 : RatBall :=
  ⟨⟨-41/320, 109/320⟩, 3/640⟩
def center2098 : GaussianRat :=
  ⟨-6249053/62500000, 241270351/1000000000⟩
def contact2098 : RatBall := localContactBall tau2098 center2098
def work2098 : RoundedTauEval :=
  evalTau precision tau2098 contact2098 logTwoBall

theorem center_sq2098 : (center2098.re : ℝ)^2 +
    (center2098.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2098]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2098 : work2098.theta.ok = true ∧
    work2098.jac.invOK = true ∧ acceptsUnitSq work2098.out = true := by
  norm_num [work2098, contact2098, tau2098, center2098, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2098 : CellCertificate where
  tauBall := tau2098
  contactCenter := center2098
  contactBall := contact2098
  work := work2098
  center_sq := center_sq2098
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2098.1
  jac_ok := checks2098.2.1
  accepted := checks2098.2.2

def tau2099 : RatBall :=
  ⟨⟨-43/320, 111/320⟩, 3/640⟩
def center2099 : GaussianRat :=
  ⟨-21054511/200000000, 122778933/500000000⟩
def contact2099 : RatBall := localContactBall tau2099 center2099
def work2099 : RoundedTauEval :=
  evalTau precision tau2099 contact2099 logTwoBall

theorem center_sq2099 : (center2099.re : ℝ)^2 +
    (center2099.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2099]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2099 : work2099.theta.ok = true ∧
    work2099.jac.invOK = true ∧ acceptsUnitSq work2099.out = true := by
  norm_num [work2099, contact2099, tau2099, center2099, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2099 : CellCertificate where
  tauBall := tau2099
  contactCenter := center2099
  contactBall := contact2099
  work := work2099
  center_sq := center_sq2099
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2099.1
  jac_ok := checks2099.2.1
  accepted := checks2099.2.2

def tau2100 : RatBall :=
  ⟨⟨-41/320, 111/320⟩, 3/640⟩
def center2100 : GaussianRat :=
  ⟨-100474143/1000000000, 123032409/500000000⟩
def contact2100 : RatBall := localContactBall tau2100 center2100
def work2100 : RoundedTauEval :=
  evalTau precision tau2100 contact2100 logTwoBall

theorem center_sq2100 : (center2100.re : ℝ)^2 +
    (center2100.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2100]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2100 : work2100.theta.ok = true ∧
    work2100.jac.invOK = true ∧ acceptsUnitSq work2100.out = true := by
  norm_num [work2100, contact2100, tau2100, center2100, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2100 : CellCertificate where
  tauBall := tau2100
  contactCenter := center2100
  contactBall := contact2100
  work := work2100
  center_sq := center_sq2100
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2100.1
  jac_ok := checks2100.2.1
  accepted := checks2100.2.2

def tau2101 : RatBall :=
  ⟨⟨-39/320, 21/64⟩, 3/640⟩
def center2101 : GaussianRat :=
  ⟨-94297493/1000000000, 185753/800000⟩
def contact2101 : RatBall := localContactBall tau2101 center2101
def work2101 : RoundedTauEval :=
  evalTau precision tau2101 contact2101 logTwoBall

theorem center_sq2101 : (center2101.re : ℝ)^2 +
    (center2101.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2101]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2101 : work2101.theta.ok = true ∧
    work2101.jac.invOK = true ∧ acceptsUnitSq work2101.out = true := by
  norm_num [work2101, contact2101, tau2101, center2101, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2101 : CellCertificate where
  tauBall := tau2101
  contactCenter := center2101
  contactBall := contact2101
  work := work2101
  center_sq := center_sq2101
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2101.1
  jac_ok := checks2101.2.1
  accepted := checks2101.2.2

def tau2102 : RatBall :=
  ⟨⟨-37/320, 21/64⟩, 3/640⟩
def center2102 : GaussianRat :=
  ⟨-89536891/1000000000, 116308561/500000000⟩
def contact2102 : RatBall := localContactBall tau2102 center2102
def work2102 : RoundedTauEval :=
  evalTau precision tau2102 contact2102 logTwoBall

theorem center_sq2102 : (center2102.re : ℝ)^2 +
    (center2102.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2102]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2102 : work2102.theta.ok = true ∧
    work2102.jac.invOK = true ∧ acceptsUnitSq work2102.out = true := by
  norm_num [work2102, contact2102, tau2102, center2102, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2102 : CellCertificate where
  tauBall := tau2102
  contactCenter := center2102
  contactBall := contact2102
  work := work2102
  center_sq := center_sq2102
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2102.1
  jac_ok := checks2102.2.1
  accepted := checks2102.2.2

def tau2103 : RatBall :=
  ⟨⟨-39/320, 107/320⟩, 3/640⟩
def center2103 : GaussianRat :=
  ⟨-23684951/250000000, 1184781/5000000⟩
def contact2103 : RatBall := localContactBall tau2103 center2103
def work2103 : RoundedTauEval :=
  evalTau precision tau2103 contact2103 logTwoBall

theorem center_sq2103 : (center2103.re : ℝ)^2 +
    (center2103.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2103]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2103 : work2103.theta.ok = true ∧
    work2103.jac.invOK = true ∧ acceptsUnitSq work2103.out = true := by
  norm_num [work2103, contact2103, tau2103, center2103, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2103 : CellCertificate where
  tauBall := tau2103
  contactCenter := center2103
  contactBall := contact2103
  work := work2103
  center_sq := center_sq2103
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2103.1
  jac_ok := checks2103.2.1
  accepted := checks2103.2.2

def cells : List CellCertificate := [cell2096, cell2097, cell2098, cell2099, cell2100, cell2101, cell2102, cell2103]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262

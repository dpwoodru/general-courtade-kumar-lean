import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2144 : RatBall :=
  ⟨⟨-21/320, 109/320⟩, 3/640⟩
def center2144 : GaussianRat :=
  ⟨-51579953/1000000000, 48996707/200000000⟩
def contact2144 : RatBall := localContactBall tau2144 center2144
def work2144 : RoundedTauEval :=
  evalTau precision tau2144 contact2144 logTwoBall

theorem center_sq2144 : (center2144.re : ℝ)^2 +
    (center2144.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2144]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2144 : work2144.theta.ok = true ∧
    work2144.jac.invOK = true ∧ acceptsUnitSq work2144.out = true := by
  norm_num [work2144, contact2144, tau2144, center2144, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2144 : CellCertificate where
  tauBall := tau2144
  contactCenter := center2144
  contactBall := contact2144
  work := work2144
  center_sq := center_sq2144
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2144.1
  jac_ok := checks2144.2.1
  accepted := checks2144.2.2

def tau2145 : RatBall :=
  ⟨⟨-23/320, 111/320⟩, 3/640⟩
def center2145 : GaussianRat :=
  ⟨-11349381/200000000, 62401781/250000000⟩
def contact2145 : RatBall := localContactBall tau2145 center2145
def work2145 : RoundedTauEval :=
  evalTau precision tau2145 contact2145 logTwoBall

theorem center_sq2145 : (center2145.re : ℝ)^2 +
    (center2145.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2145]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2145 : work2145.theta.ok = true ∧
    work2145.jac.invOK = true ∧ acceptsUnitSq work2145.out = true := by
  norm_num [work2145, contact2145, tau2145, center2145, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2145 : CellCertificate where
  tauBall := tau2145
  contactCenter := center2145
  contactBall := contact2145
  work := work2145
  center_sq := center_sq2145
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2145.1
  jac_ok := checks2145.2.1
  accepted := checks2145.2.2

def tau2146 : RatBall :=
  ⟨⟨-21/320, 111/320⟩, 3/640⟩
def center2146 : GaussianRat :=
  ⟨-51839561/1000000000, 31235321/125000000⟩
def contact2146 : RatBall := localContactBall tau2146 center2146
def work2146 : RoundedTauEval :=
  evalTau precision tau2146 contact2146 logTwoBall

theorem center_sq2146 : (center2146.re : ℝ)^2 +
    (center2146.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2146]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2146 : work2146.theta.ok = true ∧
    work2146.jac.invOK = true ∧ acceptsUnitSq work2146.out = true := by
  norm_num [work2146, contact2146, tau2146, center2146, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2146 : CellCertificate where
  tauBall := tau2146
  contactCenter := center2146
  contactBall := contact2146
  work := work2146
  center_sq := center_sq2146
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2146.1
  jac_ok := checks2146.2.1
  accepted := checks2146.2.2

def tau2147 : RatBall :=
  ⟨⟨-31/320, 113/320⟩, 3/640⟩
def center2147 : GaussianRat :=
  ⟨-15335517/200000000, 253142899/1000000000⟩
def contact2147 : RatBall := localContactBall tau2147 center2147
def work2147 : RoundedTauEval :=
  evalTau precision tau2147 contact2147 logTwoBall

theorem center_sq2147 : (center2147.re : ℝ)^2 +
    (center2147.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2147]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2147 : work2147.theta.ok = true ∧
    work2147.jac.invOK = true ∧ acceptsUnitSq work2147.out = true := by
  norm_num [work2147, contact2147, tau2147, center2147, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2147 : CellCertificate where
  tauBall := tau2147
  contactCenter := center2147
  contactBall := contact2147
  work := work2147
  center_sq := center_sq2147
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2147.1
  jac_ok := checks2147.2.1
  accepted := checks2147.2.2

def tau2148 : RatBall :=
  ⟨⟨-29/320, 113/320⟩, 3/640⟩
def center2148 : GaussianRat :=
  ⟨-1794563/25000000, 253524459/1000000000⟩
def contact2148 : RatBall := localContactBall tau2148 center2148
def work2148 : RoundedTauEval :=
  evalTau precision tau2148 contact2148 logTwoBall

theorem center_sq2148 : (center2148.re : ℝ)^2 +
    (center2148.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2148]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2148 : work2148.theta.ok = true ∧
    work2148.jac.invOK = true ∧ acceptsUnitSq work2148.out = true := by
  norm_num [work2148, contact2148, tau2148, center2148, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2148 : CellCertificate where
  tauBall := tau2148
  contactCenter := center2148
  contactBall := contact2148
  work := work2148
  center_sq := center_sq2148
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2148.1
  jac_ok := checks2148.2.1
  accepted := checks2148.2.2

def tau2149 : RatBall :=
  ⟨⟨-31/320, 23/64⟩, 3/640⟩
def center2149 : GaussianRat :=
  ⟨-77076663/1000000000, 258044723/1000000000⟩
def contact2149 : RatBall := localContactBall tau2149 center2149
def work2149 : RoundedTauEval :=
  evalTau precision tau2149 contact2149 logTwoBall

theorem center_sq2149 : (center2149.re : ℝ)^2 +
    (center2149.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2149]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2149 : work2149.theta.ok = true ∧
    work2149.jac.invOK = true ∧ acceptsUnitSq work2149.out = true := by
  norm_num [work2149, contact2149, tau2149, center2149, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2149 : CellCertificate where
  tauBall := tau2149
  contactCenter := center2149
  contactBall := contact2149
  work := work2149
  center_sq := center_sq2149
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2149.1
  jac_ok := checks2149.2.1
  accepted := checks2149.2.2

def tau2150 : RatBall :=
  ⟨⟨-29/320, 23/64⟩, 3/640⟩
def center2150 : GaussianRat :=
  ⟨-4509823/62500000, 258436977/1000000000⟩
def contact2150 : RatBall := localContactBall tau2150 center2150
def work2150 : RoundedTauEval :=
  evalTau precision tau2150 contact2150 logTwoBall

theorem center_sq2150 : (center2150.re : ℝ)^2 +
    (center2150.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2150]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2150 : work2150.theta.ok = true ∧
    work2150.jac.invOK = true ∧ acceptsUnitSq work2150.out = true := by
  norm_num [work2150, contact2150, tau2150, center2150, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2150 : CellCertificate where
  tauBall := tau2150
  contactCenter := center2150
  contactBall := contact2150
  work := work2150
  center_sq := center_sq2150
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2150.1
  jac_ok := checks2150.2.1
  accepted := checks2150.2.2

def tau2151 : RatBall :=
  ⟨⟨-27/320, 113/320⟩, 3/640⟩
def center2151 : GaussianRat :=
  ⟨-33438609/500000000, 253881789/1000000000⟩
def contact2151 : RatBall := localContactBall tau2151 center2151
def work2151 : RoundedTauEval :=
  evalTau precision tau2151 contact2151 logTwoBall

theorem center_sq2151 : (center2151.re : ℝ)^2 +
    (center2151.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2151]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2151 : work2151.theta.ok = true ∧
    work2151.jac.invOK = true ∧ acceptsUnitSq work2151.out = true := by
  norm_num [work2151, contact2151, tau2151, center2151, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2151 : CellCertificate where
  tauBall := tau2151
  contactCenter := center2151
  contactBall := contact2151
  work := work2151
  center_sq := center_sq2151
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2151.1
  jac_ok := checks2151.2.1
  accepted := checks2151.2.2

def cells : List CellCertificate := [cell2144, cell2145, cell2146, cell2147, cell2148, cell2149, cell2150, cell2151]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268

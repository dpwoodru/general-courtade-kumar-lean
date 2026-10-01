import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2896 : RatBall :=
  ⟨⟨1/128, -251/640⟩, 3/1280⟩
def center2896 : GaussianRat :=
  ⟨3221293/500000000, -287852971/1000000000⟩
def contact2896 : RatBall := localContactBall tau2896 center2896
def work2896 : RoundedTauEval :=
  evalTau precision tau2896 contact2896 logTwoBall

theorem center_sq2896 : (center2896.re : ℝ)^2 +
    (center2896.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2896]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2896 : work2896.theta.ok = true ∧
    work2896.jac.invOK = true ∧ acceptsUnitSq work2896.out = true := by
  norm_num [work2896, contact2896, tau2896, center2896, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2896 : CellCertificate where
  tauBall := tau2896
  contactCenter := center2896
  contactBall := contact2896
  work := work2896
  center_sq := center_sq2896
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2896.1
  jac_ok := checks2896.2.1
  accepted := checks2896.2.2

def tau2897 : RatBall :=
  ⟨⟨7/640, -251/640⟩, 3/1280⟩
def center2897 : GaussianRat :=
  ⟨9019241/1000000000, -287829653/1000000000⟩
def contact2897 : RatBall := localContactBall tau2897 center2897
def work2897 : RoundedTauEval :=
  evalTau precision tau2897 contact2897 logTwoBall

theorem center_sq2897 : (center2897.re : ℝ)^2 +
    (center2897.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2897]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2897 : work2897.theta.ok = true ∧
    work2897.jac.invOK = true ∧ acceptsUnitSq work2897.out = true := by
  norm_num [work2897, contact2897, tau2897, center2897, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2897 : CellCertificate where
  tauBall := tau2897
  contactCenter := center2897
  contactBall := contact2897
  work := work2897
  center_sq := center_sq2897
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2897.1
  jac_ok := checks2897.2.1
  accepted := checks2897.2.2

def tau2898 : RatBall :=
  ⟨⟨1/128, -249/640⟩, 3/1280⟩
def center2898 : GaussianRat :=
  ⟨6423287/1000000000, -285280029/1000000000⟩
def contact2898 : RatBall := localContactBall tau2898 center2898
def work2898 : RoundedTauEval :=
  evalTau precision tau2898 contact2898 logTwoBall

theorem center_sq2898 : (center2898.re : ℝ)^2 +
    (center2898.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2898]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2898 : work2898.theta.ok = true ∧
    work2898.jac.invOK = true ∧ acceptsUnitSq work2898.out = true := by
  norm_num [work2898, contact2898, tau2898, center2898, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2898 : CellCertificate where
  tauBall := tau2898
  contactCenter := center2898
  contactBall := contact2898
  work := work2898
  center_sq := center_sq2898
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2898.1
  jac_ok := checks2898.2.1
  accepted := checks2898.2.2

def tau2899 : RatBall :=
  ⟨⟨7/640, -249/640⟩, 3/1280⟩
def center2899 : GaussianRat :=
  ⟨2248057/250000000, -142628517/500000000⟩
def contact2899 : RatBall := localContactBall tau2899 center2899
def work2899 : RoundedTauEval :=
  evalTau precision tau2899 contact2899 logTwoBall

theorem center_sq2899 : (center2899.re : ℝ)^2 +
    (center2899.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2899]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2899 : work2899.theta.ok = true ∧
    work2899.jac.invOK = true ∧ acceptsUnitSq work2899.out = true := by
  norm_num [work2899, contact2899, tau2899, center2899, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2899 : CellCertificate where
  tauBall := tau2899
  contactCenter := center2899
  contactBall := contact2899
  work := work2899
  center_sq := center_sq2899
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2899.1
  jac_ok := checks2899.2.1
  accepted := checks2899.2.2

def tau2900 : RatBall :=
  ⟨⟨9/640, -51/128⟩, 3/1280⟩
def center2900 : GaussianRat :=
  ⟨11666429/1000000000, -4577599/15625000⟩
def contact2900 : RatBall := localContactBall tau2900 center2900
def work2900 : RoundedTauEval :=
  evalTau precision tau2900 contact2900 logTwoBall

theorem center_sq2900 : (center2900.re : ℝ)^2 +
    (center2900.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2900]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2900 : work2900.theta.ok = true ∧
    work2900.jac.invOK = true ∧ acceptsUnitSq work2900.out = true := by
  norm_num [work2900, contact2900, tau2900, center2900, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2900 : CellCertificate where
  tauBall := tau2900
  contactCenter := center2900
  contactBall := contact2900
  work := work2900
  center_sq := center_sq2900
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2900.1
  jac_ok := checks2900.2.1
  accepted := checks2900.2.2

def tau2901 : RatBall :=
  ⟨⟨11/640, -51/128⟩, 3/1280⟩
def center2901 : GaussianRat :=
  ⟨3564487/250000000, -73231599/250000000⟩
def contact2901 : RatBall := localContactBall tau2901 center2901
def work2901 : RoundedTauEval :=
  evalTau precision tau2901 contact2901 logTwoBall

theorem center_sq2901 : (center2901.re : ℝ)^2 +
    (center2901.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2901]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2901 : work2901.theta.ok = true ∧
    work2901.jac.invOK = true ∧ acceptsUnitSq work2901.out = true := by
  norm_num [work2901, contact2901, tau2901, center2901, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2901 : CellCertificate where
  tauBall := tau2901
  contactCenter := center2901
  contactBall := contact2901
  work := work2901
  center_sq := center_sq2901
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2901.1
  jac_ok := checks2901.2.1
  accepted := checks2901.2.2

def tau2902 : RatBall :=
  ⟨⟨9/640, -253/640⟩, 3/1280⟩
def center2902 : GaussianRat :=
  ⟨5815363/500000000, -145189259/500000000⟩
def contact2902 : RatBall := localContactBall tau2902 center2902
def work2902 : RoundedTauEval :=
  evalTau precision tau2902 contact2902 logTwoBall

theorem center_sq2902 : (center2902.re : ℝ)^2 +
    (center2902.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2902]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2902 : work2902.theta.ok = true ∧
    work2902.jac.invOK = true ∧ acceptsUnitSq work2902.out = true := by
  norm_num [work2902, contact2902, tau2902, center2902, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2902 : CellCertificate where
  tauBall := tau2902
  contactCenter := center2902
  contactBall := contact2902
  work := work2902
  center_sq := center_sq2902
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2902.1
  jac_ok := checks2902.2.1
  accepted := checks2902.2.2

def tau2903 : RatBall :=
  ⟨⟨11/640, -253/640⟩, 3/1280⟩
def center2903 : GaussianRat :=
  ⟨7107163/500000000, -290339131/1000000000⟩
def contact2903 : RatBall := localContactBall tau2903 center2903
def work2903 : RoundedTauEval :=
  evalTau precision tau2903 contact2903 logTwoBall

theorem center_sq2903 : (center2903.re : ℝ)^2 +
    (center2903.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2903]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2903 : work2903.theta.ok = true ∧
    work2903.jac.invOK = true ∧ acceptsUnitSq work2903.out = true := by
  norm_num [work2903, contact2903, tau2903, center2903, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell2903 : CellCertificate where
  tauBall := tau2903
  contactCenter := center2903
  contactBall := contact2903
  work := work2903
  center_sq := center_sq2903
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2903.1
  jac_ok := checks2903.2.1
  accepted := checks2903.2.2

def cells : List CellCertificate := [cell2896, cell2897, cell2898, cell2899, cell2900, cell2901, cell2902, cell2903]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362

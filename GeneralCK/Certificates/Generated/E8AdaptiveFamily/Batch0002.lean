import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0016 : RatBall :=
  ⟨⟨1/8, -1/8⟩, 3/80⟩
def center0016 : GaussianRat :=
  ⟨87563403/1000000000, -85687457/1000000000⟩
def contact0016 : RatBall := localContactBall tau0016 center0016
def work0016 : RoundedTauEval :=
  evalTau precision tau0016 contact0016 logTwoBall

theorem center_sq0016 : (center0016.re : ℝ)^2 +
    (center0016.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0016]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0016 : work0016.theta.ok = true ∧
    work0016.jac.invOK = true ∧ acceptsUnitSq work0016.out = true := by
  norm_num [work0016, contact0016, tau0016, center0016, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0016 : CellCertificate where
  tauBall := tau0016
  contactCenter := center0016
  contactBall := contact0016
  work := work0016
  center_sq := center_sq0016
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0016.1
  jac_ok := checks0016.2.1
  accepted := checks0016.2.2

def tau0017 : RatBall :=
  ⟨⟨1/40, -3/40⟩, 3/80⟩
def center0017 : GaussianRat :=
  ⟨2178341/125000000, -3253349/62500000⟩
def contact0017 : RatBall := localContactBall tau0017 center0017
def work0017 : RoundedTauEval :=
  evalTau precision tau0017 contact0017 logTwoBall

theorem center_sq0017 : (center0017.re : ℝ)^2 +
    (center0017.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0017]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0017 : work0017.theta.ok = true ∧
    work0017.jac.invOK = true ∧ acceptsUnitSq work0017.out = true := by
  norm_num [work0017, contact0017, tau0017, center0017, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0017 : CellCertificate where
  tauBall := tau0017
  contactCenter := center0017
  contactBall := contact0017
  work := work0017
  center_sq := center_sq0017
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0017.1
  jac_ok := checks0017.2.1
  accepted := checks0017.2.2

def tau0018 : RatBall :=
  ⟨⟨3/40, -3/40⟩, 3/80⟩
def center0018 : GaussianRat :=
  ⟨1304683/25000000, -51781961/1000000000⟩
def contact0018 : RatBall := localContactBall tau0018 center0018
def work0018 : RoundedTauEval :=
  evalTau precision tau0018 contact0018 logTwoBall

theorem center_sq0018 : (center0018.re : ℝ)^2 +
    (center0018.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0018]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0018 : work0018.theta.ok = true ∧
    work0018.jac.invOK = true ∧ acceptsUnitSq work0018.out = true := by
  norm_num [work0018, contact0018, tau0018, center0018, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0018 : CellCertificate where
  tauBall := tau0018
  contactCenter := center0018
  contactBall := contact0018
  work := work0018
  center_sq := center_sq0018
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0018.1
  jac_ok := checks0018.2.1
  accepted := checks0018.2.2

def tau0019 : RatBall :=
  ⟨⟨1/40, -1/40⟩, 3/80⟩
def center0019 : GaussianRat :=
  ⟨17336181/1000000000, -17321167/1000000000⟩
def contact0019 : RatBall := localContactBall tau0019 center0019
def work0019 : RoundedTauEval :=
  evalTau precision tau0019 contact0019 logTwoBall

theorem center_sq0019 : (center0019.re : ℝ)^2 +
    (center0019.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0019]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0019 : work0019.theta.ok = true ∧
    work0019.jac.invOK = true ∧ acceptsUnitSq work0019.out = true := by
  norm_num [work0019, contact0019, tau0019, center0019, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0019 : CellCertificate where
  tauBall := tau0019
  contactCenter := center0019
  contactBall := contact0019
  work := work0019
  center_sq := center_sq0019
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0019.1
  jac_ok := checks0019.2.1
  accepted := checks0019.2.2

def tau0020 : RatBall :=
  ⟨⟨3/40, -1/40⟩, 3/80⟩
def center0020 : GaussianRat :=
  ⟨51918459/1000000000, -861577/50000000⟩
def contact0020 : RatBall := localContactBall tau0020 center0020
def work0020 : RoundedTauEval :=
  evalTau precision tau0020 contact0020 logTwoBall

theorem center_sq0020 : (center0020.re : ℝ)^2 +
    (center0020.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0020]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0020 : work0020.theta.ok = true ∧
    work0020.jac.invOK = true ∧ acceptsUnitSq work0020.out = true := by
  norm_num [work0020, contact0020, tau0020, center0020, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0020 : CellCertificate where
  tauBall := tau0020
  contactCenter := center0020
  contactBall := contact0020
  work := work0020
  center_sq := center_sq0020
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0020.1
  jac_ok := checks0020.2.1
  accepted := checks0020.2.2

def tau0021 : RatBall :=
  ⟨⟨1/8, -3/40⟩, 3/80⟩
def center0021 : GaussianRat :=
  ⟨86672281/1000000000, -1024941/20000000⟩
def contact0021 : RatBall := localContactBall tau0021 center0021
def work0021 : RoundedTauEval :=
  evalTau precision tau0021 contact0021 logTwoBall

theorem center_sq0021 : (center0021.re : ℝ)^2 +
    (center0021.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0021]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0021 : work0021.theta.ok = true ∧
    work0021.jac.invOK = true ∧ acceptsUnitSq work0021.out = true := by
  norm_num [work0021, contact0021, tau0021, center0021, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0021 : CellCertificate where
  tauBall := tau0021
  contactCenter := center0021
  contactBall := contact0021
  work := work0021
  center_sq := center_sq0021
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0021.1
  jac_ok := checks0021.2.1
  accepted := checks0021.2.2

def tau0022 : RatBall :=
  ⟨⟨7/40, -3/40⟩, 3/80⟩
def center0022 : GaussianRat :=
  ⟨7544217/62500000, -12616221/250000000⟩
def contact0022 : RatBall := localContactBall tau0022 center0022
def work0022 : RoundedTauEval :=
  evalTau precision tau0022 contact0022 logTwoBall

theorem center_sq0022 : (center0022.re : ℝ)^2 +
    (center0022.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0022]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0022 : work0022.theta.ok = true ∧
    work0022.jac.invOK = true ∧ acceptsUnitSq work0022.out = true := by
  norm_num [work0022, contact0022, tau0022, center0022, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0022 : CellCertificate where
  tauBall := tau0022
  contactCenter := center0022
  contactBall := contact0022
  work := work0022
  center_sq := center_sq0022
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0022.1
  jac_ok := checks0022.2.1
  accepted := checks0022.2.2

def tau0023 : RatBall :=
  ⟨⟨1/8, -1/40⟩, 3/80⟩
def center0023 : GaussianRat :=
  ⟨8623323/100000000, -17054997/1000000000⟩
def contact0023 : RatBall := localContactBall tau0023 center0023
def work0023 : RoundedTauEval :=
  evalTau precision tau0023 contact0023 logTwoBall

theorem center_sq0023 : (center0023.re : ℝ)^2 +
    (center0023.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0023 : work0023.theta.ok = true ∧
    work0023.jac.invOK = true ∧ acceptsUnitSq work0023.out = true := by
  norm_num [work0023, contact0023, tau0023, center0023, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0023 : CellCertificate where
  tauBall := tau0023
  contactCenter := center0023
  contactBall := contact0023
  work := work0023
  center_sq := center_sq0023
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0023.1
  jac_ok := checks0023.2.1
  accepted := checks0023.2.2

def cells : List CellCertificate := [cell0016, cell0017, cell0018, cell0019, cell0020, cell0021, cell0022, cell0023]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0002

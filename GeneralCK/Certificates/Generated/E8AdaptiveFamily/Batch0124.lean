import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0992 : RatBall :=
  ⟨⟨61/160, 11/160⟩, 3/320⟩
def center0992 : GaussianRat :=
  ⟨25301093/100000000, 41411583/1000000000⟩
def contact0992 : RatBall := localContactBall tau0992 center0992
def work0992 : RoundedTauEval :=
  evalTau precision tau0992 contact0992 logTwoBall

theorem center_sq0992 : (center0992.re : ℝ)^2 +
    (center0992.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0992]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0992 : work0992.theta.ok = true ∧
    work0992.jac.invOK = true ∧ acceptsUnitSq work0992.out = true := by
  norm_num [work0992, contact0992, tau0992, center0992, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0992 : CellCertificate where
  tauBall := tau0992
  contactCenter := center0992
  contactBall := contact0992
  work := work0992
  center_sq := center_sq0992
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0992.1
  jac_ok := checks0992.2.1
  accepted := checks0992.2.2

def tau0993 : RatBall :=
  ⟨⟨63/160, 11/160⟩, 3/320⟩
def center0993 : GaussianRat :=
  ⟨260517353/1000000000, 1026213/25000000⟩
def contact0993 : RatBall := localContactBall tau0993 center0993
def work0993 : RoundedTauEval :=
  evalTau precision tau0993 contact0993 logTwoBall

theorem center_sq0993 : (center0993.re : ℝ)^2 +
    (center0993.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0993]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0993 : work0993.theta.ok = true ∧
    work0993.jac.invOK = true ∧ acceptsUnitSq work0993.out = true := by
  norm_num [work0993, contact0993, tau0993, center0993, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0993 : CellCertificate where
  tauBall := tau0993
  contactCenter := center0993
  contactBall := contact0993
  work := work0993
  center_sq := center_sq0993
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0993.1
  jac_ok := checks0993.2.1
  accepted := checks0993.2.2

def tau0994 : RatBall :=
  ⟨⟨57/160, 13/160⟩, 3/320⟩
def center0994 : GaussianRat :=
  ⟨238180443/1000000000, 24897027/500000000⟩
def contact0994 : RatBall := localContactBall tau0994 center0994
def work0994 : RoundedTauEval :=
  evalTau precision tau0994 contact0994 logTwoBall

theorem center_sq0994 : (center0994.re : ℝ)^2 +
    (center0994.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0994]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0994 : work0994.theta.ok = true ∧
    work0994.jac.invOK = true ∧ acceptsUnitSq work0994.out = true := by
  norm_num [work0994, contact0994, tau0994, center0994, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0994 : CellCertificate where
  tauBall := tau0994
  contactCenter := center0994
  contactBall := contact0994
  work := work0994
  center_sq := center_sq0994
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0994.1
  jac_ok := checks0994.2.1
  accepted := checks0994.2.2

def tau0995 : RatBall :=
  ⟨⟨59/160, 13/160⟩, 3/320⟩
def center0995 : GaussianRat :=
  ⟨245825343/1000000000, 12344447/250000000⟩
def contact0995 : RatBall := localContactBall tau0995 center0995
def work0995 : RoundedTauEval :=
  evalTau precision tau0995 contact0995 logTwoBall

theorem center_sq0995 : (center0995.re : ℝ)^2 +
    (center0995.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0995]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0995 : work0995.theta.ok = true ∧
    work0995.jac.invOK = true ∧ acceptsUnitSq work0995.out = true := by
  norm_num [work0995, contact0995, tau0995, center0995, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0995 : CellCertificate where
  tauBall := tau0995
  contactCenter := center0995
  contactBall := contact0995
  work := work0995
  center_sq := center_sq0995
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0995.1
  jac_ok := checks0995.2.1
  accepted := checks0995.2.2

def tau0996 : RatBall :=
  ⟨⟨57/160, 3/32⟩, 3/320⟩
def center0996 : GaussianRat :=
  ⟨11931267/50000000, 14368881/250000000⟩
def contact0996 : RatBall := localContactBall tau0996 center0996
def work0996 : RoundedTauEval :=
  evalTau precision tau0996 contact0996 logTwoBall

theorem center_sq0996 : (center0996.re : ℝ)^2 +
    (center0996.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0996]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0996 : work0996.theta.ok = true ∧
    work0996.jac.invOK = true ∧ acceptsUnitSq work0996.out = true := by
  norm_num [work0996, contact0996, tau0996, center0996, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0996 : CellCertificate where
  tauBall := tau0996
  contactCenter := center0996
  contactBall := contact0996
  work := work0996
  center_sq := center_sq0996
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0996.1
  jac_ok := checks0996.2.1
  accepted := checks0996.2.2

def tau0997 : RatBall :=
  ⟨⟨59/160, 3/32⟩, 3/320⟩
def center0997 : GaussianRat :=
  ⟨246278271/1000000000, 56993771/1000000000⟩
def contact0997 : RatBall := localContactBall tau0997 center0997
def work0997 : RoundedTauEval :=
  evalTau precision tau0997 contact0997 logTwoBall

theorem center_sq0997 : (center0997.re : ℝ)^2 +
    (center0997.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0997]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0997 : work0997.theta.ok = true ∧
    work0997.jac.invOK = true ∧ acceptsUnitSq work0997.out = true := by
  norm_num [work0997, contact0997, tau0997, center0997, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0997 : CellCertificate where
  tauBall := tau0997
  contactCenter := center0997
  contactBall := contact0997
  work := work0997
  center_sq := center_sq0997
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0997.1
  jac_ok := checks0997.2.1
  accepted := checks0997.2.2

def tau0998 : RatBall :=
  ⟨⟨61/160, 13/160⟩, 3/320⟩
def center0998 : GaussianRat :=
  ⟨126702243/500000000, 6119291/125000000⟩
def contact0998 : RatBall := localContactBall tau0998 center0998
def work0998 : RoundedTauEval :=
  evalTau precision tau0998 contact0998 logTwoBall

theorem center_sq0998 : (center0998.re : ℝ)^2 +
    (center0998.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0998]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0998 : work0998.theta.ok = true ∧
    work0998.jac.invOK = true ∧ acceptsUnitSq work0998.out = true := by
  norm_num [work0998, contact0998, tau0998, center0998, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0998 : CellCertificate where
  tauBall := tau0998
  contactCenter := center0998
  contactBall := contact0998
  work := work0998
  center_sq := center_sq0998
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0998.1
  jac_ok := checks0998.2.1
  accepted := checks0998.2.2

def tau0999 : RatBall :=
  ⟨⟨63/160, 13/160⟩, 3/320⟩
def center0999 : GaussianRat :=
  ⟨260916819/1000000000, 48524207/1000000000⟩
def contact0999 : RatBall := localContactBall tau0999 center0999
def work0999 : RoundedTauEval :=
  evalTau precision tau0999 contact0999 logTwoBall

theorem center_sq0999 : (center0999.re : ℝ)^2 +
    (center0999.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0999 : work0999.theta.ok = true ∧
    work0999.jac.invOK = true ∧ acceptsUnitSq work0999.out = true := by
  norm_num [work0999, contact0999, tau0999, center0999, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell0999 : CellCertificate where
  tauBall := tau0999
  contactCenter := center0999
  contactBall := contact0999
  work := work0999
  center_sq := center_sq0999
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0999.1
  jac_ok := checks0999.2.1
  accepted := checks0999.2.2

def cells : List CellCertificate := [cell0992, cell0993, cell0994, cell0995, cell0996, cell0997, cell0998, cell0999]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124

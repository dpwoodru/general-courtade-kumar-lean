import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1992 : RatBall :=
  ⟨⟨-15/64, 97/320⟩, 3/640⟩
def center1992 : GaussianRat :=
  ⟨-87284451/500000000, 101799907/500000000⟩
def contact1992 : RatBall := localContactBall tau1992 center1992
def work1992 : RoundedTauEval :=
  evalTau precision tau1992 contact1992 logTwoBall

theorem center_sq1992 : (center1992.re : ℝ)^2 +
    (center1992.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1992]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1992 : work1992.theta.ok = true ∧
    work1992.jac.invOK = true ∧ acceptsUnitSq work1992.out = true := by
  norm_num [work1992, contact1992, tau1992, center1992, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1992 : CellCertificate where
  tauBall := tau1992
  contactCenter := center1992
  contactBall := contact1992
  work := work1992
  center_sq := center_sq1992
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1992.1
  jac_ok := checks1992.2.1
  accepted := checks1992.2.2

def tau1993 : RatBall :=
  ⟨⟨-73/320, 97/320⟩, 3/640⟩
def center1993 : GaussianRat :=
  ⟨-42539121/250000000, 204268971/1000000000⟩
def contact1993 : RatBall := localContactBall tau1993 center1993
def work1993 : RoundedTauEval :=
  evalTau precision tau1993 contact1993 logTwoBall

theorem center_sq1993 : (center1993.re : ℝ)^2 +
    (center1993.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1993]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1993 : work1993.theta.ok = true ∧
    work1993.jac.invOK = true ∧ acceptsUnitSq work1993.out = true := by
  norm_num [work1993, contact1993, tau1993, center1993, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1993 : CellCertificate where
  tauBall := tau1993
  contactCenter := center1993
  contactBall := contact1993
  work := work1993
  center_sq := center_sq1993
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1993.1
  jac_ok := checks1993.2.1
  accepted := checks1993.2.2

def tau1994 : RatBall :=
  ⟨⟨-15/64, 99/320⟩, 3/640⟩
def center1994 : GaussianRat :=
  ⟨-35050807/200000000, 8320383/40000000⟩
def contact1994 : RatBall := localContactBall tau1994 center1994
def work1994 : RoundedTauEval :=
  evalTau precision tau1994 contact1994 logTwoBall

theorem center_sq1994 : (center1994.re : ℝ)^2 +
    (center1994.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1994]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1994 : work1994.theta.ok = true ∧
    work1994.jac.invOK = true ∧ acceptsUnitSq work1994.out = true := by
  norm_num [work1994, contact1994, tau1994, center1994, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1994 : CellCertificate where
  tauBall := tau1994
  contactCenter := center1994
  contactBall := contact1994
  work := work1994
  center_sq := center_sq1994
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1994.1
  jac_ok := checks1994.2.1
  accepted := checks1994.2.2

def tau1995 : RatBall :=
  ⟨⟨-73/320, 99/320⟩, 3/640⟩
def center1995 : GaussianRat :=
  ⟨-42707047/250000000, 20869737/100000000⟩
def contact1995 : RatBall := localContactBall tau1995 center1995
def work1995 : RoundedTauEval :=
  evalTau precision tau1995 contact1995 logTwoBall

theorem center_sq1995 : (center1995.re : ℝ)^2 +
    (center1995.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1995]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1995 : work1995.theta.ok = true ∧
    work1995.jac.invOK = true ∧ acceptsUnitSq work1995.out = true := by
  norm_num [work1995, contact1995, tau1995, center1995, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1995 : CellCertificate where
  tauBall := tau1995
  contactCenter := center1995
  contactBall := contact1995
  work := work1995
  center_sq := center_sq1995
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1995.1
  jac_ok := checks1995.2.1
  accepted := checks1995.2.2

def tau1996 : RatBall :=
  ⟨⟨-79/320, 101/320⟩, 3/640⟩
def center1996 : GaussianRat :=
  ⟨-92389531/500000000, 210978373/1000000000⟩
def contact1996 : RatBall := localContactBall tau1996 center1996
def work1996 : RoundedTauEval :=
  evalTau precision tau1996 contact1996 logTwoBall

theorem center_sq1996 : (center1996.re : ℝ)^2 +
    (center1996.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1996]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1996 : work1996.theta.ok = true ∧
    work1996.jac.invOK = true ∧ acceptsUnitSq work1996.out = true := by
  norm_num [work1996, contact1996, tau1996, center1996, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1996 : CellCertificate where
  tauBall := tau1996
  contactCenter := center1996
  contactBall := contact1996
  work := work1996
  center_sq := center_sq1996
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1996.1
  jac_ok := checks1996.2.1
  accepted := checks1996.2.2

def tau1997 : RatBall :=
  ⟨⟨-77/320, 101/320⟩, 3/640⟩
def center1997 : GaussianRat :=
  ⟨-45094603/250000000, 105856123/500000000⟩
def contact1997 : RatBall := localContactBall tau1997 center1997
def work1997 : RoundedTauEval :=
  evalTau precision tau1997 contact1997 logTwoBall

theorem center_sq1997 : (center1997.re : ℝ)^2 +
    (center1997.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1997]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1997 : work1997.theta.ok = true ∧
    work1997.jac.invOK = true ∧ acceptsUnitSq work1997.out = true := by
  norm_num [work1997, contact1997, tau1997, center1997, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1997 : CellCertificate where
  tauBall := tau1997
  contactCenter := center1997
  contactBall := contact1997
  work := work1997
  center_sq := center_sq1997
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1997.1
  jac_ok := checks1997.2.1
  accepted := checks1997.2.2

def tau1998 : RatBall :=
  ⟨⟨-77/320, 103/320⟩, 3/640⟩
def center1998 : GaussianRat :=
  ⟨-36223107/200000000, 108064747/500000000⟩
def contact1998 : RatBall := localContactBall tau1998 center1998
def work1998 : RoundedTauEval :=
  evalTau precision tau1998 contact1998 logTwoBall

theorem center_sq1998 : (center1998.re : ℝ)^2 +
    (center1998.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1998]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1998 : work1998.theta.ok = true ∧
    work1998.jac.invOK = true ∧ acceptsUnitSq work1998.out = true := by
  norm_num [work1998, contact1998, tau1998, center1998, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1998 : CellCertificate where
  tauBall := tau1998
  contactCenter := center1998
  contactBall := contact1998
  work := work1998
  center_sq := center_sq1998
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1998.1
  jac_ok := checks1998.2.1
  accepted := checks1998.2.2

def tau1999 : RatBall :=
  ⟨⟨-15/64, 101/320⟩, 3/640⟩
def center1999 : GaussianRat :=
  ⟨-21994767/125000000, 212432751/1000000000⟩
def contact1999 : RatBall := localContactBall tau1999 center1999
def work1999 : RoundedTauEval :=
  evalTau precision tau1999 contact1999 logTwoBall

theorem center_sq1999 : (center1999.re : ℝ)^2 +
    (center1999.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1999 : work1999.theta.ok = true ∧
    work1999.jac.invOK = true ∧ acceptsUnitSq work1999.out = true := by
  norm_num [work1999, contact1999, tau1999, center1999, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1999 : CellCertificate where
  tauBall := tau1999
  contactCenter := center1999
  contactBall := contact1999
  work := work1999
  center_sq := center_sq1999
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1999.1
  jac_ok := checks1999.2.1
  accepted := checks1999.2.2

def cells : List CellCertificate := [cell1992, cell1993, cell1994, cell1995, cell1996, cell1997, cell1998, cell1999]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249

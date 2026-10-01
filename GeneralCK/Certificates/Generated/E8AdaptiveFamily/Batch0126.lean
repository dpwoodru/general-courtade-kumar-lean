import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1008 : RatBall :=
  ⟨⟨9/32, 27/160⟩, 3/320⟩
def center1008 : GaussianRat :=
  ⟨194904883/1000000000, 13595459/125000000⟩
def contact1008 : RatBall := localContactBall tau1008 center1008
def work1008 : RoundedTauEval :=
  evalTau precision tau1008 contact1008 logTwoBall

theorem center_sq1008 : (center1008.re : ℝ)^2 +
    (center1008.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1008]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1008 : work1008.theta.ok = true ∧
    work1008.jac.invOK = true ∧ acceptsUnitSq work1008.out = true := by
  norm_num [work1008, contact1008, tau1008, center1008, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1008 : CellCertificate where
  tauBall := tau1008
  contactCenter := center1008
  contactBall := contact1008
  work := work1008
  center_sq := center_sq1008
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1008.1
  jac_ok := checks1008.2.1
  accepted := checks1008.2.2

def tau1009 : RatBall :=
  ⟨⟨47/160, 27/160⟩, 3/320⟩
def center1009 : GaussianRat :=
  ⟨5075841/25000000, 107985769/1000000000⟩
def contact1009 : RatBall := localContactBall tau1009 center1009
def work1009 : RoundedTauEval :=
  evalTau precision tau1009 contact1009 logTwoBall

theorem center_sq1009 : (center1009.re : ℝ)^2 +
    (center1009.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1009]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1009 : work1009.theta.ok = true ∧
    work1009.jac.invOK = true ∧ acceptsUnitSq work1009.out = true := by
  norm_num [work1009, contact1009, tau1009, center1009, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1009 : CellCertificate where
  tauBall := tau1009
  contactCenter := center1009
  contactBall := contact1009
  work := work1009
  center_sq := center_sq1009
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1009.1
  jac_ok := checks1009.2.1
  accepted := checks1009.2.2

def tau1010 : RatBall :=
  ⟨⟨41/160, 29/160⟩, 3/320⟩
def center1010 : GaussianRat :=
  ⟨89605161/500000000, 4741701/40000000⟩
def contact1010 : RatBall := localContactBall tau1010 center1010
def work1010 : RoundedTauEval :=
  evalTau precision tau1010 contact1010 logTwoBall

theorem center_sq1010 : (center1010.re : ℝ)^2 +
    (center1010.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1010]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1010 : work1010.theta.ok = true ∧
    work1010.jac.invOK = true ∧ acceptsUnitSq work1010.out = true := by
  norm_num [work1010, contact1010, tau1010, center1010, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1010 : CellCertificate where
  tauBall := tau1010
  contactCenter := center1010
  contactBall := contact1010
  work := work1010
  center_sq := center_sq1010
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1010.1
  jac_ok := checks1010.2.1
  accepted := checks1010.2.2

def tau1011 : RatBall :=
  ⟨⟨43/160, 29/160⟩, 3/320⟩
def center1011 : GaussianRat :=
  ⟨187487239/1000000000, 23550431/200000000⟩
def contact1011 : RatBall := localContactBall tau1011 center1011
def work1011 : RoundedTauEval :=
  evalTau precision tau1011 contact1011 logTwoBall

theorem center_sq1011 : (center1011.re : ℝ)^2 +
    (center1011.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1011]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1011 : work1011.theta.ok = true ∧
    work1011.jac.invOK = true ∧ acceptsUnitSq work1011.out = true := by
  norm_num [work1011, contact1011, tau1011, center1011, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1011 : CellCertificate where
  tauBall := tau1011
  contactCenter := center1011
  contactBall := contact1011
  work := work1011
  center_sq := center_sq1011
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1011.1
  jac_ok := checks1011.2.1
  accepted := checks1011.2.2

def tau1012 : RatBall :=
  ⟨⟨41/160, 31/160⟩, 3/320⟩
def center1012 : GaussianRat :=
  ⟨36003433/200000000, 3171591/25000000⟩
def contact1012 : RatBall := localContactBall tau1012 center1012
def work1012 : RoundedTauEval :=
  evalTau precision tau1012 contact1012 logTwoBall

theorem center_sq1012 : (center1012.re : ℝ)^2 +
    (center1012.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1012]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1012 : work1012.theta.ok = true ∧
    work1012.jac.invOK = true ∧ acceptsUnitSq work1012.out = true := by
  norm_num [work1012, contact1012, tau1012, center1012, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1012 : CellCertificate where
  tauBall := tau1012
  contactCenter := center1012
  contactBall := contact1012
  work := work1012
  center_sq := center_sq1012
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1012.1
  jac_ok := checks1012.2.1
  accepted := checks1012.2.2

def tau1013 : RatBall :=
  ⟨⟨43/160, 31/160⟩, 3/320⟩
def center1013 : GaussianRat :=
  ⟨188321901/1000000000, 126012049/1000000000⟩
def contact1013 : RatBall := localContactBall tau1013 center1013
def work1013 : RoundedTauEval :=
  evalTau precision tau1013 contact1013 logTwoBall

theorem center_sq1013 : (center1013.re : ℝ)^2 +
    (center1013.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1013]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1013 : work1013.theta.ok = true ∧
    work1013.jac.invOK = true ∧ acceptsUnitSq work1013.out = true := by
  norm_num [work1013, contact1013, tau1013, center1013, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1013 : CellCertificate where
  tauBall := tau1013
  contactCenter := center1013
  contactBall := contact1013
  work := work1013
  center_sq := center_sq1013
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1013.1
  jac_ok := checks1013.2.1
  accepted := checks1013.2.2

def tau1014 : RatBall :=
  ⟨⟨9/32, 29/160⟩, 3/320⟩
def center1014 : GaussianRat :=
  ⟨97851331/500000000, 116935591/1000000000⟩
def contact1014 : RatBall := localContactBall tau1014 center1014
def work1014 : RoundedTauEval :=
  evalTau precision tau1014 contact1014 logTwoBall

theorem center_sq1014 : (center1014.re : ℝ)^2 +
    (center1014.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1014]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1014 : work1014.theta.ok = true ∧
    work1014.jac.invOK = true ∧ acceptsUnitSq work1014.out = true := by
  norm_num [work1014, contact1014, tau1014, center1014, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1014 : CellCertificate where
  tauBall := tau1014
  contactCenter := center1014
  contactBall := contact1014
  work := work1014
  center_sq := center_sq1014
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1014.1
  jac_ok := checks1014.2.1
  accepted := checks1014.2.2

def tau1015 : RatBall :=
  ⟨⟨47/160, 29/160⟩, 3/320⟩
def center1015 : GaussianRat :=
  ⟨25481847/125000000, 58047077/500000000⟩
def contact1015 : RatBall := localContactBall tau1015 center1015
def work1015 : RoundedTauEval :=
  evalTau precision tau1015 contact1015 logTwoBall

theorem center_sq1015 : (center1015.re : ℝ)^2 +
    (center1015.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1015]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1015 : work1015.theta.ok = true ∧
    work1015.jac.invOK = true ∧ acceptsUnitSq work1015.out = true := by
  norm_num [work1015, contact1015, tau1015, center1015, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1015 : CellCertificate where
  tauBall := tau1015
  contactCenter := center1015
  contactBall := contact1015
  work := work1015
  center_sq := center_sq1015
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1015.1
  jac_ok := checks1015.2.1
  accepted := checks1015.2.2

def cells : List CellCertificate := [cell1008, cell1009, cell1010, cell1011, cell1012, cell1013, cell1014, cell1015]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126

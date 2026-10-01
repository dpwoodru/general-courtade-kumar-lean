import GeneralCK.Certificates.E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1936 : RatBall :=
  ⟨⟨-81/320, 87/320⟩, 3/640⟩
def center1936 : GaussianRat :=
  ⟨-9218121/50000000, 179930859/1000000000⟩
def contact1936 : RatBall := localContactBall tau1936 center1936
def work1936 : RoundedTauEval :=
  evalTau precision tau1936 contact1936 logTwoBall

theorem center_sq1936 : (center1936.re : ℝ)^2 +
    (center1936.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1936]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1936 : work1936.theta.ok = true ∧
    work1936.jac.invOK = true ∧ acceptsUnitSq work1936.out = true := by
  norm_num [work1936, contact1936, tau1936, center1936, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1936 : CellCertificate where
  tauBall := tau1936
  contactCenter := center1936
  contactBall := contact1936
  work := work1936
  center_sq := center_sq1936
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1936.1
  jac_ok := checks1936.2.1
  accepted := checks1936.2.2

def tau1937 : RatBall :=
  ⟨⟨-93/320, 89/320⟩, 3/640⟩
def center1937 : GaussianRat :=
  ⟨-84181/400000, 180208911/1000000000⟩
def contact1937 : RatBall := localContactBall tau1937 center1937
def work1937 : RoundedTauEval :=
  evalTau precision tau1937 contact1937 logTwoBall

theorem center_sq1937 : (center1937.re : ℝ)^2 +
    (center1937.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1937]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1937 : work1937.theta.ok = true ∧
    work1937.jac.invOK = true ∧ acceptsUnitSq work1937.out = true := by
  norm_num [work1937, contact1937, tau1937, center1937, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1937 : CellCertificate where
  tauBall := tau1937
  contactCenter := center1937
  contactBall := contact1937
  work := work1937
  center_sq := center_sq1937
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1937.1
  jac_ok := checks1937.2.1
  accepted := checks1937.2.2

def tau1938 : RatBall :=
  ⟨⟨-91/320, 89/320⟩, 3/640⟩
def center1938 : GaussianRat :=
  ⟨-103128439/500000000, 180903081/1000000000⟩
def contact1938 : RatBall := localContactBall tau1938 center1938
def work1938 : RoundedTauEval :=
  evalTau precision tau1938 contact1938 logTwoBall

theorem center_sq1938 : (center1938.re : ℝ)^2 +
    (center1938.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1938]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1938 : work1938.theta.ok = true ∧
    work1938.jac.invOK = true ∧ acceptsUnitSq work1938.out = true := by
  norm_num [work1938, contact1938, tau1938, center1938, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1938 : CellCertificate where
  tauBall := tau1938
  contactCenter := center1938
  contactBall := contact1938
  work := work1938
  center_sq := center_sq1938
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1938.1
  jac_ok := checks1938.2.1
  accepted := checks1938.2.2

def tau1939 : RatBall :=
  ⟨⟨-89/320, 89/320⟩, 3/640⟩
def center1939 : GaussianRat :=
  ⟨-40408359/200000000, 181587727/1000000000⟩
def contact1939 : RatBall := localContactBall tau1939 center1939
def work1939 : RoundedTauEval :=
  evalTau precision tau1939 contact1939 logTwoBall

theorem center_sq1939 : (center1939.re : ℝ)^2 +
    (center1939.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1939]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1939 : work1939.theta.ok = true ∧
    work1939.jac.invOK = true ∧ acceptsUnitSq work1939.out = true := by
  norm_num [work1939, contact1939, tau1939, center1939, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1939 : CellCertificate where
  tauBall := tau1939
  contactCenter := center1939
  contactBall := contact1939
  work := work1939
  center_sq := center_sq1939
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1939.1
  jac_ok := checks1939.2.1
  accepted := checks1939.2.2

def tau1940 : RatBall :=
  ⟨⟨-91/320, 91/320⟩, 3/640⟩
def center1940 : GaussianRat :=
  ⟨-51739029/250000000, 46278317/250000000⟩
def contact1940 : RatBall := localContactBall tau1940 center1940
def work1940 : RoundedTauEval :=
  evalTau precision tau1940 contact1940 logTwoBall

theorem center_sq1940 : (center1940.re : ℝ)^2 +
    (center1940.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1940]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1940 : work1940.theta.ok = true ∧
    work1940.jac.invOK = true ∧ acceptsUnitSq work1940.out = true := by
  norm_num [work1940, contact1940, tau1940, center1940, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1940 : CellCertificate where
  tauBall := tau1940
  contactCenter := center1940
  contactBall := contact1940
  work := work1940
  center_sq := center_sq1940
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1940.1
  jac_ok := checks1940.2.1
  accepted := checks1940.2.2

def tau1941 : RatBall :=
  ⟨⟨-89/320, 91/320⟩, 3/640⟩
def center1941 : GaussianRat :=
  ⟨-202731249/1000000000, 37163483/200000000⟩
def contact1941 : RatBall := localContactBall tau1941 center1941
def work1941 : RoundedTauEval :=
  evalTau precision tau1941 contact1941 logTwoBall

theorem center_sq1941 : (center1941.re : ℝ)^2 +
    (center1941.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1941]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1941 : work1941.theta.ok = true ∧
    work1941.jac.invOK = true ∧ acceptsUnitSq work1941.out = true := by
  norm_num [work1941, contact1941, tau1941, center1941, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1941 : CellCertificate where
  tauBall := tau1941
  contactCenter := center1941
  contactBall := contact1941
  work := work1941
  center_sq := center_sq1941
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1941.1
  jac_ok := checks1941.2.1
  accepted := checks1941.2.2

def tau1942 : RatBall :=
  ⟨⟨-89/320, 93/320⟩, 3/640⟩
def center1942 : GaussianRat :=
  ⟨-50860061/250000000, 2969643/15625000⟩
def contact1942 : RatBall := localContactBall tau1942 center1942
def work1942 : RoundedTauEval :=
  evalTau precision tau1942 contact1942 logTwoBall

theorem center_sq1942 : (center1942.re : ℝ)^2 +
    (center1942.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1942]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1942 : work1942.theta.ok = true ∧
    work1942.jac.invOK = true ∧ acceptsUnitSq work1942.out = true := by
  norm_num [work1942, contact1942, tau1942, center1942, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1942 : CellCertificate where
  tauBall := tau1942
  contactCenter := center1942
  contactBall := contact1942
  work := work1942
  center_sq := center_sq1942
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1942.1
  jac_ok := checks1942.2.1
  accepted := checks1942.2.2

def tau1943 : RatBall :=
  ⟨⟨-87/320, 89/320⟩, 3/640⟩
def center1943 : GaussianRat :=
  ⟨-7912299/40000000, 91131277/500000000⟩
def contact1943 : RatBall := localContactBall tau1943 center1943
def work1943 : RoundedTauEval :=
  evalTau precision tau1943 contact1943 logTwoBall

theorem center_sq1943 : (center1943.re : ℝ)^2 +
    (center1943.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1943]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1943 : work1943.theta.ok = true ∧
    work1943.jac.invOK = true ∧ acceptsUnitSq work1943.out = true := by
  norm_num [work1943, contact1943, tau1943, center1943, evalTau, evalTheta, rlog, rsub, rdiv, rsquare, precision,
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

def cell1943 : CellCertificate where
  tauBall := tau1943
  contactCenter := center1943
  contactBall := contact1943
  work := work1943
  center_sq := center_sq1943
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1943.1
  jac_ok := checks1943.2.1
  accepted := checks1943.2.2

def cells : List CellCertificate := [cell1936, cell1937, cell1938, cell1939, cell1940, cell1941, cell1942, cell1943]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242

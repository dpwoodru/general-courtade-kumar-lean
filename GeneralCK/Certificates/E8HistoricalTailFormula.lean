import GeneralCK.Certificates.E8RegularizedLog1p

/-!
# Exact `(v,u)` formula used by the historical E8 tail certificate

This is a literal algebraic transcription of `cert_theta_tail.cpp`, with
`log (1 + u) / u` replaced by its sound removable extension.  The old C++
code used a total-order-three centred jet to reduce interval wrapping.  For
a Lean replay one may instead evaluate the expressions below directly from
the value/first-derivative box in `E8RegularizedLog1p`: only the first partial
derivatives of `E` enter `Dalpha E`.
-/

namespace GeneralCK.Certificates.E8HistoricalTailFormula

open E8RegularizedLog1p

noncomputable def r (u : ℝ) : ℝ := (1 - u) / (1 + u)
noncomputable def rPrime (u : ℝ) : ℝ := -2 / (1 + u) ^ 2

noncomputable def B (v u : ℝ) : ℝ :=
  1 + v * u * regLog1p u

noncomputable def Bv (_v u : ℝ) : ℝ := u * regLog1p u
noncomputable def Bu (v u : ℝ) : ℝ :=
  v * (regLog1p u + u * regLog1pPrime u)

noncomputable def G (v u : ℝ) : ℝ :=
  v * regLog1p u + 2 / (1 + u)

noncomputable def Gv (_v u : ℝ) : ℝ := regLog1p u
noncomputable def Gu (v u : ℝ) : ℝ :=
  v * regLog1pPrime u - 2 / (1 + u) ^ 2

noncomputable def qhDen (v u : ℝ) : ℝ := (1 + u) ^ 2 * G v u
noncomputable def qh (v u : ℝ) : ℝ := 4 / qhDen v u

noncomputable def qhV (v u : ℝ) : ℝ :=
  -4 * ((1 + u) ^ 2 * Gv v u) / qhDen v u ^ 2

noncomputable def qhU (v u : ℝ) : ℝ :=
  -4 * (2 * (1 + u) * G v u + (1 + u) ^ 2 * Gu v u) /
    qhDen v u ^ 2

noncomputable def C (v u : ℝ) : ℝ :=
  2 * B v u - v * r u ^ 2

noncomputable def Cv (v u : ℝ) : ℝ :=
  2 * Bv v u - r u ^ 2

noncomputable def Cu (v u : ℝ) : ℝ :=
  2 * Bu v u - 2 * v * r u * rPrime u

/-- Historical `E = (log (Y'/X'))'`. -/
noncomputable def E (v u : ℝ) : ℝ :=
  -3 * qh v u + 2 * v * r u ^ 3 / C v u + 4 * r u -
    3 * v * r u / B v u

noncomputable def Ev (v u : ℝ) : ℝ :=
  -3 * qhV v u +
    (2 * r u ^ 3 / C v u -
      2 * v * r u ^ 3 * Cv v u / C v u ^ 2) -
    3 * r u / B v u +
    3 * v * r u * Bv v u / B v u ^ 2

noncomputable def Eu (v u : ℝ) : ℝ :=
  -3 * qhU v u +
    2 * v * (3 * r u ^ 2 * rPrime u / C v u -
      r u ^ 3 * Cu v u / C v u ^ 2) +
    4 * rPrime u -
    3 * v * (rPrime u / B v u - r u * Bu v u / B v u ^ 2)

/-- `d/da = -v² d/dv - 2u d/du` under `v=1/a`, `u=exp(-2a)`. -/
noncomputable def Ealpha (v u : ℝ) : ℝ :=
  -(v ^ 2) * Ev v u - 2 * u * Eu v u

/-- Historical `X = (log X')'`. -/
noncomputable def X (v u : ℝ) : ℝ :=
  v * r u / B v u - 2 * r u + 2 * qh v u

/-- The exact tail scalar checked by `cert_theta_tail.cpp`. -/
noncomputable def L (v u : ℝ) : ℝ :=
  E v u ^ 2 - Ealpha v u + E v u * X v u

end GeneralCK.Certificates.E8HistoricalTailFormula

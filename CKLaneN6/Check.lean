import CKLaneN6.Rad
import CKLaneN6.LSKW
import CKLaneN6.APar
import CKLaneN6.PLog

/-!
# Lane N6: the unified per-cell certificate of SMALL_RATIO Theorem 3

`W.check B w = true → LeafOK B` for every certificate constructor (`W.check_sound`):

| constructor | archived owners it serves | kernel |
|---|---|---|
| `irr`   | `outside` | `b1 - a0 < 1/100` |
| `prior` | `prior_same_side` | `1/20 ≤ b0 - a1` |
| `csr`   | `central_small_ratio` | `E⁺ ≤ 11/200`, `b1 - a0 ≤ 4 E⁻` |
| `cap`   | `cap` | `(1-t0)(C0hi - EMIN) ≤ 3/40` (`CKLaneM05.FE8.capCheck`) |
| `apar`  | `phi_parent`, `phi_parent_log` | compiled analytic parent dominance (`CKLaneN6.APar`) |
| `par`   | `phi_parent` | monotone parent dominance (`CKLaneM05.FE8.parentCheck`, reused) |
| `plog`  | `phi_parent_log` | archive rule (13) (`CKLaneN6.PLog`) |
| `rad`   | `sum_normalized`, `endpoint_*`, `shifted_logsum`, `logsum*` | radial (`CKLaneN6.Rad`) |
| `lsk`   | `logsum*`, `shifted_logsum` | lane E `LSK` on the bounding box (`CKLaneN6.LSKW`) |

Cells may refine an archived leaf box (`CKLaneM05.FE8.CT`, exact halving); `CT.soundN6` and
`entries_sound` (`CKLaneN6.Base`) lift cell certificates to archived leaves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneN6

/-- Per-cell certificate. -/
inductive W where
  | irr
  | prior
  | csr
  | cap
  | apar
  | par (u0 v2 u1 : ℚ) (mode : Bool)
  | plog (vm vp v2 : ℚ)
  | rad (vS vI vc : ℚ) (useHm : Bool)
  | lsk (v0S v0I v1S v1I : ℚ)
  deriving Repr

def W.check (B : CKLaneD.Box) : W → Bool
  | .irr => decide (B.bhi - B.alo < 1 / 100)
  | .prior => decide (1 / 20 ≤ B.blo - B.ahi)
  | .csr => csrCheck B
  | .cap => CKLaneM05.FE8.capCheck B
  | .apar => APar.aparCheck B
  | .par u0 v2 u1 mode => CKLaneM05.FE8.parentCheck B ⟨u0, v2, u1, mode⟩
  | .plog vm vp v2 => PLog.plogCheck B ⟨vm, vp, v2⟩
  | .rad vS vI vc useHm => Rad.radCheck B ⟨vS, vI, vc, useHm⟩
  | .lsk v0S v0I v1S v1I => LSKW.lskCheck B ⟨v0S, v0I, v1S, v1I⟩

theorem W.check_sound : ∀ (B : CKLaneD.Box) (w : W), W.check B w = true → LeafOK B
  | _, .irr, h => leafOK_of_irr (by simpa [W.check] using h)
  | _, .prior, h => leafOK_of_prior (by simpa [W.check] using h)
  | _, .csr, h => leafOK_of_csr h
  | _, .cap, h => leafOK_of_cap h
  | _, .apar, h => APar.leafOK_of_aparCheck h
  | _, .par _ _ _ _, h => leafOK_of_parentBox (CKLaneM05.FE8.parentCheck_sound h)
  | _, .plog _ _ _, h => PLog.leafOK_of_plogCheck h
  | _, .rad _ _ _ _, h => Rad.leafOK_of_radCheck h
  | _, .lsk _ _ _ _, h => LSKW.leafOK_of_lskCheck h

/-- Shard form: one kernel-evaluated `List.all` gives every listed archived leaf. -/
theorem shard_sound (L : List (List ℕ × CKLaneM05.FE8.CT W))
    (h : L.all (fun x => x.2.check W.check (CKLaneM05.FE8.feBox x.1)) = true) :
    ∀ q ∈ L.map Prod.fst, LeafOK (CKLaneM05.FE8.feBox q) :=
  entries_sound W.check W.check_sound L h

/-- Compact dyadic literal `n / 2^e` for witness data. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

end CKLaneN6

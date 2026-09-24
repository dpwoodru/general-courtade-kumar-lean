import CKLaneA3X.TMFun

/-!
# CKLaneA3X.HornerSplit — one Horner iteration per theorem

`tmHorner_good` checks a whole Horner evaluation inside one kernel `decide`, which at order 24 needs
~30 GB. These lemmas perform one iteration `H ↦ c + X·H` with an intermediate literal accumulator `H`,
so each iteration is a separate (small) kernel check.
-/

namespace CKLaneA3X

theorem hornerSplit_good {x : ℝ → ℝ → ℝ} {X H : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n)
    (c : ℚ) (cs cs' : List ℚ) (hcs : cs = c :: cs')
    (hH : Good (fun t ρ => hornerR cs' (x t ρ)) H) (hHn : H.n = n) :
    Good (fun t ρ => hornerR cs (x t ρ)) (TMd.add (TMd.const c n) (TMd.mul X H vx 0 n)) := by
  subst hcs
  have hm := TMd.mul_good hx hH vx 0 n hz (zeroPrefix_zero _) hvx (by omega) (by omega)
  exact TMd.add_good (TMd.const_good c n) hm

theorem hornerSplitLast_good {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n)
    (c : ℚ) (cs : List ℚ) (hcs : cs = [c]) :
    Good (fun t ρ => hornerR cs (x t ρ)) (TMd.add (TMd.const c n) (TMd.mul X (TMd.zero n) vx 0 n)) :=
  hornerSplit_good hx vx n hz hvx hn c cs [] hcs (TMd.zero_good n) rfl

end CKLaneA3X

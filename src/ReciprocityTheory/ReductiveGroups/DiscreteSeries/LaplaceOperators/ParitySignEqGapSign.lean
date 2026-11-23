module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.InterlacesULt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.RsParLamMinus
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.GlueSt

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def WalkStepStatement : Prop :=
  S0.IntSStatement → StepStatement →
    ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (t : ℕ),
      1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
      StepGap (parEps k r) r h → BesselNZ (parEps k r) (lamT k r u b t) u →
      BesselNZ (parEps k r) (parLam k r v b) u

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.WalkEnds

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem walkEnds : EndsStatement := by
  intro k r u v b t
  refine ⟨?_, ?_, ?_⟩
  · funext a
    have ha := a.isLt
    simp only [lamT, raisePar]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
      | (have h0 : a.val - (k - 1) = 0 := by omega
         simp [h0])
  · funext a
    have ha := a.isLt
    simp only [raisePar, walkPar, parLam]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
  · funext a
    simp [walkPar]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Walk

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem walk : WalkStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hstep hP
  obtain ⟨e1, e2, e3⟩ := walkEnds k r u v b t
  have hR : ∀ j, 1 ≤ j → j ≤ 2 * r + 2 → P (raisePar k r u b t j) := by
    intro j
    induction j with
    | zero => intro h1; omega
    | succ j ih =>
      intro h1 h2
      rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · have hj : j = 0 := by omega
        subst hj
        rw [← e1]
        exact hP
      · exact raiseStep k r u v b h t P hk hpar hint hhalf hlow hstep j (by omega) (by omega)
          (ih (by omega) (by omega))
  have key : ∀ m, m ≤ k → P (walkPar k r u v b (k - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, ← e2]
      exact hR (2 * r + 2) (by omega) le_rfl
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have heq : k - m = (k - (m + 1)) + 1 := by omega
      rw [heq] at h1
      exact lowerStep k r u v b h P hk hpar hint hhalf hlow hstep (k - (m + 1)) (by omega) h1
  have h0 := key k le_rfl
  rw [Nat.sub_self, e3] at h0
  exact h0

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.ParEpsQOf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem parEps_qOf (k r : ℕ) (hk : 1 ≤ k) : qOf (parEps k r) = r + 1 :=
  noncompactCount_parabolicSign k r hk

theorem parEps_pOf (k r : ℕ) (hk : 1 ≤ k) : pOf (parEps k r) = k + r := by
  have h := compactCount_parabolicSign k r hk
  rw [show parEps k r = Formalism.MainNotions.CayleySignature.eps48 k r from rfl, h]
  omega

theorem walkStep : WalkStepStatement := by
  intro hIS hStep k r u v b h t hk hHC hI hH hL hG hB
  exact walk k r u v b h t (fun lam => BesselNZ (parEps k r) lam u) hk hHC hI hH hL
    (hStep hIS k r (parEps k r) u h hG (parEps_pOf k r hk) (parEps_qOf k r hk)) hB

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapLapStepGapStatement

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def GapLapStepGapStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), 1 ≤ pOf ε → 1 ≤ qOf ε → GapLap ε lam h →
    StepGap ε (qOf ε - 1) h

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapStep

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem gapLap_stepGap : GapLapStepGapStatement := by
  intro n ε lam h hp hq hG
  obtain ⟨-, -, hN⟩ := hG
  unfold hNeed at hN
  have h1 := lt_of_le_of_lt (le_max_left _ _) hN
  have h3 := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hcast : (((qOf ε - 1 : ℕ) : ℕ) : ℝ) = (qOf ε : ℝ) - 1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  have hm : (1 : ℝ) ≤ (min (pOf ε) (qOf ε) : ℕ) := by
    exact_mod_cast le_min hp hq
  have hs : 0 < Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨by linarith, ?_⟩
  rw [hcast, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  linarith
end Lap
end DS
end ChartRestriction
end ReciprocityTheory
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ParitySignEqGapSign

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def NVStatement : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ),
    1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
    GapLap (parEps k r) (parLam k r v b) h → BesselAll (parEps k r) (parLam k r v b) u

theorem nv_of (hI : Base.StepIBaseStatement) (hS : StepStatement) (hIS : S0.IntSStatement)
    (hDD : DecDerivStatement) : NVStatement := by
  intro k r u v b h hk hHC hIL hHalf hLow hGap
  have hp := parEps_pOf k r hk
  have hq := parEps_qOf k r hk
  have hSG : StepGap (parEps k r) r h := by
    have := gapLap_stepGap _ (parEps k r) (parLam k r v b) h (by rw [hp]; omega) (by rw [hq]; omega) hGap
    rwa [hq, Nat.add_sub_cancel] at this
  obtain ⟨t₀, ht⟩ := hI k r u v b hk hHC hIL hHalf
  exact TransportInt.transport_of hIS hDD hk hGap
    (walkStep hIS hS k r u v b h t₀ hk hHC hIL hHalf hLow hSG (ht t₀ le_rfl))

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
end

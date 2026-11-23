module

public import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTieCuts

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def EmbIntSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ t : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr t))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.L2.Pj

theorem vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha

theorem embIntSt_holds : EmbIntSt := by
  unfold EmbIntSt
  intro T C _ V ι h t
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, map_zero]
    exact VF.Ge.zero 0
  · have hx : algebraMap T.V T.Fr t ≠ 0 :=
      fun h0 => ht ((IsFractionRing.injective T.V T.Fr) (by rw [h0, map_zero]))
    have hl : ((V.l : ℕ) : T.Fr) = algebraMap T.V T.Fr ((V.l : ℕ) : T.V) := (map_natCast _ _).symm
    have h1 := vV_algebraMap_nonneg T t
    have h2 := vV_algebraMap_nonneg T ((V.l : ℕ) : T.V)
    rw [← hl] at h2
    unfold VF.Ge
    rw [h (algebraMap T.V T.Fr t) hx]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2))

end Formalism.L2.FormalSeriesBounds
end
end
end

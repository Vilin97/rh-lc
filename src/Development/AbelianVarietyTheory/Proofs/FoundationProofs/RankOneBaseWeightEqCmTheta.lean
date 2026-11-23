module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistCoverDesign
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalfOfPrimesIffLevelPb

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfOnRecord
end
end
end

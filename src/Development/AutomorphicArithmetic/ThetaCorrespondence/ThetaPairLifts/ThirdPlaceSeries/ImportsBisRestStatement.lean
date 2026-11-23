module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlaceStatement
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeStdTwCoverStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

end GlobalTheory.RowPointLoc
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRest

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowPointLoc
theorem main_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) :
    GlobalTheory.SplitRead.RowPoint D.nd D.naut := by
  intro i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ
end GlobalTheory.RowPointLoc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRestStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.point_of_aux42_aux41
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.Conclusion42 D →
      _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
      GlobalTheory.SplitRead.RowPoint D.nd D.naut :=
  _root_.GlobalTheory.RowPointLoc.main_alt_alt hL D P
end
end
end

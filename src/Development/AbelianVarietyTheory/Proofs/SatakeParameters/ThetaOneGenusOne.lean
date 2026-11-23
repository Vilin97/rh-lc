module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlacesStatement
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweThetaLiftComponents

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem howeUp_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i →
    GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  intro R H what₂ N A i hL hB hS hR σ P P' hP hP'
  refine GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places R H what₂ N A i hB hS hR P P' (Filter.Eventually.of_forall fun w hw => ?_)
  rw [hL σ P hP w hw, hL σ P' hP' w hw]

end GlobalTheory.RowTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  first | exact @GlobalTheory.RowTie.howeUp_of_pairLift | exact GlobalTheory.RowTie.howeUp_of_pairLift | (intros; apply GlobalTheory.RowTie.howeUp_of_pairLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaOneGenusOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end
end

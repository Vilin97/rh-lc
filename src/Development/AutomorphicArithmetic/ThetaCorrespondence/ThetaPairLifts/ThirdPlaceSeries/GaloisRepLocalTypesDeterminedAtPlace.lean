module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.InstMainA
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProduct
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaChi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisMore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamified

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm4OfRowsA

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypesAtPin

theorem not_over_g_of_mem_Q (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ D.nd.Q i)
    (k : Fin 2) : w ∉ placesOver D.host.E (D.host.g k) := by
  intro hk
  have hS : w ∈ D.nd.S i := (D.nd.S_def i w).2 ⟨by
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk), D.nd.SQ_l i w (Or.inr hw)⟩
  exact Finset.disjoint_left.1 (D.nd.SQ_disj i) hS hw

end GlobalTheory.TypesAtPin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockTypeVectorIrreducibleSplitsAsProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.blockTypeVector_irreducible_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], BlockSplit k := by
  first | exact @GlobalTheory.BlockSplitProof.main | exact GlobalTheory.BlockSplitProof.main | (intros; apply GlobalTheory.BlockSplitProof.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D C nch),
    Formalism.L2.Host.NCharTied D C nch Tp → GlobalTheory.SplitRead.MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tameParahoricRep_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  first | exact @GlobalTheory.TameIwahori.tameSplit | exact GlobalTheory.TameIwahori.tameSplit | (intros; apply GlobalTheory.TameIwahori.tameSplit <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiIneMain

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.MainNotions.SumRepresentations.At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
theorem chiIne_main_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D → MuInt D.nd D.naut →
    ChiIne D.nd D.naut :=
  fun D h0 h2 h5 hMu => _root_.GlobalTheory.SplitRead.chiIne_of_lp_aut_admissible_mult_one D.nd D.naut h0.1 h0.2.1 h2 h5 hMu
end GlobalTheory.SplitRead
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamifiedStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.type_tame_of_tame_not_unram : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  first | exact @_root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | exact _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | (intros; apply _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalTypesDeterminedAtPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypesAtPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro pr hL D P hrow rA
  obtain ⟨S, hTrue, hLaws, hSupp⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws pr.fin hL D P hrow
  have hTS : TameSplitAll D.host.E := fun w => GlobalTheory.T.tameParahoricRep_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hBS : BlockSplitAll D.host.E := fun w => GlobalTheory.T.blockTypeVector_irreducible_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hchi : ChiIne D.nd D.naut := _root_.GlobalTheory.SplitRead.chiIne_main_alt D rA.tie0 rA.a2 rA.a5
    (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr)
  have hTT : ∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) →
      TypeTame S i w hw := by
    intro i w hw h
    have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
      rcases h with hQ | ⟨-, hg⟩
      · exact not_over_g_of_mem_Q D i w hQ
      · exact hg
    have hSQ : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i := by
      rcases h with hQ | ⟨hS, -⟩
      · exact Or.inr hQ
      · exact Or.inl hS
    have ht := _root_.GlobalTheory.MuTameQS.main_alt_alt hL D P S hTrue i w hw hSQ
    exact _root_.GlobalTheory.T.type_tame_of_tame_not_unram hL D P S hTrue i w hw hng ht.1 (ht.2 hng)
  have hTB : ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw := by
    intro i w hw hSQ
    have ht := _root_.GlobalTheory.MuTameQS.main_alt_alt hL D P S hTrue i w hw hSQ
    by_cases hg : ∃ k, w ∈ placesOver D.host.E (D.host.g k)
    · exact _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hTrue i w hw hg ht.1
    · have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := fun k hk => hg ⟨k, hk⟩
      have hT : TypeTame S i w hw := hTT i w hw (by
        rcases hSQ with hS | hQ
        · exact Or.inr ⟨hS, hng⟩
        · exact Or.inl hQ)
      refine ⟨hT.1, fun Q => ?_⟩
      obtain ⟨v, hv0, hv⟩ := hT.2.2 Q
      exact ⟨v, hv0, fun h hK h1 _ u hu => hv h hK h1 u hu⟩
  exact _root_.GlobalTheory.InertialTypes.main_alt_alt D P.T S hTS hBS hLaws hSupp hchi hTT hTB
end GlobalTheory.TypesAtPin
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.archimedeanSignatureMatching_of_modules : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  first | exact @_root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end

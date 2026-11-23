module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.FarRegularExhaustion
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.InfinitesimalCharacterShift
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.DecayEstimate
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.KTypesAbove
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitaryStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ExhaustionFiniteLength

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  first | exact @GlobalTheory.CoverDS.unitEquiv_of_dsUnique | exact GlobalTheory.CoverDS.unitEquiv_of_dsUnique | (intros; apply GlobalTheory.CoverDS.unitEquiv_of_dsUnique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeries

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverExhaust

variable {p q n : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

theorem blockOrd_perm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (s : Equiv.Perm (Fin n))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : BlockOrd (e.trans s.symm) (ε ∘ s) := by
  refine ⟨fun i => by simpa using h.1 i, fun j => by simpa using h.2.1 j, ?_⟩
  intro a b hab
  obtain ⟨hlt, hε⟩ := (h.posC_iff a b).1 hab
  simp only [Equiv.trans_apply]
  rcases lt_trichotomy (s.symm (e a)) (s.symm (e b)) with h1 | h1 | h1
  · exact h1
  · exact absurd (s.symm.injective h1) (ne_of_lt hlt)
  · have h2 := hs _ _ h1 (by simp only [Equiv.apply_symm_apply]; exact hε.symm)
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd h2 (not_lt.2 hlt.le)

theorem exists_param_of_trivial (hE : GlobalTheory.Dec.DSExhaust) {T : GrpData p q} (R : DSRep T)
    (k : ∀ x, T.cov x = 1 → R.U.π x = 1) :
    ∃ (P : SignedPar (p + q)) (e : Ix p q ≃ Fin (p + q)), BlockOrd e P.sgn ∧ HasParam R (blockPar P e) := by
  obtain ⟨σ, hF⟩ := exists_factors R.U (finSumFinEquiv : Ix p q ≃ Fin (p + q)) k
  have hB0 := blockOrd_std p q
  have hIrr : GlobalTheory.Dec.IsSqIntIrr (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) σ :=
    ⟨R.U.cs, R.nontriv,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).1,
      (GlobalTheory.T.discreteSeries_cover_irreducibleUnitary p q (p + q) _ _ T R σ hB0 hF).2,
      GlobalTheory.T.block_ordered_square_integrable p q (p + q) _ _ T R σ hB0 hF⟩
  obtain ⟨s, mu, hc, hs, hDS⟩ := hE (p + q) _ R.U.H σ hIrr
  let P : SignedPar (p + q) := ⟨mu, (fun i : Fin (p + q) => (finSumFinEquiv.symm i).isLeft) ∘ s, hc⟩
  have hB : BlockOrd ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm) P.sgn := blockOrd_perm hB0 s hs
  have hF' : Factors R.U ((finSumFinEquiv : Ix p q ≃ Fin (p + q)).trans s.symm)
      (fun g => σ (g.submatrix s.symm s.symm)) := by
    intro x
    rw [hF x]
    congr 1
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact ⟨P, _, hB, (hasParam_iff_isDSPar R P hB hF').2 hDS⟩

theorem exists_param : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  intro hE p q _ T R
  rcases Cover.trivial_or_twist R with k | k
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE R k
    exact ⟨_, isParam_blockPar P h1, h2⟩
  · obtain ⟨P, e, h1, h2⟩ := exists_param_of_trivial hE (Cover.twist R) k
    exact ⟨_, isParam_half P h1, (Cover.hasParam_twist R _).1 h2⟩

end GlobalTheory.CoverExhaust
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeriesStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.exists_param_coverDiscreteSeries : GlobalTheory.Dec.DSExhaust → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T), ∃ lam, IsParam lam ∧ HasParam R lam := by
  first | exact @GlobalTheory.CoverExhaust.exists_param | exact GlobalTheory.CoverExhaust.exists_param | (intros; apply GlobalTheory.CoverExhaust.exists_param <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatio

section

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := GlobalTheory.T.exists_param_coverDiscreteSeries hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesDetSqrtCoverOfUnitaryClassificatioStatement

section

@[expose] public section

theorem GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover :=
  GlobalTheory.CoverDS.discreteSeriesCover_of_classification
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ClassLit

section

@[expose] public section

namespace CompanionTheory.RgExh.Fin

theorem dsClass_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.DSId.DSClass := by
  intro n
  have key : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), Formalism.QuantumDeterminants.IsHCParam lam → GlobalTheory.DSId.IsHCDS ε lam π ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
          Formalism.MainNotions.S.IsDS ε lam σ → GlobalTheory.Dec.UEquiv ε σ π := by
    intro ε lam
    by_cases hl : Formalism.QuantumDeterminants.IsHCParam lam
    · obtain ⟨G, i1, i2, π, h1, h2⟩ := CompanionTheory.RgDs.B.classUsed n ε lam hl
      exact ⟨G, i1, i2, π, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨ℂ, inferInstance, inferInstance, fun _ => 0, fun h => absurd h hl⟩
  choose G i1 i2 π hπ using key
  refine ⟨G, i1, i2, π, fun ε lam hl => (hπ ε lam hl).1, fun ε H' _ _ σ' hσ' => ?_⟩
  obtain ⟨s, mu, hm, hs, hds⟩ := hX n ε H' σ' hσ'
  exact ⟨s, mu, hm, hs, (hπ (ε ∘ s) mu hm).2 H' _ hds⟩

theorem discreteSeriesClassification_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.Published.DiscreteSeriesClassification :=
  GlobalTheory.Published.discreteSeriesClassification_iff.2 (dsClass_of hX)

theorem discreteSeriesCover_of (hX : GlobalTheory.Dec.DSExhaust) : GlobalTheory.Published.DiscreteSeriesCover :=
  GlobalTheory.T.discreteSeries_detSqrtCover_of_unitary_classification (discreteSeriesClassification_of hX)

end CompanionTheory.RgExh.Fin
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.DsExhaust

section

@[expose] public section

namespace CompanionTheory.RgExh

theorem dsExhaust : GlobalTheory.Dec.DSExhaust :=
  Fin.exhaustion_finite_length Hk.infinitesimal_character_shift Hk.hecke_algebra_exhaustion (Dec.decay_estimate Hk.infinitesimal_character_shift) U.far_regular_exhaustion

theorem discreteSeriesClassification : GlobalTheory.Published.DiscreteSeriesClassification :=
  Fin.discreteSeriesClassification_of dsExhaust

theorem discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover := Fin.discreteSeriesCover_of dsExhaust

end CompanionTheory.RgExh
end
end

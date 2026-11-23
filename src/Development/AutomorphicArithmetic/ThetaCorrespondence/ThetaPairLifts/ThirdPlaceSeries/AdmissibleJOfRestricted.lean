module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.RhoBar
public import Formalism.SharpRestriction.LevelLetterCocycles.AutomorphicSideWildInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisationsStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWildStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H1H2LocalDualityStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamPointsWeightJumps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisClauseOfSufficient
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisClauseOfSufficient
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SemisimpleOfFin
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  first | exact @GlobalTheory.OrthogonalDesignFromSize.main | exact GlobalTheory.OrthogonalDesignFromSize.main | (intros; apply GlobalTheory.OrthogonalDesignFromSize.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigPdHoldsTyz

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.TameEig
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
abbrev _root_.GlobalTheory.TameEig.eigPd_holds_tyz : Prop :=  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D → RbEx D → EigPd D
end GlobalTheory.TameEig
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigPdHolds

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
open GlobalTheory.TameEig
noncomputable section
namespace UpperTheory.GalS
theorem eigPd_holds_alt : _root_.GlobalTheory.TameEig.eigPd_holds_tyz := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := isoRep D hA.1 (_root_.UpperTheory.GalS.weak' hA.2.2.2.1) i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0
end UpperTheory.GalS
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.tame_descent_conditions_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  first | exact @GlobalTheory.TameDesign.main | exact GlobalTheory.TameDesign.main | (intros; apply GlobalTheory.TameDesign.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.NonCriticalLocalParamOfFullDim

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace UpperTheory.GalS

theorem nonCritical_localParam_of_full_dim (D : D7) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (i : D.nd.Loc) (P : D.naut.AV i) (w : PlE D.host) (hw : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i)
    (hA : w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde')))) (hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV) :
    Nc D.nd D.naut (D.naut.locV i P w) := by
  obtain ⟨hχ, hDel⟩ := (GlobalTheory.T.tame_descent_conditions_every_localisation D i).1
  obtain ⟨m, p⟩ := h4.1 i P w hw (hA.imp id fun h => ⟨hDel, h.2⟩)
  refine ⟨fun σ hσ hW => ?_, m, fun γ hγ z hz => ?_⟩
  · have e : chi1 D.nd i σ = 1 := by
      show ((D.nd.chi i 1 σ : (D.nd.O i)ˣ) : D.nd.O i) = 1
      rw [hχ w hA σ hW, Units.val_one]
    rw [p σ hσ, e, map_one, map_one, ← pow_add, hd]; rfl
  · have h1 : (D.naut.inePol (D.naut.locV i P w) γ).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
    rw [p γ hγ.1] at h1
    simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_C, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, one_pow]
    · have k := char_pow_ine (D.nd.plOm.2 w) (D.nd.chi i 1) (hχ w hA) γ hγ.1
      rw [sub_eq_zero.1 (pow_eq_zero_iff'.1 h1).1, ← map_pow]
      show iotaO D.nd D.naut i (((D.nd.chi i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) ^ _) = 1
      rw [← Units.val_pow_eq_pow_val, k, Units.val_one, map_one]

end UpperTheory.GalS
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LgcOfCut

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace UpperTheory.GalS
theorem lgc_of_cut'_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (hC : UpperTheory.GalC.CutRec D) : LGCN D := by
  intro i r hr w hw x
  have ht := hA.1
  have h1 := hA.2.2.1
  have h2 := _root_.UpperTheory.GalS.weak' hA.2.2.2.1
  have h5 := hA.2.2.2.2.2.2
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, -⟩ := isoRep D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hPa ρ hc hss hwd
  have hsp := D.nd.SQ_split i w hw
  have hwl := D.nd.SQ_l i w hw
  have rel : RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [← hPa.2.2.2.1 w hsp, ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w (Or.inl hwl)]
    exact hwd w hwl
  refine ⟨P, hP, rel, (nc_tw _ _).2 ?_⟩
  have hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV := by
    rw [← D.naut.lpDim_tw _ ((1 - (D.R.nV : ℝ)) / 2), ← rel.dim, D.naut.wdOf_dim]
  have hne : D.naut.ptV i P ≠ none := by rw [hP]; simp
  rcases hw with hS | hQ
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hC i P hne 0 w h
    · exact hC i P hne 1 w h
    · refine nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inl hS) (Or.inr ⟨hS, ?_⟩) hd
      split_ifs at h with he
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl h
  · exact nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inr hQ) (Or.inl hQ) hd
end UpperTheory.GalS
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted

section

@[expose] public section



section
noncomputable section
namespace UpperTheory.GalS
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC
theorem g3a_of_restricted_general_alt {D : D7} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r := h.2
theorem admJ_of_admPar (D : D7) (L : SizeData₂ D) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : CutRec D) (hW : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D) (hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D) (hP : AdmissibleParameterJ.AdmPar L) :
    _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L :=
  have hG := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h2 h5 hC
  ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, _root_.GlobalTheory.T.admDict_of_weight_blockChar GlobalTheory.Published.cheb_holds D h2 hW hB, GlobalTheory.T.hodgeTateJumpsReading_rowAdm D, hP⟩
theorem duties_of_large_aux41 (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hL : GlobalTheory.CoefDuty.Large D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hg : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D)
    (hRho : AutomorphicSideWildInertia.ResidualIrreducibleGood D) : GlobalTheory.CoefDuty.Duties D :=
  ⟨hL.1, fun i r hr => jc_of_u hr hL.2.1 (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hg i r hr), GlobalTheory.T.designConditionAll_of_cheb_of_takenAll hC D hL.2.2, GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive hC D hRho hL.2.2⟩
theorem prvG5_of_admissible_cutRec : LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → CutRec D → SumRepresentations.ConclusionG5 D := by
  intro h1 h2 h3 D hA hRb hC
  have hLGC : _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D := _root_.UpperTheory.GalS.lgc_of_cut'_alt D hA.1.1 hC
  have hEig : EigPd D := _root_.UpperTheory.GalS.eigPd_holds_alt D hA.1.1 hLGC hRb
  have hH : HOneTwo D := GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar h1 h2 h3 D
  refine _root_.Formalism.MainNotions.SumRepresentations.galois_clause_of_sufficient_alt D hA.1.1 fun i hg r hr w hw => ⟨hLGC i r hr w hw, fun hS => ⟨hRb i hg, fun rb hrb => ?_⟩⟩
  have hS' := (D.nd.S_def i w).1 hS
  have hnr : ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) := by
    have hk : ∀ k, w ∈ placesOver D.host.E (D.host.g k) → D.nd.l i ≠ D.host.g k :=
      fun k hk h => hS'.2 (h ▸ hk)
    rcases hS'.1 with h0 | h0 | h0
    · exact (hA.2.1 i hg rb hrb).2 0 (hk 0 h0) w h0
    · exact (hA.2.1 i hg rb hrb).2 1 (hk 1 h0) w h0
    · exact hEig i hg w hS h0 rb hrb
  exact ⟨hnr, hH i rb w hS hrb hnr⟩
end UpperTheory.GalS
end
end
end
end

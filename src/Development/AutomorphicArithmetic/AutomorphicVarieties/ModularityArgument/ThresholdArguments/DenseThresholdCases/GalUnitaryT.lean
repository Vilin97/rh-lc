module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTwT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.RecTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumHTAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Assemble
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuFrobTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuIrrCaseT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuProdT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSpehT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.HalfG

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Win.Gu.halfG :
    TwistLoc → PolG → HalfG := by
  intro hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) σ hσ
  have key : ∀ w (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc →
      rc (algNorm (σ w)) = (rc (cl (ρ w))).lpTw ((e : ℝ) / 2) := by
    intro w A h rc hrc
    obtain ⟨_, _, L⟩ := hrc
    rw [← L.nu]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  refine ⟨r, HT, ⟨hr.cont, hr.ss, fun w hg => hr.ht w fun A h rc hrc => ?_,
    fun w A h rc hrc => key w A h rc hrc ▸ hr.par w A h rc hrc⟩, fun τ => ?_⟩
  · have := hg A h rc hrc
    simp only [key w A h rc hrc]
    exact this
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumFamG

section

section

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Win.Gu.sumFamG :
    SumTwoG → SumRed → SumFamG := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = p 0 w A h rc := by
      intro w A h rc
      simp [sumList, WD.lpSum_zero]
    have e' : (fun τ => ∑ i, HT i τ) = HT 0 := by
      funext τ
      simp
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · rw [e']
      exact (H 0).ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact (H 0).par w A h rc hrc
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) =
        (p 0 w A h rc).lpSum (sumList (List.ofFn fun i : Fin (c + 1) => p i.succ w A h rc)) := by
      intro w A h rc
      rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    have e' : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
      funext τ
      rw [Fin.sum_univ_succ]
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ?_⟩
    · rw [e']
      exact hS.ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact hS.par w A h rc hrc
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuPolG

section

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT :
    _root_.UpperTheory.V.Af.HypothesesH' → RowT → PolG := by
  intro PH hRow E Ω _ _ _ _ _ _ l _ ι a ha P χ hreg hpol σ hσ
  obtain ⟨r, wt, HT, H⟩ := hRow E Ω l ι a ha P χ hreg
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a P (compNorm E χ) (PH.toClassicalTheorems.litN.aut.gk E a _) hpol.dual⟩
  have hRc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp H.cont
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w hg A h O _ _ _ Bw hj => ?_,
    fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj g => ?_⟩⟩, H.weights⟩
  · obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
    obtain ⟨g1, g2⟩ := hg A h rc hrc
    obtain ⟨k1, -, k3, -⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g1) g2
    exact ⟨k1, k3⟩
  · exact ⟨wdOf h hw ι r, isWDOf_wdOf hw ι hRc, fun g => (H.away w hw A h rc hrc (σ w) (hσ w)).tor g.1 g.2⟩
  · obtain ⟨-, k2, -, k4⟩ := (H.above (Loc.PP l) _ (Loc.tiedP l) w A h O Bw hj).nice (σ w) (hσ w) rc hrc (Or.inr g.1) g.2
    exact ⟨k2, k4.tor g.1 g.2⟩
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT

section

@[expose] public section




section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
namespace UpperTheory.V.Z.Win.Gu
theorem half_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) : HalfG := halfG UpperTheory.twist_local_components_compatible (_root_.UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT H hR)
theorem recTotT_of_printsH (H : _root_.UpperTheory.V.Af.HypothesesH') : RecTotT := recTotT (_root_.UpperTheory.V.Z.Win.Gu.prodT_alt H extraV) (_root_.UpperTheory.V.Z.Win.Gu.spehT_alt H extraV)
theorem galUnitaryT_of_printsH_of_bcSpeh_of_rT (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) : GalUnitaryT :=
  _root_.UpperTheory.V.Z.Win.Gu.assemble_s H hB (sumFamG (_root_.UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt H gdLaws UpperTheory.galoisRep_direct_sum_away_from_places sumHTAt) UpperTheory.finiteSum_reduction) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness
    (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems)) (_root_.UpperTheory.satake_galois_link_of_printed_hida H) UpperTheory.satake_parameters_complex_conjugate
    (_root_.UpperTheory.V.Z.Win.Gu.irrCaseT_alt H) plainGd
theorem endShapeT' (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) :
    type_of% (endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)) :=
  endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)
end UpperTheory.V.Z.Win.Gu
end
end
end

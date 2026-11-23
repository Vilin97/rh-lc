module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesCoverOfFactorsThroughCove
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesCoverOfFactorsThroughCoveStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_factors | exact GlobalTheory.CoverDS.hasTypes_of_factors | (intros; apply GlobalTheory.CoverDS.hasTypes_of_factors <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLe

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

namespace GlobalTheory.HwSpan

theorem eq_top_of_hwSub_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N →
    (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  intro p q M N hN hhw
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hfd, hvW, hW⟩ := M.kfin v
  have hle : W ≤ N := GlobalTheory.BlockReps.le_of_hw hL hW (fun x _ => M.wts x) hN
    (fun μ x _ hx => hhw μ hx.2)
  exact hle hvW

end GlobalTheory.HwSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KStableSubmoduleEqTopOfHighestWeightLeStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), KStable M.act N → (∀ μ, hwSub M.act μ ≤ N) → N = ⊤ := by
  first | exact @GlobalTheory.HwSpan.eq_top_of_hwSub_le | exact GlobalTheory.HwSpan.eq_top_of_hwSub_le | (intros; apply GlobalTheory.HwSpan.eq_top_of_hwSub_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwist

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoverDS.TwistTypes

variable {p q : ℕ}

theorem sum_rhoNC (lam : Ix p q → ℚ) : ∑ a, rhoNC lam a = 0 := by
  have symm : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have k1 : ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  have k2 : ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  simp only [rhoNC, Finset.sum_sub_distrib, ← Finset.sum_div, k1, k2, sub_self, zero_div]

theorem normSq_add_half (lam : Ix p q → ℚ) :
    normSq (fun a => lam a + 1 / 2) =
      normSq lam + ∑ a, (lam a + 1 / 2) - (Fintype.card (Ix p q) : ℚ) / 4 := by
  have e : ∀ a, (lam a + 1 / 2) ^ 2 = lam a ^ 2 + (lam a + 1 / 2) - 1 / 4 := fun a => by ring
  simp only [normSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casimir_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) :
    casimir (Cover.twAct act) v = casimir act v - act 1 v + ((Fintype.card (Ix p q) : ℂ) / 4) • v := by
  have hterm : ∀ a b, Cover.twAct act (Eab a b) (Cover.twAct act (Eab b a) v) =
      act (Eab a b) (act (Eab b a) v) - if a = b then act (Eab a a) v - (1 / 4 : ℂ) • v else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [Cover.twAct_apply, if_true, Eab, Matrix.trace_single_eq_same, map_sub, map_smul]
      module
    · simp [Cover.twAct_apply, hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab,
        Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  have h1 : act 1 v = ∑ a, act (Eab a a) v := by

    rw [← Matrix.sum_single_one, map_sum, LinearMap.sum_apply]
    rfl
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h1, Finset.sum_const, Finset.card_univ]
  module

theorem hwSub_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · exact ⟨fun h => ((Cover.isHW_twAct act μ v).1 ⟨hv, h⟩).2, fun h => ((Cover.isHW_twAct act μ v).2 ⟨hv, h⟩).2⟩

theorem sum_of_inCone {lam μ : Ix p q → ℚ} (h : InCone lam μ) : ∑ a, μ a = ∑ a, lam a := by
  obtain ⟨m, -, rfl⟩ := h
  have e : ∑ c, ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, e, blattner, sum_rhoNC, add_zero]

theorem inCone_add {lam μ : Ix p q → ℚ} (c : ℚ) (h : InCone lam fun a => μ a - c) :
    InCone (fun a => lam a + c) μ := by
  obtain ⟨m, hm, hμ⟩ := h
  refine ⟨m, fun a b hab => add_lt_add_left (hm a b hab) c, funext fun a => ?_⟩
  have := congrFun hμ a
  rw [Cover.blattner_add]
  simp only at this ⊢
  linarith

theorem hasTypes_of_twist (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ)
    (h : HasTypes (Cover.twist R) lam) : HasTypes R fun a => lam a + 1 / 2 := by
  have h1 : Module.finrank ℂ ↥(hwSub (Cover.twAct R.HK.act) (blattner lam)) = 1 := h.1
  have h2 : ∀ v, casimir (Cover.twAct R.HK.act) v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v := h.2.1
  have h3 : ∀ (μ : Ix p q → ℚ) v, IsHW (Cover.twAct R.HK.act) μ v → InCone lam μ := h.2.2
  have hcone : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (fun a => lam a + 1 / 2) μ := fun μ v hv =>
    inCone_add _ (h3 _ v ((Cover.isHW_twAct _ _ v).2 (by simpa only [sub_add_cancel] using hv)))
  refine ⟨by rwa [Cover.blattner_add, ← hwSub_twAct], fun v => ?_, hcone⟩
  set c : ℂ := ((∑ a, (lam a + 1 / 2) : ℚ) : ℂ) with hc
  have htop : LinearMap.ker (R.HK.act 1 - c • LinearMap.id) = ⊤ := by
    refine GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le p q R.HK _ (fun X _ w hw => ?_) fun μ w hw => ?_
    · have e := congrArg (fun f : Module.End ℂ R.HK.V => f w) (R.HK.lie X 1)
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply,
        Module.End.mul_apply] at e
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      rw [← sub_eq_zero.1 e.symm, hw, map_smul]
    · by_cases h0 : w = 0
      · rw [h0]
        exact Submodule.zero_mem _
      have e := sum_of_inCone (hcone μ w ⟨h0, hw⟩)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

      rw [hc, ← e, ← Matrix.sum_single_one, map_sum, LinearMap.sum_apply, Rat.cast_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => ((mem_hwSub_iff _ _ _).1 hw).1 a
  have hv : R.HK.act 1 v = c • v := by
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using Submodule.eq_top_iff'.1 htop v
  have e := casimir_twAct R.HK.act v
  rw [h2, hv] at e
  rw [normSq_add_half, Rat.cast_sub, Rat.cast_sub, Rat.cast_add, ← hc]
  rw [Rat.cast_sub] at e
  push_cast
  linear_combination (norm := module) -e

end GlobalTheory.CoverDS.TwistTypes

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwistStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist : ∀ (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), HasTypes (Cover.twist R) lam → HasTypes R fun a => lam a + 1 / 2 := by
  first | exact @GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | exact GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | (intros; apply GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCover

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_hasParam_of_group : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ),
      IsParam lam → HasParam R lam → HasTypes R lam := by
  intro hL hK hD p q hpq T R lam hlam hR
  have hn : 0 < p + q := hpq
  obtain ⟨P, e, -, hB, hcase⟩ := isParam_cases hlam
  rcases hcase with rfl | rfl
  · obtain ⟨σ, hf, hds⟩ := (hasParam_iff_factors R hn P hB).1 hR
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T R σ hB hf hds
  · obtain ⟨σ, hπ, hds⟩ := (hasParam_half_iff R hn P hB).1 hR
    have hf : Factors (Cover.twist R).U e σ := (factors_twist_iff R σ).2 hπ
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist p q T R (blockPar P e)
      (GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T (Cover.twist R) σ hB hf hds)

end GlobalTheory.CoverDS
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasTypes R lam := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | exact GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group | (intros; apply GlobalTheory.CoverDS.hasTypes_of_hasParam_of_group <;> assumption)
end
end

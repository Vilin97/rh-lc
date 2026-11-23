module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypeParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTupleStatement
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseForms
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.FinrankISupLeSum
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuples

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.NRows.LamUsedProof

theorem main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD μ hU0 i σ
  have hU : Used0 D μ := hU0
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hU⟩
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  by_cases hne : D.what₂.isot ((i : ℕ) + 1) σ = ⊥
  · refine ⟨fun f hf => ?_, fun h => absurd hne h⟩
    rw [hne, Submodule.mem_bot] at hf
    subst hf
    simp
  obtain ⟨p, hL⟩ := GlobalTheory.Mem.R3.LabProof.hasLab_exists h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD σ
  set c : ℝ := R.lam3 i t p A3.A.v0 with hc

  have hpre : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ, ∃ x ∈ (LinearMap.ker θ)ᗮ, θ x = y ∧
      ∀ x', ⟪θ x, θ x'⟫_ℂ = (c : ℂ) * ⟪x, x'⟫_ℂ := by
    intro y hy
    obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
    set K := (LinearMap.ker θ)ᗮ
    have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
      have := K.sub_starProjection_mem_orthogonal x
      rwa [Submodule.orthogonal_orthogonal] at this
    have he : θ (K.starProjection x) = θ x := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
    have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
      rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
    exact ⟨K.starProjection x, K.starProjection_apply_mem x, he,
      GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
        (K.starProjection_apply_mem x) hW⟩

  have heig : ∀ y ∈ D.what₂.isot ((i : ℕ) + 1) σ,
      D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.thetaT (Y.tup t) ((i : ℕ) + 1) y) = ((c : ℝ) : ℂ) • y := by
    intro y hy
    obtain ⟨x, -, rfl, hx⟩ := hpre y hy
    have ha : LinearMap.adjoint θ (θ x) = (c : ℂ) • x := by
      refine ext_inner_right ℂ fun x' => ?_
      rw [LinearMap.adjoint_inner_left, hx, inner_smul_left, Complex.conj_ofReal]
    show θ (LinearMap.adjoint θ (θ x)) = (c : ℂ) • θ x
    rw [ha, map_smul]
  have hlam : D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = c := Y.tied.lift.lamP (Y.tup t) hU i σ c hne heig
  refine ⟨fun f hf => by rw [hlam]; exact heig f hf, fun _ => ?_⟩
  rw [hlam]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨x, -, rfl, hx⟩ := hpre y hy
  have h := hx x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hyn : 0 < ‖θ x‖ := norm_pos_iff.2 hy0
  have h' : ‖θ x‖ ^ 2 = c * ‖x‖ ^ 2 := by
    have h2 : ((‖θ x‖ ^ 2 : ℝ) : ℂ) = ((c * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      first | (push_cast; exact h) | (push_cast; simpa using h) | (simp only [RCLike.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_mul] at h ⊢; exact h) | (rw [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_pow]; exact h)
    exact Complex.ofReal_injective h2
  by_contra hcn
  push_neg at hcn
  nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hyn]

end GlobalTheory.NRows.LamUsedProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownLiftUpLiftPositiveScalarUsedTuplesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.downLift_upLift_positiveScalar_usedTuples : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → GlobalTheory.NRows.LamUsed D := by
  first | exact @GlobalTheory.NRows.LamUsedProof.main | exact GlobalTheory.NRows.LamUsedProof.main | (intros; apply GlobalTheory.NRows.LamUsedProof.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypic

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.IsotSum



theorem span_all : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m), (⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) = ⊤ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    have hn : (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) *
        (((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) false)).ne', Complex.ofReal_one]
    have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.toRealDat.hv0
    have h1 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        ∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k) := by

      simp only [CxData.w0C, CxData.wC, lin, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
      rfl
    apply_fun (Tw.out (s := twAt D.what₂.embLL A3.A.v0))
    case inj =>
      intro a b h
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) h
    rw [h1]
    change Tw.out (∑ k, A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k)) = _
    change (∑ k, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) (A3.A.v0.embedding (y k) • (R.toCx3 F).eW false i ((R.toCx3 F).bW false i A3.A.v0 k))) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding (y k)) •
      ((((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) •
        (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k))) = _
    rw [smul_smul (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)), hn, one_smul, R.toRealDat.emb0, cj_cj]
    congr 1
    exact (DFunLike.congr_fun hs (y k)).symm
  have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
    have h2 : ‖d‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hnP.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i

  have hUT : ∀ p, Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) =
      (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
    intro p
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy, LinearMap.mem_range_self _ _⟩
    · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
        hR.liftHyp0.h3W hR.partsW i p]
      exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw (Submodule.span ℂ
        ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))) ((R.toCx3 F).WpK false i p)
        (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
  let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
    { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
      map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
      map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
  set S : Submodule ℂ (D.what₂.Mj ((i : ℕ) + 1)) :=
    ⨆ p, Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) with hS

  have h5 : ∀ p, (Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _))).map outL ≤
      S.map (Y.mj.eW i) := by
    intro p
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_map.2 ⟨Z.jW i y, ?_, ?_⟩
    · exact (le_iSup (fun p => Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) p)
        (Submodule.subset_span ⟨y, hy, rfl⟩)
    · show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
  rw [eq_top_iff]
  intro x _
  have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
    exact LinearMap.mem_range_self _ _
  have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
      Submodule.comap (Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H)
        (LinearMap.range ((R.toCx3 F).w0C false i)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ LinearMap.range ((R.toCx3 F).w0C false i) := hle hWS
  rw [← (hR.partsW i).2] at h1
  have h4 : Y.mj.eW i x ∈ (⨆ p, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL :=
    Submodule.mem_map_of_mem (f := outL) h1
  rw [Submodule.map_iSup] at h4
  have h6 : (⨆ p, ((R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i)).map outL) ≤ S.map (Y.mj.eW i) :=
    iSup_le fun p => (hUT p) ▸ h5 p
  obtain ⟨x', hx', hxx⟩ := h6 h4
  rw [← hinj hxx]
  exact hx'

end GlobalTheory.IsotSum

namespace GlobalTheory.IsotSum



theorem isotInternal_of_read : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hRk
  obtain ⟨cOf, h1, -, -⟩ := GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost hRk
  show Rows.IsotInternal D.what₂
  intro j hj1 hjm
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i
  · rw [eq_top_iff, ← span_all hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost i]
    refine iSup_le fun c => ?_
    rw [← (h1 i c).2]
    exact iSup_le fun σ => le_iSup (fun σ => D.what₂.isot ((i : ℕ) + 1) σ) σ.1

end GlobalTheory.IsotSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftFormsInternalDirectSumIsotypicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.thetaLift_forms_internal_direct_sum_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D := by
  first | exact @GlobalTheory.IsotSum.isotInternal_of_read | exact GlobalTheory.IsotSum.isotInternal_of_read | (intros; apply GlobalTheory.IsotSum.isotInternal_of_read <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLambdaAdicDecomposition

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.NRows.OverX

theorem lambdaAdic_components_over_base_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → OverRows fun _ _ _ _ w Z _ _ z p0 Y => ReadL z.R z.F p0 Y →
    (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  intro hN hPX
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo hEx _ hGrp _ hRd hp
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    rw [z.lev.C, w.C_eq]
    exact hGrp
  have hME := _root_.GlobalTheory.T.twisted_multiplicity_one hPX.ana hPX.dsc hN.decay hN.hc hPX.trc hPX.dm hPX.flath hN.zel
    hN.what₂.geo hN.greenC z.R z.F hHo.ok z.pins.char hEx hH hp B.ccK_top z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev hT)
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  exact ⟨GlobalTheory.T.thetaLift_forms_internal_direct_sum_isotypic hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH hIR,
    GlobalTheory.T.downLift_upLift_positiveScalar_usedTuples hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH⟩
end GlobalTheory.NRows.OverX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.adm8_and_lamUsed_of_readL_of_parameters : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → OverRows fun _ _ _ _ w Z _ _ z p0 Y => ReadL z.R z.F p0 Y → (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  first | exact @_root_.GlobalTheory.NRows.OverX.lambdaAdic_components_over_base_alt | exact _root_.GlobalTheory.NRows.OverX.lambdaAdic_components_over_base_alt | (intros; apply _root_.GlobalTheory.NRows.OverX.lambdaAdic_components_over_base_alt <;> assumption)
end
end
end
end

module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPair
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotLocallyFiniteQuadraticMulAddDegreeNonraising
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsItWOfGlobIt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrre
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsEqCoverDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPairStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.gridColumnParameters_negated_dataAR_pair : ∀ (D : D7) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ al be ga de : List ℚ,
    Formalism.MainNotions.SchurIrreducible.DataAR (GlobalTheory.Grid.sLen D - 1) al be ga de ∧
    GlobalTheory.Grid.parP D i τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
    GlobalTheory.Grid.parP D (i + 1) τ =
      dualPar (signed (al ++ block (GlobalTheory.Grid.sLen D - 1) ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) := by
  first | exact @GlobalTheory.NegPair.params | exact GlobalTheory.NegPair.params | (intros; apply GlobalTheory.NegPair.params <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValues

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.AdjSmooth

variable {D : D7}

theorem eq_zero_of_ellT_smooth {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (u : SmT M')
    (hu : ∀ v : M'.Vec, ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u) = 0) : u = 0 := by
  classical
  obtain ⟨F, hF, h⟩ := exists_finite_support u
  obtain ⟨y, rfl⟩ := h F fun _ => le_rfl
  let o := fun τ => stdOrthonormalBasis ℂ (F τ)
  let b := Basis.piTensorProduct fun τ => (o τ).toBasis
  have key : ∀ i, b.coord i = ellT M' (fun τ => (((o τ (i τ) : F τ) : M'.sm τ) : M'.H τ)) ∘ₗ inclT M' ∘ₗ
      PiTensorProduct.map fun τ => (F τ).subtype := by
    intro i
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, inclT, ellT_pure,
      Module.Basis.coord_apply, b]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [OrthonormalBasis.repr_apply_apply]
  have hy : y = 0 := by
    refine b.ext_elem fun i => ?_
    have h1 : b.coord i y = 0 := by
      rw [key]
      exact hu fun τ => (o τ (i τ) : M'.sm τ)
    change b.repr y i = b.repr 0 i
    rw [map_zero b.repr, Finsupp.zero_apply]
    exact h1
  rw [hy, map_zero]

end GlobalTheory.AdjSmooth

namespace GlobalTheory.AdjSmooth

open GlobalTheory.Chain.RealLine

variable {D : D7}

theorem exists_adj_glue {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W)
    (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hC : GlobalTheory.Published.DiscreteSeriesCover)
    (hH : GlobalTheory.Published.HarishChandraModules) (hθ : IsInfFam θ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ)))
    (hω : IsWeilExp ψ V W aS aT ω) (hf : IsVacVec ψ θ M M' f) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (Ps : D.what₂.Tau → LPol W.rank V.rank) (w : M.Vec) :
    ∃ u : SmT M', ∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It (glue Ps) (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u)) := by
  classical
  obtain ⟨X, hX, -, -, -, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hC hH
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hC hH D
  obtain ⟨χS, χT, hωd, he⟩ := hω
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hωd (he τ).1 (he τ).2 hf
  have key : ∀ τ, ∃ A₀ : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ,
      ∀ A, LocW M M' τ (aS τ) (aT τ) A → ∃ c : ℂ, A = c • A₀ := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact loc_line hX h3 hH hB M M' τ hd e1 e2
  choose A₀ hA₀ using key
  let Fn : (∀ τ, LPol W.rank V.rank × M'.sm τ × M.H τ) → ℂ := fun a => ellT M (fun τ => (a τ).2.2)
    (inclT M (It (glue fun τ => (a τ).1) (PiTensorProduct.tprod ℂ fun τ => (a τ).2.1)))
  have part : ∀ τ a, ∃ B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, LocW M M' τ (aS τ) (aT τ) B ∧
      ∀ x, Fn (Function.update a τ x) = ⟪x.2.2, B x.1 x.2.1⟫_ℂ := by
    intro τ a
    obtain ⟨A, hA, hA'⟩ := GlobalTheory.T.exists_realIntertwiner_contraction_one_place D V W _ _ M M' θ ψ ω f τ _ _ It hθ (hv τ).2.1 (hv τ).2.2 hI
      (fun ρ => (a ρ).2.1) (fun ρ => (a ρ).2.2)
    obtain ⟨j, hj⟩ := exists_ins (fun ρ => (a ρ).1) τ
    refine ⟨A ∘ₗ j, locW_of_semiW hA hj, fun x => ?_⟩
    rw [LinearMap.comp_apply, hA' (j x.1) x.2.1 x.2.2, hj]
    have h1 : (fun ρ => (Function.update a τ x ρ).2.2) = Function.update (fun ρ => (a ρ).2.2) τ x.2.2 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.2.2) a τ x ρ
    have h2 : (fun ρ => (Function.update a τ x ρ).1) = Function.update (fun ρ => (a ρ).1) τ x.1 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.1) a τ x ρ
    have h3 : (fun ρ => (Function.update a τ x ρ).2.1) = Function.update (fun ρ => (a ρ).2.1) τ x.2.1 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.2.1) a τ x ρ
    show ellT M (fun ρ => (Function.update a τ x ρ).2.2) (inclT M (It (glue fun ρ => (Function.update a τ x ρ).1)
      (PiTensorProduct.tprod ℂ fun ρ => (Function.update a τ x ρ).2.1))) = _
    rw [h1, h2, h3]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ a, Fn a = c * ∏ τ, ⟪(a τ).2.2, A₀ τ (a τ).1 (a τ).2.1⟫_ℂ := by
    refine eq_mul_prod_of_partial (fun τ x => ⟪x.2.2, A₀ τ x.1 x.2.1⟫_ℂ) Fn fun τ a => ?_
    obtain ⟨B, hB, hB'⟩ := part τ a
    obtain ⟨d, hd⟩ := hA₀ τ B hB
    exact ⟨d, fun x => by rw [hB', hd, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_right]⟩
  by_cases h0 : ∀ a, Fn a = 0
  · refine ⟨0, fun v => ?_⟩
    rw [map_zero, map_zero, map_zero]
    exact h0 fun τ => (Ps τ, v τ, (w τ : M.H τ))
  push_neg at h0
  obtain ⟨a₀, ha₀⟩ := h0
  have loc : ∀ τ, ∃ (K : ℂ) (B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), K ≠ 0 ∧
      LocW M M' τ (aS τ) (aT τ) B ∧
      ∀ x : LPol W.rank V.rank × M'.sm τ × M.H τ, K * ⟪x.2.2, A₀ τ x.1 x.2.1⟫_ℂ = ⟪x.2.2, B x.1 x.2.1⟫_ℂ := by
    intro τ
    obtain ⟨B, hB, hB'⟩ := part τ a₀
    have hpr : ∀ x, ∏ ρ ∈ Finset.univ.erase τ,
        ⟪(Function.update a₀ τ x ρ).2.2, A₀ ρ (Function.update a₀ τ x ρ).1 (Function.update a₀ τ x ρ).2.1⟫_ℂ =
        ∏ ρ ∈ Finset.univ.erase τ, ⟪(a₀ ρ).2.2, A₀ ρ (a₀ ρ).1 (a₀ ρ).2.1⟫_ℂ := fun x =>
      Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
    refine ⟨c * ∏ ρ ∈ Finset.univ.erase τ, ⟪(a₀ ρ).2.2, A₀ ρ (a₀ ρ).1 (a₀ ρ).2.1⟫_ℂ, B, ?_, hB, fun x => ?_⟩
    · intro hK
      apply ha₀
      rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_left_comm, hK, mul_zero]
    · rw [← hB', hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hpr, Function.update_self]
      ring
  choose K B hK hB hKB using loc
  have adj : ∀ τ, ∃ b : M'.sm τ, ∀ y : M'.sm τ,
      ⟪(w τ : M.H τ), B τ (Ps τ) y⟫_ℂ = ⟪(b : M'.H τ), (y : M'.H τ)⟫_ℂ := by
    intro τ
    obtain ⟨b, hbK, hb⟩ := (hB τ).kT (Ps τ) (w τ)
    exact ⟨⟨b, (GlobalTheory.KFinLoc.kFin_smooth_absIrr hH D W S' M' τ).1 hbK⟩, hb⟩
  choose b hb using adj
  refine ⟨conj (c * ∏ τ, (K τ)⁻¹) • PiTensorProduct.tprod ℂ b, fun v => ?_⟩
  have e1 := hc fun τ => (Ps τ, v τ, (w τ : M.H τ))
  have e2 : ∀ τ, ⟪(w τ : M.H τ), A₀ τ (Ps τ) (v τ)⟫_ℂ = (K τ)⁻¹ * ⟪(b τ : M'.H τ), (v τ : M'.H τ)⟫_ℂ := fun τ => by
    rw [← hb, ← hKB τ (Ps τ, v τ, (w τ : M.H τ)), inv_mul_cancel_left₀ (hK τ)]
  have e3 : ellT M (fun τ => (w τ : M.H τ)) (inclT M (It (glue Ps) (PiTensorProduct.tprod ℂ v))) =
      c * ∏ τ, ((K τ)⁻¹ * ⟪(b τ : M'.H τ), (v τ : M'.H τ)⟫_ℂ) := by
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ]
    exact e1
  rw [e3, map_smul, map_smul, inclT, PiTensorProduct.map_tprod, ellT_pure]
  simp [Finset.prod_mul_distrib, map_prod, inner_conj_symm, mul_assoc]

end GlobalTheory.AdjSmooth

namespace GlobalTheory.AdjSmooth

variable {D : D7}

theorem ellT_update_add {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ ρ, M.H ρ) (τ : D.what₂.Tau)
    (x y : M.H τ) (z : ⨂[ℂ] ρ, M.H ρ) [DecidableEq D.what₂.Tau] :
    ellT M (Function.update w τ (x + y)) z = ellT M (Function.update w τ x) z + ellT M (Function.update w τ y) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have e : ∀ u : M.H τ, (fun ρ => ⟪Function.update w τ u ρ, v ρ⟫_ℂ) =
        Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ := fun u =>
      funext fun ρ => Function.apply_update (fun ρ (a : M.H ρ) => ⟪a, v ρ⟫_ℂ) w τ u ρ
    have h := (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).map_update_add (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪x, v τ⟫_ℂ ⟪y, v τ⟫_ℂ
    simp only [map_smul, ellT_pure, smul_eq_mul]
    rw [← mul_add]
    congr 1
    have e2 : ∀ u : M.H τ, ∏ ρ, ⟪Function.update w τ u ρ, v ρ⟫_ℂ =
        MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ (Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ) := fun u => by
      rw [MultilinearMap.mkPiAlgebra_apply, ← e u]
    rw [e2, e2, e2, inner_add_left, h]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    ring

theorem ellT_update_smul {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ ρ, M.H ρ) (τ : D.what₂.Tau)
    (c : ℂ) (x : M.H τ) (z : ⨂[ℂ] ρ, M.H ρ) [DecidableEq D.what₂.Tau] :
    ellT M (Function.update w τ (c • x)) z = conj c * ellT M (Function.update w τ x) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have e : ∀ u : M.H τ, (fun ρ => ⟪Function.update w τ u ρ, v ρ⟫_ℂ) =
        Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ := fun u =>
      funext fun ρ => Function.apply_update (fun ρ (a : M.H ρ) => ⟪a, v ρ⟫_ℂ) w τ u ρ
    have h := (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).map_update_smul (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ (conj c) ⟪x, v τ⟫_ℂ
    simp only [map_smul, ellT_pure, smul_eq_mul]
    have e2 : ∀ u : M.H τ, ∏ ρ, ⟪Function.update w τ u ρ, v ρ⟫_ℂ =
        MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ (Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ) := fun u => by
      rw [MultilinearMap.mkPiAlgebra_apply, ← e u]
    rw [smul_eq_mul, smul_eq_mul] at h
    rw [e2, e2, inner_smul_left, h]
    simp only [RingHom.id_apply]
    ring
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb]
    ring

theorem coe_update {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : M.Vec) (τ : D.what₂.Tau) (x : M.sm τ)
    [DecidableEq D.what₂.Tau] :
    (fun ρ => ((Function.update w τ x ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (w ρ : M.H ρ)) τ (x : M.H τ) :=
  funext fun ρ => Function.apply_update (fun ρ (a : M.sm ρ) => (a : M.H ρ)) w τ x ρ

theorem adjoint_smooth : ∀ {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    IsInfFam θ →
    (∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) →
    IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ Tp : PolF D W.rank V.rank →ₗ⋆[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (P : PolF D W.rank V.rank) (v : M'.Vec) (w : M.Vec),
      ellT M (fun τ => w τ) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        starRingEnd ℂ (ellT M' (fun τ => v τ) (inclT M' (Tp P (PiTensorProduct.tprod ℂ w)))) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hC hH hθ hP hω hf hI
  classical
  have hE : ∀ (P : PolF D W.rank V.rank) (w : M.Vec), ∃ u : SmT M', ∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u)) := by
    intro P w
    have hP' : P ∈ Submodule.span ℂ
        (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) := by
      rw [(GlobalTheory.T.gluing_law_holds D V.rank W.rank).1]
      trivial
    induction hP' using Submodule.span_induction with
    | mem P hP' =>
      obtain ⟨Ps, rfl⟩ := hP'
      exact exists_adj_glue M M' θ ψ aS aT ω f It hC hH hθ hP hω hf hI Ps w
    | zero => exact ⟨0, fun v => by simp⟩
    | add P Q _ _ h1 h2 =>
      obtain ⟨u1, h1⟩ := h1
      obtain ⟨u2, h2⟩ := h2
      exact ⟨u1 + u2, fun v => by simp only [map_add (f := _), LinearMap.add_apply, h1, h2]⟩
    | smul c P _ h1 =>
      obtain ⟨u, hu⟩ := h1
      exact ⟨conj c • u, fun v => by
        simp only [map_smul, LinearMap.smul_apply, hu, smul_eq_mul, map_mul, Complex.conj_conj]⟩
  choose U hU using hE
  have char : ∀ P w u, (∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u))) → U P w = u := by
    intro P w u h
    refine sub_eq_zero.1 (eq_zero_of_ellT_smooth M' _ fun v => ?_)
    have e := (hU P w v).symm.trans (h v)
    rw [(starRingEnd ℂ).injective.eq_iff] at e
    rw [map_sub, map_sub, e, sub_self]
  let mm : PolF D W.rank V.rank → MultilinearMap (RingHom.id ℂ) (fun τ => M.sm τ) (SmT M') := fun P =>
    { toFun := U P
      map_update_add' := fun w τ x y => by
        refine char P _ _ fun v => ?_
        rw [coe_update, Submodule.coe_add, ellT_update_add, ← coe_update, ← coe_update, hU, hU, map_add (f := _), map_add (f := _),
          map_add]
      map_update_smul' := fun w τ c x => by
        refine char P _ _ fun v => ?_
        rw [coe_update, Submodule.coe_smul, ellT_update_smul, ← coe_update, hU, map_smul, map_smul, smul_eq_mul,
          map_mul]
        rfl }
  have hmm : ∀ P w, mm P w = U P w := fun _ _ => rfl
  refine ⟨{ toFun := fun P => PiTensorProduct.lift (mm P)
            map_add' := fun P Q => PiTensorProduct.ext (MultilinearMap.ext fun w => ?_)
            map_smul' := fun c P => PiTensorProduct.ext (MultilinearMap.ext fun w => ?_) }, fun P v w => ?_⟩
  · simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.add_apply, hmm]
    refine char _ _ _ fun v => ?_
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), map_add (f := _), hU, hU, map_add (f := _), map_add (f := _), map_add (f := _)]
  · simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.smul_apply, hmm,
      RingHom.id_apply]
    refine char _ _ _ fun v => ?_
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, hU, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul,
      Complex.conj_conj]
  · show _ = conj (ellT M' _ (inclT M' (PiTensorProduct.lift (mm P) (PiTensorProduct.tprod ℂ w))))
    rw [PiTensorProduct.lift.tprod, hmm]
    exact hU P w v

end GlobalTheory.AdjSmooth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValuesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.realIntertwiner_adjoint_smoothValues : ∀ {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    IsInfFam θ →
    (∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) →
    IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ Tp : PolF D W.rank V.rank →ₗ⋆[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (P : PolF D W.rank V.rank) (v : M'.Vec) (w : M.Vec),
      ellT M (fun τ => w τ) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        starRingEnd ℂ (ellT M' (fun τ => v τ) (inclT M' (Tp P (PiTensorProduct.tprod ℂ w)))) := by
  first | exact @GlobalTheory.AdjSmooth.adjoint_smooth | exact GlobalTheory.AdjSmooth.adjoint_smooth | (intros; apply GlobalTheory.AdjSmooth.adjoint_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

namespace GlobalTheory.DownArrow

theorem itPair_gen (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (hθ : IsInfFam θ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ ω f, IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

theorem down_intertwiner_adj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hC hgap G' W hW G hsp hch hag hcos i hi ω f hω hf
  have hθ : IsInfFam R.θ := hC.models.inf
  obtain ⟨ω₀, f₀, χ₀, e, hω₀, hχ₀, hf₀, htr⟩ :=
    GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint (G.P (i + 1)) (G.P i) R.ψ R.θ (G.chi (D.R.m - i)) ω f hθ hω hf
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have hexp : ∀ τ, HasInfExp D (G.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) :=
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ (fun τ => (GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (hch.tie _ hm1 hm2)).2 (hch.aux _ hm1 hm2).inf
  have hS : (G.P i).S = GlobalTheory.Grid.parP D i := (hsp.P i (by omega)).par
  have hS' : (G.P (i + 1)).S = GlobalTheory.Grid.parP D (i + 1) := (hsp.P (i + 1) (by omega)).par
  have hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      (G.P i).S τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
      (G.P (i + 1)).S τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) :=
    fun τ => by
      obtain ⟨al, be, ga, de, hd, e1, e2⟩ := GlobalTheory.T.gridColumnParameters_negated_dataAR_pair D i hi τ
      exact ⟨_, al, be, ga, de, hd, by rw [hS]; exact e1, by rw [hS']; exact e2⟩
  obtain ⟨It, -, hIt⟩ := itPair_gen hDC hHC (G.P i).M (G.P (i + 1)).M R.θ R.ψ
    (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) hθ hP
  have hωe : IsWeilExp R.ψ (G.P i).V (G.P (i + 1)).V (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) ω₀ :=
    ⟨χ₀, χ₀, hω₀, fun τ => ⟨hχ₀ τ _ (hexp τ), hχ₀ τ _ (hexp τ)⟩⟩
  have hI := hIt ω₀ f₀ hωe hf₀
  obtain ⟨Tp, hTp⟩ := GlobalTheory.T.realIntertwiner_adjoint_smoothValues (G.P i).M (G.P (i + 1)).M R.θ R.ψ _ _ ω₀ f₀ It hDC hHC hθ hP hωe hf₀ hI
  refine ⟨It ∘ₗ e.toLinearMap, Tp.comp e.toLinearMap, htr It hI, fun P v w => ?_⟩
  exact hTp (e P) v w

end GlobalTheory.DownArrow
end
end
end

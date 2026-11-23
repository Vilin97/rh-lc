module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisatiStatement
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)


theorem _root_.GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.OpenBaseDim.dim_eq | exact GlobalTheory.OpenBaseDim.dim_eq | (intros; apply GlobalTheory.OpenBaseDim.dim_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOnStatement

section

@[expose] public section

open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)


theorem _root_.GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn : ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W → DifferentiableOn ℂ g W → Set.InjOn g W → ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  first | exact @GlobalTheory.InjHol.exists_local_inverse_of_injOn | exact GlobalTheory.InjHol.exists_local_inverse_of_injOn | (intros; apply GlobalTheory.InjHol.exists_local_inverse_of_injOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w (hw : w ∈ W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source)) => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)


theorem _root_.GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  first | exact @GlobalTheory.LieBase.isHol_chart_framePt | exact GlobalTheory.LieBase.isHol_chart_framePt | (intros; apply GlobalTheory.LieBase.isHol_chart_framePt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloFrameChart

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.LieBase.HoloFrame

theorem exists_un : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (y : CxPts (genStr T.Z) σ), ¬ LiesIn y (genBd T.Z) → ∃ (k : U.Comp) (x : (U.X k).dom), cxPt T.Z (U.un k x) = y := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ r U hU y hy
  have hr : Set.range y.1 ⊆ Set.range T.Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact not_not.1 hy
  haveI := T.Z.jQ_open
  let xF := IsOpenImmersion.lift T.Z.jQ y.1 hr
  have hxF : xF ≫ T.Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, T.Z.jQ_over] at h2
    exact h2
  have hover : (xF ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs]
    exact GlobalTheory.ShFam.OpenReg.spMap_comp _ _
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ Limits.pullback.fst _ _ :=
    GlobalTheory.FlagTan.exists_frPt _ hover
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  refine ⟨k, f, ?_⟩
  rw [cxPt_congr hb.1.symm]
  refine Subtype.ext ?_
  show GlobalTheory.AllWt.ptF (S := CAt σ) z ≫ T.Z.jQ = y.1
  rw [← hxF]
  congr 1
  apply Limits.pullback.hom_ext
  · exact (ptF_fst z).trans hz
  · exact (ptF_snd z).trans hs.symm

theorem exists_holo_frame_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k : U.Comp) (Fr : V X.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (c'.e y), ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = cxOf e σ hj (c'.e.symm u) ∧ ∀ τ' a b, DifferentiableAt ℂ (fun u => mat (Fr u) τ' a b) u := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hjo hj y hy c' hyc
  have hnb : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro h
    have h1 : IsLocalRing.closedPoint ℂ ∈ y.1 ⁻¹ᵁ openPart j := hy (Set.mem_univ _)
    exact h1 h
  obtain ⟨k, x₀, hx₀⟩ := exists_un E H Dw l Xo c O β Y T σ _ U hU _ hnb
  have hn := GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj ⟨y, hy⟩ k
  obtain ⟨W, a, ψ, hWo, haW, hψd, hψh, hψa, hinj⟩ := GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation E H Dw l Xo c σ U hσ hU k x₀ X.dim hn
  obtain ⟨q, hOo, hq, hqd⟩ := GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj c' k X.dim W ψ hWo hψd hψh
  haveI := T.Z.jQ_open
  have hxeq : ∀ {z z' : FrPt Xo c (CAt σ)}, cxPt T.Z z = cxPt T.Z z' → z.x = z'.x := by
    intro z z' h
    have h1 : GlobalTheory.AllWt.ptF (S := CAt σ) z = GlobalTheory.AllWt.ptF (S := CAt σ) z' :=
      (cancel_mono T.Z.jQ).1 (congrArg Subtype.val h)
    rw [← ptF_fst z, h1, ptF_fst]
  have hcxinj : Function.Injective (cxOf e σ hj) := by
    intro y1 y2 h
    apply Subtype.ext
    exact (cancel_mono j).1 (congrArg Subtype.val h)
  have hya : cxOf e σ hj y = cxPt T.Z (U.un k ⟨ψ a, hψd a haW⟩) := hx₀.symm.trans (cxPt_congr (hψa _).symm)
  have haO : a ∈ {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := ⟨haW, hψd a haW, y, hyc, hya⟩
  have hqa : q a = y := hcxinj ((hq a haW _ ⟨y, hyc, hya⟩).2.trans hya.symm)
  have hinjg : Set.InjOn (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
    rintro w ⟨hw, hwd, hw'⟩ w' ⟨hw2, hwd', hw2'⟩ hg
    have h1 := hq w hw hwd hw'
    have h2 := hq w' hw2 hwd' hw2'
    have hqq : q w = q w' := c'.e.injOn h1.1 h2.1 hg
    refine hinj w hw w' hw2 hwd hwd' (hxeq ?_)
    rw [← h1.2, ← h2.2, hqq]
  obtain ⟨h, hev⟩ := GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn X.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show c'.e y = c'.e (q a) by rw [hqa]]
  filter_upwards [hev] with u ⟨⟨huW, hud, hux⟩, hgu, hdu⟩
  refine ⟨hψd _ huW, ?_, fun τ' i i' => ?_⟩
  · have h1 := hq _ huW (hψd _ huW) hux
    rw [← h1.2]
    congr 1
    exact (c'.e.left_inv h1.1).symm.trans (congrArg c'.e.symm hgu)
  · exact ((hψh τ' i i' _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

end GlobalTheory.LieBase.HoloFrame
end
end
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Mathlib.Algebra.Azumaya.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameChangeAlongAnalyticLiftStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLieEigenspaceFrameAtUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrame

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end SlopeTestRemainingChoices

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem exists_frame_of_tied (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hy : y.1 = spMap (Var.evStalk y) ≫ stalkPt X (under y) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm
  have hφ : σ = (Var.evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = Var.evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((Var.evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (Var.evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [hy]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (Var.evStalk y) hφ hx
  exact ⟨g, φ, fz, Var.evStalk y, hy, hc, hg⟩

end Frame

theorem eventually_frameAt_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU k X j f₀ Eb A₀ hj hji hT ψ hψ h v hv A hA
  classical
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) hp0 (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((GlobalTheory.TrueCx.TorHolo.differentiable_stdMat (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have key : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p),
      cxOf e σ hj (ψ v) = cxPt T.Z (U.un k (x (L v))) := by
    intro v hv
    have h1 := hψ (x (L v))
    have h2 : flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (x (L v)).1) = v := by
      show flat (domPt _ _ _ (stdFrame _ _ _ hp0 (unflat (L.symm (L v)))).1) = v
      rw [L.symm_apply_apply, domPt_stdFrame _ _ _ hp0 hv]
      rfl
    rw [h2] at h1
    exact h1
  have hcont : ContinuousOn (fun b => cxPt T.Z (U.un k (x b))) B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun W => ⟨?_, fun g => ?_⟩
    · have := (hY W 0).1.preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin _ → ℂ) ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ W} := ⟨v.2, hv⟩
      have hca := (((hY W g).2).differentiableAt (((hY W g).1).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hκ := isOpenEmbedding_cxOf e σ hj
  have hLB : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L v ∈ B := fun v hv => by
    show L.symm (L v) ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
    rwa [L.symm_apply_apply]
  have hψc : ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := by
    rw [hκ.isInducing.continuousOn_iff]
    exact (hcont.comp L.continuous.continuousOn hLB).congr fun v hv => key v hv
  have hc : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hψc.continuousAt (ho.mem_nhds hv)).comp (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  filter_upwards [hc.eventually (eventually_mem_frames hA)] with w hw
  exact exists_frame_of_tied hj hT _ hw

end GlobalTheory.UnifFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLieEigenspaceFrameAtUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology


theorem _root_.GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  first | exact @GlobalTheory.UnifFrame.eventually_frameAt_unif | exact GlobalTheory.UnifFrame.eventually_frameAt_unif | (intros; apply GlobalTheory.UnifFrame.eventually_frameAt_unif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainSectionFlatCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameLift

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ShFam.SecFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

theorem analyticAt_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) (v₀ : Tau × Fin j × Fin (r - j) → ℂ) :
    AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) v₀ := by
  have hM : ∀ c, AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) v₀ := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact analyticAt_const | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Tau × Fin j × Fin (r - j) => ℂ) _).analyticAt _
  simp only [mat_frameAt, Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (hM c)

end GlobalTheory.FrameLift


open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ShFam.SecFrame in
theorem GlobalTheory.FrameLift.exists_analytic_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  intro E _ _ _ p q n Xd hp h v hv
  refine ⟨fun w => frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w)), ?_, ?_, ?_⟩
  · rw [analyticAt_pi_iff]; intro τ
    rw [analyticAt_pi_iff]; intro a
    rw [analyticAt_pi_iff]; intro b
    have hL : AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v := (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v
    exact (GlobalTheory.FrameLift.analyticAt_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) τ a b
      (GlobalTheory.UnifDens.flatL h v)).comp hL
  · intro τ a b
    have e : (fun w => coW Xd (Nat.le_add_right p q)
        (frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w))) τ a b) =
        fun _ => (1 : Matrix (Fin p) (Fin p) ℂ) a b := by
      funext w; rw [(co_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) _ τ).1]
    rw [e]; exact analyticAt_const
  · have ho : IsOpen (DomFlat Xd.Ψ p (p + q - p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
    filter_upwards [(GlobalTheory.UnifDens.flatL h).continuous.continuousAt.preimage_mem_nhds (ho.mem_nhds hv)] with w hw
    refine ⟨frameAt_mem Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) hp hw, ?_⟩
    rw [domPt_frameAt]
    rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainSectionFlatCoordinatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology


theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  first | exact @GlobalTheory.FrameLift.exists_analytic_section | exact GlobalTheory.FrameLift.exists_analytic_section | (intros; apply GlobalTheory.FrameLift.exists_analytic_section <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationGramLocalHolomorphic

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.HodgeUnifFrame

theorem transpose_hermitian_gram_submatrix_bijection {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : n → m)
    (he : Function.Bijective e) (K G : Matrix m m ℂ) (W P : Matrix n n ℂ) (c : ℂ)
    (hG : G.submatrix e e = c • (Wᴴ * P * W)) :
    ((Kᴴ * G * K)ᵀ).submatrix e e = c • ((W * K.submatrix e e)ᵀ * Pᵀ * ((W * K.submatrix e e)ᵀ)ᴴ) := by
  have h1 : (Kᴴ * G * K).submatrix e e = (K.submatrix e e)ᴴ * G.submatrix e e * K.submatrix e e := by
    rw [Matrix.submatrix_mul _ _ _ e _ he, Matrix.submatrix_mul _ _ _ e _ he, Matrix.conjTranspose_submatrix]
  have h2 : ((Kᴴ * G * K)ᵀ).submatrix e e = ((Kᴴ * G * K).submatrix e e)ᵀ := by ext; rfl
  rw [h2, h1, hG]
  have h3 : ((W * K.submatrix e e)ᵀ)ᴴ = ((W * K.submatrix e e)ᴴ)ᵀ := by ext; rfl
  rw [h3]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem lieGram_unif_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA τ
  obtain ⟨hoi, -, hT⟩ := hL
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨s, hsa, hWa, hsev⟩ := GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates E Dw.p Dw.q X.dim (U.X k) hp h v hv
  obtain ⟨K, hKa, hKu, hKev⟩ := GlobalTheory.T.exists_holomorphic_frameChange_along_analyticLift E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA s hsa hsev
  have hex := GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU k τ with hτ'
  set ec : Fin Dw.p → Fin (Dw.mult τ.1) := Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm with hec
  have he : Function.Bijective ec := (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm).bijective
  refine ⟨2 * Real.pi, Real.two_pi_pos,
    fun w => (coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ' * (K w τ.1).submatrix ec ec)ᵀ, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.submatrix_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hWa τ' b i).mul (hKa τ.1 (ec i) (ec a))
  · obtain ⟨hs0, -⟩ := hsev.self_of_nhds
    rw [Matrix.det_transpose, Matrix.det_mul]
    refine (isUnit_coW (U.X k) _ hp hs0 τ').mul ?_
    have : (K v τ.1).submatrix ec ec = (K v τ.1).submatrix (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
      (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hKu τ.1
  · filter_upwards [hsev, hKev, hex] with w ⟨hs, hflat⟩ hKw ⟨g0, hg0⟩
    have hexw : ∃ g, FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := ⟨g0, hg0⟩
    rw [lieGram, dite_eq_left hexw]
    show (((hodgeMet T.Z U).gram _ hexw.choose τ.1)ᵀ).submatrix ec ec = _
    rw [hKw hs _ hexw.choose_spec (hodgeMet T.Z U) τ.1]
    have hG := GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU k ⟨s w, hs⟩ τ τ' rfl (Nat.le_add_right Dw.p Dw.q)
    have hz : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w) τ' = unflat (GlobalTheory.UnifDens.flatL h w) τ' := by
      rw [← hflat]; rfl
    have hG' : ((hodgeMet T.Z U).gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ.1).submatrix ec ec =
        ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ')ᴴ *
          (hP (unflat (GlobalTheory.UnifDens.flatL h w) τ'))⁻¹ * coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ') := by
      rw [← hz]; exact hG
    rw [transpose_hermitian_gram_submatrix_bijection ec he _ _ _ _ _ hG']

end GlobalTheory.HodgeUnifFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationGramLocalHolomorphicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix


theorem _root_.GlobalTheory.T.hodge_metric_uniformisation_gram_local_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  first | exact @GlobalTheory.HodgeUnifFrame.lieGram_unif_local | exact GlobalTheory.HodgeUnifFrame.lieGram_unif_local | (intros; apply GlobalTheory.HodgeUnifFrame.lieGram_unif_local <;> assumption)
end
end

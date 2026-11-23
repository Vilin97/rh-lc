module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteHolomorphicCoordinatesIndependentDiffereStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsCharStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChartStatement
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishes

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam

theorem mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  intro k _ Y p σ D U m f J h x hx
  have h1 := (ev_eq_zero_iff h hx).symm
  rw [LiesIn] at h1
  rw [h1, CxPts.ev_eq hx, map_prod, Finset.prod_eq_zero_iff]
  simp only [CxPts.ev_eq hx]

end GlobalTheory.ShFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  first | exact @GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | exact GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod | (intros; apply GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleChartHolomorphicCoordinateChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem valAt'_eq_ev {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {U : Y.Opens}
    {x : CxPts p σ} (h : x ∈ CxPts.ptsIn p σ U) (f : Γ(Y, U)) : valAt' x.1 U f = CxPts.ev p σ U f x := by
  rw [CxPts.ev_eq h, CxPts.evHom_eq_evalPt h, TangentOrigin.valAt'_eq_evalPt _ _ h]

theorem chart_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  intro k _ Y p n σ c ψ hψ hψs
  refine ⟨fun j V _ _ _ B x hB hx hm => ?_, fun U' f => ⟨?_, ?_⟩⟩
  · have hs : ∀ b ∈ B, x b ∈ c.e.source ∧ c.e (x b) ∈ ψ.source := fun b hb => by
      simpa [OpenPartialHomeomorph.trans_source] using hm hb
    have hco : ∀ a, DifferentiableOn ℂ (fun b => c.e (x b) a) B := fun a => by
      refine ((hx c.U (c.x a)).2.mono fun b hb => ⟨hb, c.source_subset (hs b hb).1⟩).congr fun b hb => ?_
      rw [c.apply_eq _ (hs b hb).1, valAt'_eq_ev (c.source_subset (hs b hb).1)]
    have hce : DifferentiableOn ℂ (fun b => c.e (x b)) B := differentiableOn_euclidean.2 hco
    have h2 : DifferentiableOn ℂ (fun b => ψ (c.e (x b))) B := hψ.comp hce fun b hb => (hs b hb).2
    exact differentiableOn_pi.1 h2 j
  · exact (c.e.trans ψ).continuousOn_symm.isOpen_inter_preimage (c.e.trans ψ).open_target
      (CxPts.isOpen_ptsIn U')
  · have hm : ∀ z ∈ {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'},
        z ∈ ψ.target ∧ ψ.symm z ∈ c.e.target ∧ c.e.symm (ψ.symm z) ∈ CxPts.ptsIn p σ U' := fun z hz => by
      have h1 := hz.1
      simp only [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at h1
      exact ⟨h1.1, h1.2, hz.2⟩
    have h2 : DifferentiableOn ℂ (CxPts.ev p σ U' f ∘ c.e.symm ∘ ψ.symm)
        {z ∈ (c.e.trans ψ).target | ⊤ ≤ ((c.e.trans ψ).symm z).1 ⁻¹ᵁ U'} :=
      (c.holo U' f).comp (hψs.mono fun z hz => (hm z hz).1) fun z hz => ⟨(hm z hz).2.1, (hm z hz).2.2⟩
    refine h2.congr fun z hz => ?_
    exact valAt'_eq_ev (hm z hz).2.2 f

end GlobalTheory.ShFam.Hor.LogCh
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleChartHolomorphicCoordinateChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.etaleChart_holomorphic_coordinate_change : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ)), DifferentiableOn ℂ ψ ψ.source → DifferentiableOn ℂ ψ.symm ψ.target → (∀ j, HolAlong (c.e.trans ψ).source fun x => (c.e.trans ψ) x j) ∧ IsHolTo (c.e.trans ψ).target (fun z => ((c.e.trans ψ).symm z).1) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.chart_change | exact GlobalTheory.ShFam.Hor.LogCh.chart_change | (intros; apply GlobalTheory.ShFam.Hor.LogCh.chart_change <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace SncChart

theorem linearIndependent_fderiv_params (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    [SmoothOfRelativeDimension n p] (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source)
    (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hR : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m
      (fun i => Y.presheaf.germ U.1 _ hy (f i))) :
    LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ U.1 (f i) ∘ c.e.symm) (c.e x₀)) := by
  rw [Fintype.linearIndependent_iff]
  intro l hl
  by_contra hne
  push_neg at hne
  have hl0 : l ≠ 0 := fun h => by obtain ⟨i, hi⟩ := hne; exact hi (congrFun h i)
  obtain ⟨δ, hc0, hlb, hne'⟩ := GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero k Y p n σ inferInstance x₀ U hy m f hR l hl0
  obtain ⟨v, hv⟩ := GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart k Y p n σ c x₀ hx U (CxPts.mem_ptsIn.2 hy) δ hc0 hlb
  apply hne'
  have := congrArg (fun F => F v) hl
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at this
  simpa [hv] using this

theorem exists_chart_of_fderiv (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source) (W : Y.Opens)
    (hW : x₀ ∈ CxPts.ptsIn p σ W) (a : ℕ) (g : Fin a → Γ(Y, W))
    (h0 : ∀ i, CxPts.ev p σ W (g i) x₀ = 0)
    (hli : LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ W (g i) ∘ c.e.symm) (c.e x₀))) :
    ∃ e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ), x₀ ∈ e.source ∧ e.source ⊆ CxPts.ptsIn p σ W ∧
      e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
      ∀ x ∈ e.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), e x j = CxPts.ev p σ W (g ⟨j, hj⟩) x := by
  let c' := c.restr (CxPts.ptsIn p σ W) (CxPts.isOpen_ptsIn W)
  have hx' : x₀ ∈ c'.e.source := ⟨hx, hW⟩
  let G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun i => CxPts.ev p σ W (g i) ∘ c.e.symm
  have hv0 : c.e x₀ ∈ c'.e.target := c'.e.map_source hx'
  have hG : ∀ i, DifferentiableOn ℂ (G i) c'.e.target := fun i =>
    (c.holo W (g i)).mono (fun v hv => ⟨hv.1, hv.2⟩)
  have hG0 : ∀ i, G i (c.e x₀) = 0 := by
    intro i
    simp only [G, Function.comp_apply, c.e.left_inv hx, h0]
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.complete_holomorphic_coordinates_independent_differentials n a (c.e x₀) c'.e.target G c'.e.open_target hv0 hG hG0 hli
  obtain ⟨hh, hs⟩ := GlobalTheory.T.etaleChart_holomorphic_coordinate_change k Y p n σ c' ψ h4 h5
  refine ⟨c'.e.trans ψ, ⟨hx', h1⟩, fun x hx => hx.1.2, h3, hh, hs, fun x hx j hj => ?_⟩
  have := h6 _ hx.2 j hj
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at this ⊢
  refine this.trans ?_
  simp only [G, Function.comp_apply]
  exact congrArg _ (c'.e.left_inv hx.1)

theorem exists_coords : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  intro k _ _ Y p n D σ hsm hsnc x₀
  haveI := hsm
  obtain ⟨-, U, hy, m, f, J, hR, hD⟩ := hsnc (x₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := n) (p := p) (σ := σ) x₀
  have hli := linearIndependent_fderiv_params k Y p n σ c x₀ hc U hy m f hR
  let ix : Fin J.card → Fin m := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hxU : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have h0 : ∀ i, CxPts.ev p σ U.1 (f (ix i)) x₀ = 0 := by
    intro i
    by_contra hne
    have hb := CxPts.mem_ptsIn.1 ((CxPts.mem_ptsIn_basicOpen hxU (f (ix i))).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hy] at hb
    have hmem : Y.presheaf.germ U.1 _ hy (f (ix i)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨ix i, rfl⟩
    exact hmem hb
  have hli' := hli.comp ix hix
  have hcard : J.card ≤ n := by
    have := hli'.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V n) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, he0, hhol, hsymm, hev⟩ :=
    exists_chart_of_fderiv k Y p n σ c x₀ hc U.1 hxU J.card (fun i => f (ix i)) h0 hli'
  refine ⟨J.card, e, hx0, he0, hhol, hsymm, fun x hx => ?_⟩
  rw [GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes k Y p σ D U m f J hD x (hsub hx)]
  constructor
  · intro h j hj he
    exact h ⟨ix ⟨j, hj⟩, (J.equivFin.symm _).2, by rw [← hev x hx j hj]; exact he⟩
  · rintro h ⟨i, hi, hi0⟩
    have ht : ix (J.equivFin ⟨i, hi⟩) = i := by simp [ix]
    have hlt : ((J.equivFin ⟨i, hi⟩ : Fin J.card) : ℕ) < n := lt_of_lt_of_le (Fin.isLt _) hcard
    refine h ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt ?_
    rw [hev x hx ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt]
    simpa [ht] using hi0

end SncChart
end GlobalTheory
end
end
end

module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicEigenFrameDirsInExpChartStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibre
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChartStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGramStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSummaStatement
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts


theorem _root_.GlobalTheory.T.exists_holomorphicChart_of_expChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  first | exact @GlobalTheory.LieBase.exists_holoChart_of_expChart | exact GlobalTheory.LieBase.exists_holoChart_of_expChart | (intros; apply GlobalTheory.LieBase.exists_holoChart_of_expChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts


theorem _root_.GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  first | exact @GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge | exact GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge | (intros; apply GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

theorem gram_entry {m m' g : ℕ} (R : Matrix (Fin m) (Fin g) ℂ) (R' : Matrix (Fin m') (Fin g) ℂ)
    (M : Matrix (Fin g) (Fin g) ℂ) (s t : ℂ) (b : Fin m) (b' : Fin m') :
    ((s • R) * M * (t • R')ᴴ) b b' = s * star t * hermForm M (R b) (R' b') := by
  simp only [hermForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mem_openPart_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) (z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ Inner (cxOf e σ hj z) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj z
  rw [mem_ptsIn]
  exact Iff.rfl


open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem periodChart_rescale : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (r : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → 0 < r → r ≤ 1 → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ u : Fin n → ℂ, (∀ i : Fin a, u (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (r • u) + ∑ i, (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B u = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (r • u) := by
  intro n a ha g rk τ₀ B r hP hr hr1
  set cst : ℂ := (((Real.log r : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log r / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log r / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hP.psd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, r • z ∈ polydisc n 1 := fun z hz k => by
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hr.le]
    calc r * ‖z k‖ ≤ 1 * ‖z k‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hz k
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => r • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (r : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hP.rk_le, fun j k => ?_, fun z hz => ?_, hP.psd, hP.supp, hP.toric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hP.holo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hP.symm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := hP.abelian _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hP.supp _ j k (Or.inl hj)]
  · ext j k
    have hu' : ∀ i : Fin a, tlog ((r • u) (Fin.castLE ha i)) = -Real.log r / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg hr.le,
        Real.log_mul hr.ne' (norm_ne_zero_iff.2 (hu i))]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    ring

theorem exists_hodge_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), y ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∃ (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)) (a : ℕ) (ha : a ≤ X.dim) (g rk : ℕ) (τ₀ : (Fin X.dim → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ (∀ z ∈ ch.source, z ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ∃ i : Fin a, ch z (Fin.castLE ha i) = 0) ∧ ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ, (∀ τ i k, DifferentiableOn ℂ (fun w => Q τ w i k) (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1)) ∧ Fintype.card (Σ τ, Fin (Dw.mult τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q p.1 0 p.2) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ, lieGram e U hj f₀ A₀ A z τ = Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ (ch z).ofLp)ᴴ) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ τ', τ ≠ τ' → Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ' (ch z).ofLp)ᴴ = 0) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, κ, hP, hE, hx₀, h0, hcard, hκ, hInner, hHodge⟩ :=
    GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre E H Dw l Xo c O β Y T σ U hσ hU (cxOf e σ hj y)
  obtain ⟨A, hA, r, hr, W, hWd, hWli, hWfr⟩ :=
    GlobalTheory.T.exists_holomorphic_eigenFrame_dirs_in_expChart E H Dw l Xo c O β Y T F e σ C X j f f₀ Eb A₀ hj hL y n g ch₀ ex hE hx₀ h0
  obtain ⟨hn, r', ch, hr', hr'r, hr'1, hHolo, hy', hch0, hpoly, hrel⟩ :=
    GlobalTheory.T.exists_holomorphicChart_of_expChart_genericFibre E H Dw l Xo c O β Y T F e σ X j hj hL.1 y n g ch₀ ex hE hx₀ h0 r hr
  subst hn
  have hrel' : ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = r' • (ch z).ofLp := by
    intro z hz
    refine ⟨(hrel z hz).1, ?_⟩
    rw [(hrel z hz).2]
    try (funext k; simp [Complex.real_smul])
  obtain ⟨hP1, hY⟩ := periodChart_rescale X.dim a ha g rk τ₀ B r' hP hr' hr'1.le
  have hr'0 : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'.ne'
  have hball : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1, r' • u ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr'.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc r' * ‖u‖ ≤ r' * 1 := by gcongr
      _ < r := by linarith
  have hnz : ∀ z ∈ ch.source, Inner (cxOf e σ hj z) → ∀ i : Fin a, (ch z).ofLp (Fin.castLE ha i) ≠ 0 := by
    intro z hz hI i h
    have := ((hInner _ (hrel' z hz).1).1 hI) i
    rw [(hrel' z hz).2, Pi.smul_apply, h, smul_zero] at this
    exact this rfl
  let Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u =>
    ((Real.sqrt (κ τ) : ℝ) : ℂ) • Matrix.of fun b k => W (r' • u) ⟨τ, b⟩ k
  refine ⟨ch, a, ha, g, rk, _, B, hP1, hHolo, hy', hch0, hpoly, ?_, A, hA, Q, ?_, hcard, ?_, ?_, ?_⟩
  · intro z hz
    rw [mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z, hInner _ (hrel' z hz).1, (hrel' z hz).2]
    simp only [Pi.smul_apply, ne_eq, not_forall, not_not]
    refine exists_congr fun i => ?_
    rw [smul_eq_zero, or_iff_right hr'.ne']
    try rfl
  · intro τ i k
    have hd := (hWd ⟨τ, i⟩ k).comp (f := fun u : Fin X.dim → ℂ => r' • u)
      ((differentiable_id.const_smul (r' : ℂ)).differentiableOn.congr fun u _ => by
        simp [Complex.real_smul, Pi.smul_def]) (fun u hu => hball u hu)
    exact (hd.const_mul ((Real.sqrt (κ τ) : ℝ) : ℂ)).congr fun u _ => by simp [Q]
  · have hW0 : (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => Q p.1 0 p.2) =
        (fun p => Units.mk0 (((Real.sqrt (κ p.1) : ℝ) : ℂ))
          (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hκ p.1)).ne') • W 0 p) := by
      funext p k
      simp [Q]
    rw [hW0]
    exact hWli.units_smul _
  · intro z hz hzO τ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    unfold lieGram
    rw [dite_eq_left hex]
    obtain ⟨hgram, -⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hgram τ, hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Q]
    rw [← (hrel' z hz).2]
    simp only [Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hκ τ).le]
    rfl
  · intro z hz hzO τ τ' hττ
    have hI : Inner (cxOf e σ hj z) := (mem_openPart_iff E H Dw l Xo c O β Y T F e σ X j hj z).1 hzO
    have hb : ch₀ (cxOf e σ hj z) ∈ Metric.ball (0 : Fin X.dim → ℂ) r := by
      rw [(hrel' z hz).2]; exact hball _ (hpoly z hz)
    obtain ⟨hex, hDirs⟩ := hWfr z (hrel' z hz).1 hb
    obtain ⟨-, horth⟩ := hHodge _ (hrel' z hz).1 hI hex.choose _ (hDirs _ hex.choose_spec)
    rw [hY _ (hnz z hz hI), ← (hrel' z hz).2]
    ext b b'
    rw [gram_entry]
    have h1 := horth ⟨τ, b⟩ ⟨τ', b'⟩ hττ
    simp only [Matrix.zero_apply]
    rw [← (hrel' z hz).2]
    exact mul_eq_zero_of_right _ h1

end GlobalTheory.LieBase.HodgeChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

theorem _root_.GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), y ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∃ (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)) (a : ℕ) (ha : a ≤ X.dim) (g rk : ℕ) (τ₀ : (Fin X.dim → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ (∀ z ∈ ch.source, z ∉ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ∃ i : Fin a, ch z (Fin.castLE ha i) = 0) ∧ ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ Q : ∀ τ : E →+* ℂ, (Fin X.dim → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ, (∀ τ i k, DifferentiableOn ℂ (fun w => Q τ w i k) (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1)) ∧ Fintype.card (Σ τ, Fin (Dw.mult τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q p.1 0 p.2) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ, lieGram e U hj f₀ A₀ A z τ = Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ (ch z).ofLp)ᴴ) ∧ (∀ z ∈ ch.source, z ∈ GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j) → ∀ τ τ', τ ≠ τ' → Q τ (ch z).ofLp * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch z).ofLp)⁻¹ * (Q τ' (ch z).ofLp)ᴴ = 0) := by
  first | exact @GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart | exact GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart | (intros; apply GlobalTheory.LieBase.HodgeChart.exists_hodge_period_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumford

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumfordStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  exact @GlobalTheory.LieBaseGood.lieGram_isGood
end
end

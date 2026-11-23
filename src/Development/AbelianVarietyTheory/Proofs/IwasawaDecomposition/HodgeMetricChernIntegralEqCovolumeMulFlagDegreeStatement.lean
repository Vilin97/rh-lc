module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolumeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointwiseHodge

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory

theorem iSup_measure_apply_eq_zero {α κ : Type*} [MeasurableSpace α] (μ : κ → Measure α) {S : Set α}
    (hS : MeasurableSet S) (h : ∀ i, μ i S = 0) : (⨆ i, μ i) S = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => ?_
    calc μ i = (μ i).restrict Sᶜ :=
          (Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 (h i))).symm
      _ ≤ (⨆ i, μ i).restrict Sᶜ := Measure.restrict_mono subset_rfl (le_iSup μ i)
  refine le_antisymm ?_ (zero_le)
  calc (⨆ i, μ i) S ≤ (⨆ i, μ i).restrict Sᶜ S := Measure.le_iff'.1 hle S
    _ = 0 := by rw [Measure.restrict_apply hS, Set.inter_compl_self, measure_empty]

theorem chernTopPart_neg_eq_zero_of_nonneg {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R : MvPolynomial (ι × ℕ) ℝ)
    (h : ∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) :
    chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  unfold chernTopPart glueMeas
  refine iSup_measure_apply_eq_zero _ hS fun c => ?_
  rw [chartMeas_apply c.e _ hS]
  have hm : MeasurableSet (c.e '' (c.e.source ∩ ptsIn X.str σ O)) :=
    measurableSet_image c.e (c.e.open_source.measurableSet.inter hS) Set.inter_subset_left
  rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
  rintro _ ⟨y, ⟨hys, hyS⟩, rfl⟩
  have hz : c.e.symm (c.e y) ∈ c.e.source ∩ ptsIn X.str σ O := by
    rw [c.e.left_inv hys]; exact ⟨hys, hyS⟩
  beta_reduce
  generalize c.e.symm (c.e y) = z at hz ⊢
  apply ENNReal.ofReal_eq_zero.2
  have := h z hz.2 c hz.1 _ (E.nonempty (under z)).choose_spec
  push_cast
  linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopFormNegativePartEqZeroOfNonnegOnOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric


theorem _root_.GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ), (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y), 0 ≤ chernTop R (fun w => H A (c.e.symm w)) (c.e y)) → chernTopPart E H R (-1) (ptsIn X.str σ O) = 0 := by
  first | exact @GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | exact GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg | (intros; apply GlobalTheory.chernTopPart_neg_eq_zero_of_nonneg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralPointPolyCovol

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_pointPoly_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw) (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have h0 := GlobalTheory.T.chernTopForm_negativePart_eq_zero_of_nonneg_on_open Eb (openPart j) (lieGram e U hj f₀ A₀) (pointPoly H Dw)
    (GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL)
  have h1 := GlobalTheory.T.hodgeMetric_pointClassForm_mass_eq_covolume E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL
  have hc := (GlobalTheory.TrueCx.covol_pos (U.X k)).le
  refine ⟨fun ε => ?_, ?_⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [h1]; exact ENNReal.ofReal_ne_top
    · rw [h0]; exact ENNReal.zero_ne_top
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, h1, h0, ENNReal.toReal_ofReal hc]; simp

end GlobalTheory.LieBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_covol_flagDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL la R hR
  have h3 := GlobalTheory.LieBase.hasChernIntegral_pointPoly_covol E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have h := GlobalTheory.GoodMetric.hasChernIntegral_of_eq_mul Eb (openPart j) (lieGram e U hj f₀ A₀) R (pointPoly H Dw) _
    (GlobalTheory.TrueCx.covol (U.X k))
    (fun y hy c' hc A hA => GlobalTheory.PointHodge.pointwise_hodge E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
      la R hR y hy c' hc A hA) h3
  rw [mul_comm] at h
  convert h using 3

end GlobalTheory.LieBase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.hodgeMetric_chernIntegral_eq_covolume_mul_flagDegree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  first | exact @GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg | exact GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg | (intros; apply GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg <;> assumption)
end
end

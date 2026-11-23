module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLeStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

open scoped Matrix

namespace GlobalTheory.ArcGenBound

open Matrix

theorem affine_pos {T a b c : ℝ} (h : ∀ x s : ℝ, T < s → 0 < a + x * b + s * c) : b = 0 ∧ 0 ≤ c := by
  have h1 := h 0 (T + 1) (by linarith)
  constructor
  · by_contra hb
    have := h (-(a + (T + 1) * c) / b) (T + 1) (by linarith)
    rw [div_mul_cancel₀ _ hb] at this
    linarith
  · by_contra hc
    have hc' : 0 < -c := by linarith [not_le.1 hc]
    have hd : 0 < (a + (T + 1) * c) / (-c) := div_pos (by linarith) hc'
    have := h 0 (T + 1 + (a + (T + 1) * c) / (-c)) (by linarith)
    have e := div_mul_cancel₀ (a + (T + 1) * c) hc'.ne'
    nlinarith

theorem det_im_lower_bound {g : ℕ} (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (T : ℝ) (A B : Matrix (Fin g) (Fin g) ℂ)
    (haff : ∀ w, τ w = A + w • B) (hpos : ∀ w : ℂ, T < w.im → ((τ w).map Complex.im).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, T + 1 < w.im → C ≤ ((τ w).map Complex.im).det := by
  have hq : ∀ (w : ℂ) (v : Fin g → ℝ), v ⬝ᵥ ((τ w).map Complex.im) *ᵥ v = v ⬝ᵥ (A.map Complex.im) *ᵥ v +
      w.re * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + w.im * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := by
    intro w v
    have e : (τ w).map Complex.im = A.map Complex.im + w.re • B.map Complex.im + w.im • B.map Complex.re := by
      ext i j
      simp [haff, add_assoc]
    rw [e]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h0 : T < (⟨0, T + 1⟩ : ℂ).im := by simp
  refine ⟨((τ ⟨0, T + 1⟩).map Complex.im).det, (hpos _ h0).det_pos, fun w hw => ?_⟩
  have hw' : T < w.im := by linarith
  have hD : ((τ w).map Complex.im - (τ ⟨0, T + 1⟩).map Complex.im).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hpos w hw').isHermitian.sub (hpos _ h0).isHermitian) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hp : ∀ x s : ℝ, T < s → 0 < v ⬝ᵥ (A.map Complex.im) *ᵥ v +
        x * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + s * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := fun x s hs => by
      have := (hpos ⟨x, s⟩ hs).dotProduct_mulVec_pos hv
      rwa [star_trivial, hq] at this
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq, hq]
    obtain ⟨hb, hc⟩ := affine_pos hp
    have := mul_nonneg (sub_pos.2 hw).le hc
    rw [hb]
    dsimp only
    linarith
  have := GlobalTheory.ClassFin.gramLB_det_mono (hpos _ h0) hD
  rwa [add_sub_cancel] at this

end GlobalTheory.ArcGenBound


open GlobalTheory.ArcGenBound in
theorem GlobalTheory.ArcGenBound.gen_ratio_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z _ _ _
  have haff : ∀ w, Θ.τ w = Matrix.of (fun i k => (Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) i) +
      w • Matrix.of (fun i k => (Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) i) := by
    intro w
    ext i k
    have e := congrFun (Θ.per w k).2 i
    rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e
    simpa [Matrix.transpose_apply] using e.symm
  obtain ⟨C, hC, hdet⟩ := det_im_lower_bound Θ.τ Ha.T _ _ haff (fun w hw => (Θ.pos w hw).2)
  refine ⟨Ha.T + 1, Real.sqrt (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ Uw.g * C))⁻¹), ?_⟩
  intro w hw yw hA k x t hx hb
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨hLie, hGen⟩ := hA
  have V1 := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W Uw.g _ Uw.F Ha th Θ w yw hw' hLie.1 hGen
  have V2 := Uw.norm k x hx
  obtain ⟨G, -, -, hchg⟩ := (GlobalTheory.Frames.frBor_iff_frChg _ _ _).1 hb
  have hs := (GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 E H Dw l Xo c
    σ Uw.g _ Uw.F (Uw.ik k) Ha.i (Uw.Pm k x) (Ha.Pw w) (U.un k x) yw G (t none : CAt σ) 1 _ (Uw.period k x)
    (Ha.period w hw') (Uw.lie k x).1 hLie.1 hchg V2 V1).2
  rw [mul_one] at hs
  apply Real.le_sqrt_of_sq_le
  rw [← hs]
  have hd := hdet w hw
  have h2 : (0 : ℝ) < 2 ^ Uw.g := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos h2 hC)) (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd h2.le))
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arc_generator_ratio_bounded_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  first | exact @GlobalTheory.ArcGenBound.gen_ratio_bounded | exact GlobalTheory.ArcGenBound.gen_ratio_bounded | (intros; apply GlobalTheory.ArcGenBound.gen_ratio_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArc

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArcBdd

theorem norm_prod_pow_le {ι : Type} [Fintype ι] (f : ι → ℂ) (e : ι → ℕ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∏ i, f i ^ e i‖ ≤ B ^ (∑ i, e i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hf i) _

theorem pnorm_unitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (hx : GlobalTheory.FrameNorm.IsUnitFr X x) :
    X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, hx τ i.succ, hx τ i.castSucc, div_one]
  simp only [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem holSub_bdd {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : (k : Comp) → Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X)
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) :
    ∃ C : ℝ, ∀ x ∈ (X k).dom, (X k).pnorm (la k) (P k) x ≤ C := by
  unfold Formalism.L2.PjFree.holSub at hP
  induction hP using Submodule.span_induction with
  | mem P hP => exact (hP k).1.2
  | zero => exact ⟨0, fun x _ => by
      have := Formalism.L2.Pj.pnorm_zero (X k) (la k) x
      simpa using this.le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨C1, h1⟩ := hP
    obtain ⟨C2, h2⟩ := hQ
    exact ⟨C1 + C2, fun x hx => (Formalism.L2.Pj.pnorm_add_le (X k) (la k) (P k) (Q k) x).trans (add_le_add (h1 x hx) (h2 x hx))⟩
  | smul s P _ hP =>
    obtain ⟨C1, h1⟩ := hP
    exact ⟨‖s‖ * C1, fun x hx => by
      have := Formalism.L2.Pj.pnorm_smul (X k) (la k) s (P k) x
      simp only [Pi.smul_apply] at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1 x hx) (norm_nonneg _)⟩

theorem cusp_bounded_at_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Formalism.L2.PjFree.GoodEmb c σ → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ M : ℝ, ∀ (k : (U σ).Comp) (x : ((U σ).X k).dom), GlobalTheory.FrameNorm.IsUnitFr ((U σ).X k) x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x))‖ ≤ M := by
  intro E _ _ _ H Dw l Xo c r U σ a' n F hG hF
  haveI := (U σ).fin
  have hF' : Formalism.L2.PjFree.rdU (U σ) F ∈ Formalism.L2.PjFree.holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) := by
    unfold Formalism.L2.PjFree.cusp at hF
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hF
    have := hF.2 σ
    rw [Submodule.mem_iInf] at this
    exact Submodule.mem_comap.mp (this hG)
  choose C hC using holSub_bdd (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) _ hF'
  refine ⟨∑ k, max (C k) 0, fun k x hx => ?_⟩
  have h1 := hC k x.1 x.2
  rw [pnorm_unitFr _ _ _ _ hx] at h1
  have h2 : Formalism.L2.PjFree.rdU (U σ) F k x.1 = Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) := by
    simp [Formalism.L2.PjFree.rdU, x.2]
  rw [← h2]
  refine h1.trans ((le_max_left (C k) 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (C k) 0) (fun k _ => le_max_right _ _) (Finset.mem_univ k)

theorem cusp_values_bounded_on_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c r U σ Uw _ _ O _ β Y a χ W Ha th Θ z hU hG hz a' n F hD hF
  obtain ⟨T1, B1, h1⟩ := GlobalTheory.T.norm_diag_tangent_unitFrame_holomorphicArc_le E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨T2, B2, h2⟩ := GlobalTheory.T.arc_generator_ratio_bounded_unit_frame E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨M, hM⟩ := cusp_bounded_at_unitFr E H Dw l Xo c r U σ a' n F hG hF
  have hev : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c, hwt, hbc⟩
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  set B := max 1 (max B1 B2)
  refine ⟨max T1 T2, max M 0 * B ^ (∑ i, ex Dw a' n i), ?_⟩
  intro w hw yw hyw
  obtain ⟨k, x, t, hux, hb⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hG (hU σ hG)).2 yw
  have hsc := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a' n F (Formalism.L2.PjFree.cusp_le_sec Xo c U a' n hF) (CAt σ)).2 inferInstance).1 t _ _ hb
  have ht : ∀ i, ‖Formalism.L2.PjFree.toC (t i : CAt σ)‖ ≤ B := by
    intro i
    rcases i with _ | j
    · exact (h2 w (lt_of_le_of_lt (le_max_right _ _) hw) yw hyw k x t hux hb).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 w (lt_of_le_of_lt (le_max_left _ _) hw) yw hyw k x t hux hb j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hw' : ‖Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t)‖ ≤ B ^ (∑ i, ex Dw a' n i) :=
    norm_prod_pow_le (fun i => Formalism.L2.PjFree.toC (t i : CAt σ)) (ex Dw a' n) B ht
  rw [hsc]
  change ‖(Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t) * Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) : ℂ)‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hM k x hux).trans (le_max_left _ _)) hw' (norm_nonneg _) (le_max_right _ _)

end GlobalTheory.ArcBdd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArcStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.cuspForm_values_bounded_on_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  first | exact @GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | exact GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | (intros; apply GlobalTheory.ArcBdd.cusp_values_bounded_on_arc <;> assumption)
end
end

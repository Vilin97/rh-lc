module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeGStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonneStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquare

section

@[expose] public section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquareStatement

section

@[expose] public section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  first | exact @GlobalTheory.PointFormSign.chernPoly_top_of_negSq | exact GlobalTheory.PointFormSign.chernPoly_top_of_negSq | (intros; apply GlobalTheory.PointFormSign.chernPoly_top_of_negSq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameC

section

@[expose] public section

set_option autoImplicit false

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign

theorem mContDiffAt_domGram {m r : ℕ} {k : WithTop ℕ∞} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : MContDiffAt k (domGram m r) x := by
  have h : MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) x := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  exact (((mContDiffAt_const 1).sub (h.mul h.conjTranspose)).inv hx).transpose

theorem isUnit_det_domGram {m r : ℕ} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : IsUnit (domGram m r x).det := by
  rw [domGram, det_transpose]
  exact isUnit_nonsing_inv_det _ hx

theorem isNegSq_curv_of_changeFrame_comp {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n)
    (W : V n → Matrix (Fin m) (Fin m) ℂ) (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ) (hκ : 0 < κ)
    (hG : ∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ))
    (hZ : ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u)
    (hW : ∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u)
    (hWu : IsUnit (W v).det) (hpos : (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef)
    (hneg : IsNegSq (curv (domGram m r) (Z v)) r) : IsNegSq (curv G v) r := by
  obtain ⟨S, T, hS, hF⟩ := hneg
  have hu : IsUnit (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).det :=
    (isUnit_iff_isUnit_det _).1 hpos.isUnit
  have hD2 : MContDiffAt 2 (domGram m r) (Z v) := mContDiffAt_domGram _ hu
  have hDu : IsUnit (domGram m r (Z v)).det := isUnit_det_domGram _ hu
  have hZ2 : ContDiffAt ℂ 2 Z v := (GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hZ).contDiffAt
  have hW2 : MContDiffAt 2 W v := fun i j =>
    ((GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 (hW i j)).contDiffAt (n := 2)).restrict_scalars ℝ
  have hW0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar W x η = 0 := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hW i j]
      with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b)]
    rfl
  have hH2 : MContDiffAt 2 (fun x => domGram m r (Z x)) v :=
    fun a b => (hD2 a b).comp v (hZ2.restrict_scalars ℝ)
  have hK2 : MContDiffAt 2 (fun u => (W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ) v :=
    (hW2.transpose.mul hH2).mul hW2.conjTranspose.transpose
  have hKu : IsUnit ((W v)ᵀ * domGram m r (Z v) * (W v)ᴴᵀ).det := by
    simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hWu.mul hDu).mul hWu.star
  refine ⟨S * W v, T ∘ₗ (fderiv ℂ Z v).toLinearMap, by rw [det_mul]; exact hS.mul hWu, fun ξ η => ?_⟩
  rw [curv_congr hG, curv_smul (f := fun _ => κ) contDiffAt_const hκ.ne' hK2 hKu, leviForm_const,
    curv_changeFrame (H := fun x => domGram m r (Z x)) hH2 hDu hW2 hWu hW0,
    curv_comp_holo hD2 hDu hZ2, hF, Matrix.mul_inv_rev]
  simp [Matrix.mul_assoc]

end GlobalTheory.PointFormSign
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameCStatement

section

@[expose] public section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  first | exact @GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | exact GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | (intros; apply GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonneg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

theorem chernTop_pointPoly_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    {n : ℕ} (G : V n → Mat Dw.mult ℂ) (v : V n)
    (h : ∀ τ : GlobalTheory.AllWt.Psi H, IsNegSq (curv (fun u => G u τ.1) v) (Dw.p + Dw.q - Dw.mult τ.1)) :
    0 ≤ chernTop (pointPoly H Dw) G v := by
  choose S T hS hF using h
  have key : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (sqPoly (T τ)).det ^ (Dw.p + Dw.q - Dw.mult τ.1) := by
    rw [pointPoly, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_C, aeval_X, GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare _ _ _ _ (hS τ) (hF τ)]
    congr 1
    simp only [map_pow, map_neg, map_one]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have h0 : 0 ≤ topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw)) := by
    rw [key]; exact GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg _ _ _ T
  have hre : 0 ≤ (topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw))).re :=
    (Complex.nonneg_iff.1 h0).1
  unfold chernTop
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg Real.pi_pos.le _)) hre

end GlobalTheory.PointFormSign

theorem GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA
  refine GlobalTheory.PointFormSign.chernTop_pointPoly_nonneg H Dw _ _ fun τ => ?_
  obtain ⟨κ, W, Z, hκ, hG, hZ, hW, hWu, hZd⟩ := GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ
  exact GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange _ _ W Z κ hκ hG hZ hW hWu hZd (GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram _ _ _ hZd)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPointClassHodgeMetricLieNonnegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  first | exact @GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg | exact GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg | (intros; apply GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg <;> assumption)
end
end

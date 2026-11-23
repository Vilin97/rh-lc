module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInvStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbeddingStatement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvatureStatement
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwapStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernReindex

variable {n a b : ℕ}

theorem mdel_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.mdel (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.mdel H z ξ) := by
  ext i j; rfl

theorem conn_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.conn (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.conn H z ξ) := by
  rw [GlobalTheory.HermFrame.conn, GlobalTheory.HermFrame.conn, mdel_reindex, Matrix.transpose_reindex, Matrix.transpose_reindex,
    Matrix.inv_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem curv_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.curv (fun u => Matrix.reindex e e (H u)) z ξ η = Matrix.reindex e e (GlobalTheory.HermFrame.curv H z ξ η) := by
  unfold GlobalTheory.HermFrame.curv
  simp_rw [conn_reindex]
  ext i j; rfl

theorem curvPoly_reindex (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.reindex e e (F u)) v = Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v) := by
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, curv_reindex]
  rfl

theorem charpolyRev_reindex {R : Type} [CommRing R] (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) R) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_reindex]

theorem chernPoly_reindex : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  intro n a b e F v k
  rw [GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.chernPoly, curvPoly_reindex,
    show -(Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v)) = Matrix.reindex e e (-GlobalTheory.GoodMetric.curvPoly F v) from by
      ext i j; rfl, charpolyRev_reindex]

end GlobalTheory.ChernReindex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.chernFormPolyCoeff_reindex_frame : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  first | exact @GlobalTheory.ChernReindex.chernPoly_reindex | exact GlobalTheory.ChernReindex.chernPoly_reindex | (intros; apply GlobalTheory.ChernReindex.chernPoly_reindex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem posDef_eq_conjTranspose_mul_self_of_isUnit_det :
    ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef →
      ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  intro p P hP
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP.posSemidef
  have hB : star (CFC.sqrt P) * CFC.sqrt P = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P h0]
  refine ⟨CFC.sqrt P, ?_, hB⟩
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [← hB, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDetStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef : ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef → ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  first | exact @GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | exact GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | (intros; apply GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.PointChernScale

open Matrix
open scoped ComplexOrder

theorem curv_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv Z w ξ η hw

theorem curv_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding Z w ξ η hw

theorem exists_factor {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : P.PosDef) :
    ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef P hP

theorem posDef_swap {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap z h

theorem chernPoly_conj {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n)
    (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ a b, curv F v (coordVec a) (coordVec b) =
      S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) (k : ℕ) :
    chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (chernPoly F v' k) := GlobalTheory.T.chernPoly_conj_linearSubst_curvature F v v' J S hS h k

theorem chernPoly_reindex {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) : chernPoly (fun u => reindex e e (F u)) v k = chernPoly F v k := GlobalTheory.T.chernFormPolyCoeff_reindex_frame e F v k

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def zLin {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin Dw.p) (Fin Dw.q) ℂ where
  toFun u := coordOf ix u σ
  map_add' u v := by ext i j; simp [coordOf]
  map_smul' c u := by ext i j; simp [coordOf]

theorem zLin_apply {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) (u : ReciprocityTheory.L2DbarEstimates.V n) : zLin ix σ u = coordOf ix u σ := rfl

def jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun c a =>
  (A (ix c).1 * coordOf ix (coordVec a) (ix c).1 * B (ix c).1) (ix c).2.1 (ix c).2.2

theorem zLin_jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ)
    (σ : GlobalTheory.AllWt.Psi H) (a : Fin n) :
    zLin ix σ (∑ c, jMat ix A B c a • coordVec c) = A σ * zLin ix σ (coordVec a) * B σ := by
  ext i j
  change (∑ c, jMat ix A B c a • coordVec c) (ix.symm (σ, i, j)) = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, jMat, zLin_apply, Pi.single_apply]

theorem conj_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hA : IsUnit A.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w (coordVec a) (coordVec b) =
      A⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) * A := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) =
      -(Z (∑ c, J c a • coordVec c) * (Z (∑ d, J d b • coordVec d))ᴴ) := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 ξ η = -(Z ξ * (Z η)ᴴ) := by
      intro ξ η
      rw [curv_tau Z 0 ξ η h0]
      simp

    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]; rfl
  rw [hsum, hJ, hJ, curv_tau Z w _ _ hw, ← hAA, ← hB]
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hA]

theorem conj_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hB0 : IsUnit B.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w (coordVec a) (coordVec b) =
      (Bᵀ)⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) * Bᵀ := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) =
      -((Z (∑ d, J d b • coordVec d))ᴴ * Z (∑ c, J c a • coordVec c))ᵀ := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 ξ η = -((Z η)ᴴ * Z ξ)ᵀ := by
      intro ξ η
      rw [curv_tauBar Z 0 ξ η h0]
      simp

    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg,
    Finset.sum_neg_distrib, neg_inj, transpose_sum, transpose_smul]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  rw [hsum, hJ, hJ, curv_tauBar Z w _ _ hw, ← hAA, ← hB, ← transpose_nonsing_inv, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj, ← transpose_mul, ← transpose_mul]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB0]

theorem chernPoly_model_eq_subst {H : Host E} (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n) (hw : InDom (coordOf ix w)) :
    ∃ J : Matrix (Fin n) (Fin n) ℂ, ∀ (τ : E →+* ℂ) (k : ℕ),
      chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) w k =
        aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
          (chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) 0 k) := by
  have hP : ∀ σ, (1 - coordOf ix w σ * (coordOf ix w σ)ᴴ)⁻¹.PosDef := fun σ => (posDef_swap _ (hw σ)).inv
  have hQ : ∀ σ, (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹.PosDef := fun σ => (hw σ).inv
  choose A hA hAA using fun σ => exists_factor _ (hP σ)
  choose A' hA' hAA' using fun σ => exists_factor _ (hQ σ)
  let B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ := fun σ => (A' σ)ᴴ
  have hB : ∀ σ, B σ * (B σ)ᴴ = (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹ := fun σ => by
    simp only [B, conjTranspose_conjTranspose]; exact hAA' σ
  have hB0 : ∀ σ, IsUnit (B σ).det := fun σ => by
    simp only [B, det_conjTranspose]; exact (hA' σ).star
  refine ⟨jMat ix A B, fun τ k => ?_⟩
  by_cases h : τ (H.rt : E) = H.rt0
  · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
        reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
          ((1 - (zLin ix ⟨τ, h⟩ u).map (starRingEnd ℂ) * (zLin ix ⟨τ, h⟩ u)ᵀ)⁻¹) := by
      funext u; simp only [modelGram, dif_pos h]; rfl
    rw [e, chernPoly_reindex, chernPoly_reindex]
    exact chernPoly_conj _ w 0 _ (A ⟨τ, h⟩) (hA _)
      (conj_tau (zLin ix ⟨τ, h⟩) w (A _) (B _) _ (hw _) (hA _) (hAA _) (hB _) (zLin_jMat ix A B _)) k
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
          reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
            ((1 - (zLin ix ⟨conjEmb τ, h'⟩ u)ᴴ * zLin ix ⟨conjEmb τ, h'⟩ u)⁻¹) := by
        funext u; simp only [modelGram, dif_neg h, dif_pos h']; rfl
      rw [e, chernPoly_reindex, chernPoly_reindex]
      exact chernPoly_conj _ w 0 _ (B _)ᵀ (by rw [det_transpose]; exact hB0 _)
        (conj_tauBar (zLin ix ⟨conjEmb τ, h'⟩) w (A _) (B _) _ (hw _) (hB0 _) (hAA _) (hB _)
          (zLin_jMat ix A B _)) k
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun _ => 1 := by
        funext u; simp only [modelGram, dif_neg h, dif_neg h']
      have hc : ∀ v, chernPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v k =
          (1 : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)).coeff k := by
        intro v
        have h0 : curvPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v = 0 := by
          ext i j; simp [curvPoly]
        simp [chernPoly, h0, Matrix.charpolyRev]
      rw [e, hc, hc, Polynomial.coeff_one]
      split_ifs <;> simp

end GlobalTheory.PointChernScale


open GlobalTheory.PointChernScale in
theorem GlobalTheory.PointChern.chernTop_model_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) →
    ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ,
      chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  intro E _ _ _ H Dw n ix w hw
  obtain ⟨J, hJ⟩ := chernPoly_model_eq_subst Dw ix w hw
  refine ⟨Complex.normSq J.det, fun R => ?_⟩
  let φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)
  have hR : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) w x.2) R =
      φ (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) R) := by
    have := congrArg (fun f => f R) (MvPolynomial.comp_aeval (R := ℝ)
      (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (φ.restrictScalars ℝ))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => (aeval f R : MvPolynomial (Fin n × Fin n) ℂ)) (funext fun x => hJ x.1 x.2)
  simp only [chernTop]
  rw [hR, GlobalTheory.GoodMetric.topCoeff_subst_conj, Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOriginStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.chernPolyTopDensity_boundedDomainModel_eq_mul_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  first | exact @GlobalTheory.PointChern.chernTop_model_eq_mul | exact GlobalTheory.PointChern.chernTop_model_eq_mul | (intros; apply GlobalTheory.PointChern.chernTop_model_eq_mul <;> assumption)
end
end

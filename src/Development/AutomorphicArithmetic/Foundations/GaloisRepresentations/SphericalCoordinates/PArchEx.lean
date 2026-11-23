module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsHermitianDiagonalizationAtInfinitePlaceOfS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ReMulSignatureIPosOfHermitianTraceFormula
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.FinrankArchimedeanEqTwoMulDim

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.finrank_archimedean_eq_two_mul_dim :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → UpperTheory.Gal.W2.ArchSpan → Module.finrank ℝ (Arch G) = Module.finrank ℚ (VQ D) ∧ Module.finrank ℝ (Arch G) = 2 * D.g := by
  intro p _ D G L hm hA
  have h1 : Module.finrank ℝ (Arch G) = Fintype.card (InfinitePlace G.F) * (G.n * 2) := by
    have hc : Module.finrank ℝ (Fin G.n → ℂ) = G.n * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    unfold Arch
    rw [Module.finrank_pi_fintype]
    simp [hc]
  have h2 : Module.finrank ℝ (Arch G) = G.n * Module.finrank ℚ G.F := (hA G.F G.n).2.1
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa
    rw [← D.rankLa]
    exact Module.finrank_baseChange
  have hg : D.g = D.m * D.n * Module.finrank ℚ D.F / 2 := rfl
  have h2' : Module.finrank ℝ (Arch G) = D.n * Module.finrank ℚ D.F := by
    rw [h2, h3, L.n_eq]
  have h1' : Module.finrank ℝ (Arch G) = 2 * (Fintype.card (InfinitePlace G.F) * D.n) := by
    rw [h1, L.n_eq]; ring
  rw [hm, _root_.one_mul] at h4 hg
  refine ⟨by rw [h2', h4], ?_⟩
  rw [hg, ← h2', h1']
  omega
end
end

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.SpanRealMatrixMulVecInfinitePlaceEmbeddingEqTop

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ S : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ, (∀ v, (S v).det ≠ 0) → Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) => S v *ᵥ fun i => v.embedding (x i)) = ⊤ := by
  intro F _ _ _ n hA S hS
  let Ph : (InfinitePlace F → Fin n → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
    { toFun := fun x v => S v *ᵥ x v
      map_add' := fun x y => by
        funext v
        simp [Matrix.mulVec_add]
      map_smul' := fun c x => by
        funext v
        simp [Matrix.mulVec_smul] }
  have hsurj : Function.Surjective Ph := by
    intro y
    refine ⟨fun v => (S v)⁻¹ *ᵥ y v, ?_⟩
    funext v
    have hu : IsUnit (S v).det := isUnit_iff_ne_zero.2 (hS v)
    change S v *ᵥ ((S v)⁻¹ *ᵥ y v) = y v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h := congrArg (Submodule.map Ph) (hA F n).1
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.2 hsurj, ← Set.range_comp] at h
  exact h
end
end

-- Source module: Development.AutomorphicArithmetic.PAdicLatticeApproximation.TraceConjDotProductEqSumInfinitePlaces

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces :
    ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ), UpperTheory.Gal.W2.ArchSpan → ∀ (A : Matrix (Fin n) (Fin n) F) (S gr : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (lam : InfinitePlace F → ℂ), (∀ v, (S v).det ≠ 0) → (∀ v, (S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹ = lam v • gr v) → ∀ x y : Fin n → F, ((Algebra.trace ℚ F ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x)) : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i))).re := by
  intro F _ _ _ n hA A S gr lam hdet hform x y
  rw [((hA F n).2.2)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hU : IsUnit (S v).det := isUnit_iff_ne_zero.mpr (hdet v)
  have h1 : (S v)ᴴ * (S v)⁻¹ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.conjTranspose_one]
  have h2 : (S v)⁻¹ * S v = 1 := Matrix.nonsing_inv_mul _ hU
  have hAmap : A.map v.embedding = (S v)ᴴ * (lam v • gr v) * S v := by
    rw [← hform v]
    calc A.map v.embedding
        = ((S v)ᴴ * (S v)⁻¹ᴴ) * A.map v.embedding * ((S v)⁻¹ * S v) := by
          rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (S v)ᴴ * ((S v)⁻¹ᴴ * A.map v.embedding * (S v)⁻¹) * S v := by
          simp only [Matrix.mul_assoc]
  have e1 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = (star fun i => v.embedding (y i)) ⬝ᵥ (A.map v.embedding *ᵥ fun i => v.embedding (x i)) := by

    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply,
    IsCMField.complexEmbedding_complexConj]
    rfl
  have e2 : v.embedding ((fun i => IsCMField.complexConj F (y i)) ⬝ᵥ (A *ᵥ x))
      = lam v * hv (gr v) (S v *ᵥ fun i => v.embedding (x i)) (S v *ᵥ fun i => v.embedding (y i)) := by
    rw [e1, hAmap, hv, Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec (star fun i => v.embedding (y i)) (S v)ᴴ, Matrix.smul_mulVec]
    simp [Matrix.vecMul_conjTranspose, dotProduct_smul]
  rw [e2]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PArchEx

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.archEx_of :
    UpperTheory.Gal.W2.FMat → UpperTheory.Gal.W2.FForm → UpperTheory.Gal.W2.SN → UpperTheory.Gal.W2.ArchSpan → UpperTheory.Gal.W2.ArchEx := by
  intro hFM hFF hSN hAS p _ D G L hm
  obtain ⟨kp, σ, hk⟩ := hFM p D G L hm
  obtain ⟨A, hdet, hskew, hform, hcomm⟩ := hFF p D G L kp σ hk
  choose S lam hS hpsi hconj hAv using fun v => UpperTheory.exists_hermitian_diagonalization_at_infinitePlace_of_skewHermitian p G σ A hSN hdet hskew hcomm v
  let th : VQ D →+ Arch G :=
    { toFun := fun w v => S v *ᵥ fun i => v.embedding (kp w i)
      map_zero' := by
        funext v
        simp
        exact Matrix.mulVec_zero _
      map_add' := fun x y => by
        funext v
        have : (fun i => v.embedding (kp (x + y) i)) = (fun i => v.embedding (kp x i)) + (fun i => v.embedding (kp y i)) := by
          funext i; simp
        simp only [this, Matrix.mulVec_add]
        rfl }
  have hth : ∀ w v, th w v = S v *ᵥ fun i => v.embedding (kp w i) := fun _ _ => rfl
  have hact : ∀ (c : G.C) w v, th (L.rep c w) v = G.psi v c *ᵥ th w v := by
    intro c w v
    rw [hth, hth, Matrix.mulVec_mulVec, hpsi, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [hk c w]

    simp [Matrix.mulVec, dotProduct, map_sum]
  have hform' : ∀ u w, ((D.EF.baseChange ℚ u w : ℚ) : ℝ) = ∑ v, 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re := by
    intro u w
    rw [hform u w]
    exact UpperTheory.trace_conj_dotProduct_eq_sum_infinitePlaces G.F G.n hAS A S G.gram lam hS hAv (kp u) (kp w)
  have hspan : Submodule.span ℝ (Set.range th) = ⊤ := by
    rw [← UpperTheory.span_real_matrix_mulVec_infinitePlace_embedding_eq_top G.F G.n hAS S hS]
    congr 1
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨kp w, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨kp.symm x, by funext v; simp [hth]⟩
  have hpos := UpperTheory.re_mul_signature_I_pos_of_hermitian_trace_formula p D G L th lam hact hform' hspan hconj
  obtain ⟨hd1, hd2⟩ := UpperTheory.finrank_archimedean_eq_two_mul_dim p D G L hm hAS
  have hs2 : ∀ v, sgnV L v * sgnV L v = 1 := by
    intro v
    unfold sgnV
    split_ifs <;> simp
  have hlamim : ∀ v, lam v = ((lam v * sgnV L v * Complex.I).re : ℂ) * (-(sgnV L v) * Complex.I) := by
    intro v
    have hre : (lam v).re = 0 := by
      have := congrArg Complex.re (hconj v)
      simp at this
      linarith
    have hreal : (lam v * sgnV L v * Complex.I).im = 0 := by
      unfold sgnV
      split_ifs <;> simp [hre]
    have hc : ((lam v * sgnV L v * Complex.I).re : ℂ) = lam v * sgnV L v * Complex.I := by
      apply Complex.ext <;> simp [hreal]
    rw [hc]
    have := hs2 v
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (lam v * Complex.I * Complex.I) * this + lam v * hI
  exact ⟨{
    th := th
    r := fun v => 2 * (lam v * sgnV L v * Complex.I).re
    r_pos := fun v => by have := hpos v; linarith
    act := hact
    form := by
      intro u w
      rw [hform' u w]
      refine Finset.sum_congr rfl fun v _ => ?_
      show 2 * (lam v * hv (G.gram v) (th u v) (th w v)).re = 2 * (lam v * sgnV L v * Complex.I).re * (-(sgnV L v) * Complex.I * hv (G.gram v) (th u v) (th w v)).re
      conv_lhs => rw [hlamim v, mul_assoc ((lam v * sgnV L v * Complex.I).re : ℂ), Complex.re_ofReal_mul]
      ring
    span := hspan
    dim := hd1
    dimg := hd2 }⟩
end
end

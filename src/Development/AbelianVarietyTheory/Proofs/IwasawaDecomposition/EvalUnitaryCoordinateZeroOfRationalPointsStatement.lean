module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import ReciprocityTheory.Automorphisms.Unitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZeroStatement
public import Mathlib.Algebra.MvPolynomial.Eval
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEval
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroupStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  first | exact @GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | exact GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian | (intros; apply GlobalTheory.CayleyRat.exists_mem_GQ0_eq_cayley_of_skew_hermitian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvPolynomialClearDenominatorsEvalStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.mvPolynomial_clear_denominators_eval : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by
  first | exact @GlobalTheory.clearDenominators | exact GlobalTheory.clearDenominators | (intros; apply GlobalTheory.clearDenominators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFamilyEqCayleyOfSkewFamily

section

@[expose] public section

open NumberField Matrix

namespace GlobalTheory

variable {n : ℕ}

theorem cayleyInv_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 - (X - 1) * (X + 1)⁻¹ = (2:ℂ) • (X + 1)⁻¹ := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) - (X - 1) = (1 : Matrix (Fin n) (Fin n) ℂ) + 1 := by abel
  calc 1 - (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ - (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = ((X + 1) - (X - 1)) * (X + 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = (2:ℂ) • (X + 1)⁻¹ := by rw [e, add_mul, one_mul, two_smul]

theorem cayleyInv_one_add (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 + (X - 1) * (X + 1)⁻¹ = X * ((2:ℂ) • (X + 1)⁻¹) := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) + (X - 1) = X + X := by abel
  calc 1 + (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ + (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = (X + X) * (X + 1)⁻¹ := by rw [← add_mul, e]
    _ = X * ((2:ℂ) • (X + 1)⁻¹) := by rw [mul_smul_comm, two_smul, add_mul]

theorem cayleyInv_det_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    IsUnit (1 - (X - 1) * (X + 1)⁻¹).det := by
  rw [cayleyInv_one_sub _ hu, isUnit_iff_ne_zero]
  intro h0
  have h2 : ((2:ℂ) • (X + 1)⁻¹ * (X + 1)).det = (2:ℂ) ^ n := by
    rw [smul_mul_assoc, nonsing_inv_mul _ hu, det_smul, det_one, mul_one, Fintype.card_fin]
  rw [det_mul, h0, zero_mul] at h2
  exact (pow_ne_zero n two_ne_zero) h2.symm

theorem cayleyInv_skew (X Z : Matrix (Fin n) (Fin n) ℂ) (hXZ : X * Zᵀ = 1)
    (hX : IsUnit (X + 1).det) (hZ : IsUnit (Z + 1).det) :
    (Z - 1) * (Z + 1)⁻¹ = -((X - 1) * (X + 1)⁻¹)ᵀ := by
  have hZX : Zᵀ * X = 1 := mul_eq_one_comm.mp hXZ
  have hAZ : Xᵀ * Z = 1 := by
    simpa [transpose_mul, transpose_transpose, transpose_one] using congrArg Matrix.transpose hZX
  have hA : IsUnit (Xᵀ + 1).det := by
    rw [show Xᵀ + 1 = (X + 1)ᵀ by rw [transpose_add, transpose_one], det_transpose]; exact hX
  have key : (Xᵀ + 1) * (Z - 1) = -((Xᵀ - 1) * (Z + 1)) := by
    simp only [mul_sub, mul_add, sub_mul, add_mul, mul_one, one_mul, hAZ]; abel
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]
  calc (Z - 1) * (Z + 1)⁻¹ = (Xᵀ + 1)⁻¹ * ((Xᵀ + 1) * (Z - 1)) * (Z + 1)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = (Xᵀ + 1)⁻¹ * (-((Xᵀ - 1) * (Z + 1))) * (Z + 1)⁻¹ := by rw [key]
    _ = -((Xᵀ + 1)⁻¹ * (Xᵀ - 1)) := by
        rw [mul_neg, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hZ,
          Matrix.mul_one]

theorem unitary_isCayley_of_det_ne_zero : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) →
    ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧
      (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  intro L _ _ n X hX hdet
  have hu : ∀ σ, IsUnit (X σ + 1).det := fun σ => by
    rw [add_comm]; exact isUnit_iff_ne_zero.mpr (hdet σ)
  refine ⟨fun σ => (X σ - 1) * (X σ + 1)⁻¹, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · exact cayleyInv_skew (X σ) (X (ComplexEmbedding.conjugate σ)) (hX σ) (hu σ) (hu _)
  · exact isUnit_iff_ne_zero.mp (cayleyInv_det_one_sub (X σ) (hu σ))
  · show (1 + (X σ - 1) * (X σ + 1)⁻¹) * (1 - (X σ - 1) * (X σ + 1)⁻¹)⁻¹ = X σ
    have hY := cayleyInv_det_one_sub (X σ) (hu σ)
    rw [cayleyInv_one_add _ (hu σ), ← cayleyInv_one_sub _ (hu σ), Matrix.mul_assoc,
      mul_nonsing_inv _ hY, Matrix.mul_one]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFamilyEqCayleyOfSkewFamilyStatement

section

@[expose] public section

open NumberField Matrix

theorem _root_.GlobalTheory.T.unitary_family_eq_cayley_of_skew_family : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) → ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧ (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  first | exact @GlobalTheory.unitary_isCayley_of_det_ne_zero | exact GlobalTheory.unitary_isCayley_of_det_ne_zero | (intros; apply GlobalTheory.unitary_isCayley_of_det_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPoints

section

@[expose] public section

noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.UDense

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem eval_bind₁_scale {ι : Type} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X,
      MvPolynomial.eval_C]

theorem vanish_generic (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hX : IsUPt X) (hd : ∀ σ, (1 + X σ).det ≠ 0) :
    MvPolynomial.eval (upt X) F = 0 := by
  classical
  let V : (L →+* ℂ) → Matrix (Fin n) (Fin n) (MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :=
    fun σ => Matrix.of fun i j => MvPolynomial.X (σ, i, j)
  let P : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => ((1 + V p.1) * (1 - V p.1).adjugate) p.2.1 p.2.2
  let D : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => (1 - V p.1).det
  obtain ⟨G, M, hGM⟩ := GlobalTheory.T.mvPolynomial_clear_denominators_eval F P D
  have evV : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      (V σ).map (MvPolynomial.eval (upt y)) = y σ := by
    intro y σ; ext i j; simp [V, upt]
  have evDet : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      MvPolynomial.eval (upt y) ((1 - V σ).det) = (1 - y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evP : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, (1 - y σ).det ≠ 0) →
      (fun p => MvPolynomial.eval (upt y) (P p) / MvPolynomial.eval (upt y) (D p)) =
        upt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) := by
    intro y hy
    funext p
    have hm : ((1 + V p.1) * (1 - V p.1).adjugate).map (MvPolynomial.eval (upt y)) =
        (1 + y p.1) * (1 - y p.1).adjugate := by
      rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _), evV]
    have hP : MvPolynomial.eval (upt y) (P p) = ((1 + y p.1) * (1 - y p.1).adjugate) p.2.1 p.2.2 := by
      rw [← hm]; rfl
    rw [hP, show MvPolynomial.eval (upt y) (D p) = (1 - y p.1).det from evDet y p.1]
    simp only [upt, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [div_eq_inv_mul]
  let Q := G * ∏ σ, (1 - V σ).det
  have hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0 := by
    intro S hS
    have hdS : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det = σ (1 - S).det := by
      intro σ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    simp only [Q, map_mul, map_prod, evDet, hdS]
    by_cases h0 : (1 - S).det = 0
    · have σ0 : L →+* ℂ := Classical.arbitrary _
      rw [Finset.prod_eq_zero (Finset.mem_univ σ0) (by rw [h0, map_zero]), mul_zero]
    · obtain ⟨γ₀, hγ, hγv⟩ := GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup L n S hS h0
      have hne : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det ≠ 0 := fun σ => by
        rw [hdS]; exact (map_ne_zero σ).2 h0
      have hDy : ∀ p, MvPolynomial.eval (upt (ratPt S)) (D p) ≠ 0 := fun p => by
        rw [show MvPolynomial.eval (upt (ratPt S)) (D p) = _ from evDet _ p.1]; exact hne p.1
      obtain ⟨-, hG⟩ := hGM _ hDy
      rw [hG, evP _ hne]
      have hc : (fun σ => (1 + ratPt S σ) * (1 - ratPt S σ)⁻¹) = ratPt (γ₀ : Matrix (Fin n) (Fin n) L) := by
        funext σ
        rw [hγv]
        simp only [ratPt, Matrix.map_mul, map_inv_field_hom, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [hc, hF γ₀ hγ, mul_zero, zero_mul]
  obtain ⟨Y, hYs, hYd, hYX⟩ := GlobalTheory.T.unitary_family_eq_cayley_of_skew_family L n X hX hd
  have hQY := GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian L n Q hQ Y hYs
  have hDY : ∀ p, MvPolynomial.eval (upt Y) (D p) ≠ 0 := fun p => by
    rw [show MvPolynomial.eval (upt Y) (D p) = _ from evDet _ p.1]; exact hYd p.1
  obtain ⟨hM, hG⟩ := hGM _ hDY
  simp only [Q, map_mul, map_prod, evDet] at hQY
  have hprod : ∏ σ, (1 - Y σ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hYd σ
  have hG0 : MvPolynomial.eval (upt Y) G = 0 := (mul_eq_zero.1 hQY).resolve_right hprod
  rw [hG, evP _ hYd, show (fun σ => (1 + Y σ) * (1 - Y σ)⁻¹) = X from funext hYX] at hG0
  exact (mul_eq_zero.1 hG0).resolve_left hM

theorem eval_eq_zero_of_rat : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) →
    ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  intro L _ _ _ n F hF X hX
  obtain ⟨a, ha, hdet⟩ := GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero L n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := complexConj_invol L
  have ha' : c a * a = 1 := by rw [mul_comm]; exact ha
  have hca0 : c a ≠ 0 := left_ne_zero_of_mul_eq_one ha'
  have hemb : ∀ (σ : L →+* ℂ) x, ComplexEmbedding.conjugate σ x = σ (c x) := fun σ x =>
    (IsCMField.complexEmbedding_complexConj L σ x).symm
  let F' := MvPolynomial.bind₁ (fun p : (L →+* ℂ) × Fin n × Fin n => MvPolynomial.C (p.1 (c a)) * MvPolynomial.X p) F
  have hF'ev : ∀ z, MvPolynomial.eval z F' = MvPolynomial.eval (fun p => p.1 (c a) * z p) F :=
    fun z => eval_bind₁_scale _ z F
  have hF' : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F' = 0 := by
    intro γ₀ hγ
    let s : GL (Fin n) L := Units.map (algebraMap L (Matrix (Fin n) (Fin n) L) : L →* Matrix (Fin n) (Fin n) L)
      (Units.mk0 (c a) hca0)
    have hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.scalar (Fin n) (c a) := rfl
    have hmem : s * γ₀ ∈ GQ0 L n := by
      refine (GQ0 L n).mul_mem ?_ hγ
      show (s : Matrix (Fin n) (Fin n) L) * conjT c s = 1
      rw [hs, conjT]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hcc, ha']
      · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
    have := hF _ hmem
    rw [hF'ev, ← this]
    refine congrArg (fun z => MvPolynomial.eval z F) ?_
    funext p
    simp [upt, ratPt, hs, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let X' : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ => σ a • X σ
  have hX' : IsUPt X' := by
    intro σ
    simp only [X', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX σ, hemb, ← map_mul, ha, ha',
      map_one, one_smul]
  have h := vanish_generic L n F' hF' X' hX' hdet
  rw [hF'ev] at h
  rw [← h]
  refine congrArg (fun z => MvPolynomial.eval z F) ?_
  funext p
  simp only [upt, X', Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, ha', map_one, one_mul]

end GlobalTheory.UDense
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPointsStatement

section

@[expose] public section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) → ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  first | exact @GlobalTheory.UDense.eval_eq_zero_of_rat | exact GlobalTheory.UDense.eval_eq_zero_of_rat | (intros; apply GlobalTheory.UDense.eval_eq_zero_of_rat <;> assumption)
end
end

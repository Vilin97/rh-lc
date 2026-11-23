module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChange
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChange

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_image (F β : Type) [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) := by
    intro q
    have h : (algebraMap F A).comp (algebraMap ℚ F) = (algebraMap R A).comp (algebraMap ℚ R) :=
      RingHom.ext_rat _ _
    exact RingHom.congr_fun h q
  have hx : algebraMap F A x = ∑ j, algebraMap ℚ R (ω.repr x j) • b j := by
    conv_lhs => rw [← ω.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hq, hb, Algebra.smul_def]
  rw [hx, b.repr_sum_self]

theorem coords_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  intro F β _ _ _ _ ω R A _ _ _ _ _ b hb x
  refine ⟨repr_algebraMap_of_basis_image F β ω R A b hb x, ?_⟩
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hb j, ← map_mul, repr_algebraMap_of_basis_image F β ω R A b hb]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChangeStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.coords_leftMulMatrix_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.coords_const_baseChange | exact GlobalTheory.ClassFin.coords_const_baseChange | (intros; apply GlobalTheory.ClassFin.coords_const_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChangeStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_coord_polynomial_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  first | exact @GlobalTheory.ClassFin.exists_coord_polynomial | exact GlobalTheory.ClassFin.exists_coord_polynomial | (intros; apply GlobalTheory.ClassFin.exists_coord_polynomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnit

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem res_mulVec_repr {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] (b : Module.Basis β R A) (g : Matrix κ κ A) (v : κ → A) :
    res b g *ᵥ (fun p : κ × β => b.repr (v p.1) p.2) = fun p : κ × β => b.repr ((g *ᵥ v) p.1) p.2 := by
  funext p

  simp only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum,
  Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2
  simpa [Matrix.mulVec, dotProduct] using h

theorem res_one_mul_injective_isUnit :
    ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  intro R A β κ _ _ _ _ _ _ _ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    by_cases h : i = j
    · subst h
      simp [res, Matrix.one_apply]
    · simp [res, Matrix.one_apply, h]
  · intro g h
    ext ⟨i, k⟩ ⟨j, l⟩

    simp only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul,
    Matrix.sum_apply]
  · intro g h hgh
    ext i j
    apply Algebra.leftMulMatrix_injective b
    ext k l
    exact congrFun (congrFun hgh (i, k)) (j, l)
  · intro g hg
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    have hs : Function.Surjective (res b g).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)
    obtain ⟨u, hu⟩ := hs (fun p : κ × β => b.repr (w p.1) p.2)
    refine ⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩
    have h := res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))
    have hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u := by
      funext p
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu', hu] at h
    funext i
    apply b.repr.injective
    ext k
    exact (congrFun h (i, k)).symm

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnitStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  first | exact @GlobalTheory.ClassFin.res_one_mul_injective_isUnit | exact GlobalTheory.ClassFin.res_one_mul_injective_isUnit | (intros; apply GlobalTheory.ClassFin.res_one_mul_injective_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestriction

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.WeilEqs

noncomputable def coordOf {κ β R : Type} [Fintype β] [CommRing R] [Algebra ℚ R] (c : β → ℚ)
    (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) : R :=
  ∑ l, y (Sum.inl (i, k)) (Sum.inl (j, l)) * algebraMap ℚ R (c l)

noncomputable def gen (ι : Type) : Matrix ι ι (MvPolynomial (ι × ι) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

section
variable {κ β R : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [CommRing R] [Algebra ℚ R]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_coordOf (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (coordOf c (gen ((κ × β) ⊕ Unit)) i j k) = coordOf c y i j k := by

  simp only [coordOf, gen, map_sum, map_mul, Matrix.of_apply, MvPolynomial.aeval_X, AlgHom.commutes]

theorem aeval_det (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      ((gen ((κ × β) ⊕ Unit)).toBlocks₁₁.det) = y.toBlocks₁₁.det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [gen, Matrix.toBlocks₁₁]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_comp_coord (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R)
    (Q : MvPolynomial ((κ × κ) × β) ℚ) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c (gen ((κ × β) ⊕ Unit)) p.1.1 p.1.2 p.2) Q) =
      MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c y p.1.1 p.1.2 p.2) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [aeval_coordOf]

variable {A : Type} [CommRing A] [Algebra R A]

theorem sum_leftMul_one (b : Module.Basis β R A) (x : A) (k : β) :
    ∑ l, Algebra.leftMulMatrix b x k l * b.repr 1 l = b.repr x k := by
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b x 1) k
  simpa [Matrix.mulVec, dotProduct] using h

theorem leftMul_expand (b : Module.Basis β R A) (x : A) (k l : β) :
    Algebra.leftMulMatrix b x k l = ∑ m, b.repr x m * Algebra.leftMulMatrix b (b m) k l := by
  conv_lhs => rw [← b.sum_repr x]

  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end

theorem exists_equations : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  intro F β _ _ _ _ ω n S
  choose Q hQ using fun P : MvPolynomial (Fin n × Fin n) F => GlobalTheory.T.exists_rational_coord_polynomial_baseChange F β ω (Fin n × Fin n) P
  let c : β → ℚ := fun l => ω.repr 1 l
  let X := gen ((Fin n × β) ⊕ Unit)
  refine ⟨{f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ?_⟩
  intro R A _ _ _ _ _ b hb y
  have hm := GlobalTheory.T.coords_leftMulMatrix_const_baseChange F β ω R A b hb
  obtain ⟨h1, hmul, -, hunit⟩ := GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit R A β (Fin n) b
  have hc : ∀ l, algebraMap ℚ R (c l) = b.repr 1 l := fun l => by
    have := (hm 1).1 l
    rw [map_one] at this
    exact this.symm
  have hL : ∀ m k l, algebraMap ℚ R (Algebra.leftMulMatrix ω (ω m) k l) =
      Algebra.leftMulMatrix b (b m) k l := fun m k l => by
    rw [hb m, (hm (ω m)).2, Matrix.map_apply]
  have hX : ∀ p q, MvPolynomial.aeval
      (fun ij : ((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit) => y ij.1 ij.2) (X p q) = y p q := fun p q => by
    simp [X, gen]
  have hinv : ∀ g : GL (Fin n) A, (res b (g : Matrix (Fin n) (Fin n) A)).det *
      (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← hmul, Units.mul_inv, h1, Matrix.det_one]
  have key : (∀ f ∈ {f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ev f y = 0) ↔
      ((∀ p u, y (Sum.inl p) (Sum.inr u) = 0) ∧ (∀ p u, y (Sum.inr u) (Sum.inl p) = 0) ∧
       (∀ i j k l, y (Sum.inl (i, k)) (Sum.inl (j, l)) =
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l) ∧
       y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) = 1 ∧
       ∀ P ∈ S, ∀ k, MvPolynomial.aeval
          (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) = 0) := by
    have e3 : ∀ i j k l, ev (X (Sum.inl (i, k)) (Sum.inl (j, l)) -
        ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) y =
        y (Sum.inl (i, k)) (Sum.inl (j, l)) -
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l := fun i j k l => by

      simp only [ev, map_sub, map_sum, map_mul, hX, AlgHom.commutes, hL]
      simp only [X, aeval_coordOf]
    have e4 : ev (X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1) y =
        y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) - 1 := by
      simp only [ev, map_sub, map_mul, hX, map_one]
      simp only [X, aeval_det]
    have e5 : ∀ P k, ev (MvPolynomial.aeval
        (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)) y =
        MvPolynomial.aeval (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) :=
      fun P k => aeval_comp_coord c y (Q P k)
    have e1 : ∀ p q, ev (X p q) y = y p q := hX
    constructor
    · intro h
      refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
      · rw [← e1]; exact h _ (Or.inl ⟨p, u, rfl⟩)
      · rw [← e1]; exact h _ (Or.inr (Or.inl ⟨p, u, rfl⟩))
      · rw [← sub_eq_zero, ← e3]; exact h _ (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, rfl⟩)))
      · rw [← sub_eq_zero, ← e4]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rw [← e5]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨P, hP, k, rfl⟩))))
    · rintro ⟨a1, a2, a3, a4, a5⟩ f (⟨p, u, rfl⟩ | ⟨p, u, rfl⟩ | ⟨i, j, k, l, rfl⟩ | rfl | ⟨P, hP, k, rfl⟩)
      · rw [e1, a1]
      · rw [e1, a2]
      · rw [e3, ← a3, sub_self]
      · rw [e4, a4, sub_self]
      · rw [e5, a5 P hP]
  rw [key]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => b.equivFun.symm (coordOf c y i j)
    have hG : ∀ i j k, b.repr (G i j) k = coordOf c y i j k := fun i j k => by
      have := congrFun (b.equivFun.apply_symm_apply (coordOf c y i j)) k
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hres : res b G = y.toBlocks₁₁ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [res, Matrix.of_apply, Matrix.toBlocks₁₁]
      rw [a3, leftMul_expand]
      simp only [hG]
    have hu : IsUnit G := hunit G (by rw [hres]; exact IsUnit.of_mul_eq_one _ a4)
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, fun P hP => ?_, ?_⟩
    · apply b.repr.injective
      ext k
      rw [hQ P R A b hb, hg]
      simp only [hG]
      simpa using a5 P hP k
    · have hi := hinv g
      rw [hg, hres] at hi
      have hcorner : y (Sum.inr ()) (Sum.inr ()) =
          (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by
        calc y (Sum.inr ()) (Sum.inr ()) = (y.toBlocks₁₁.det *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det) * y (Sum.inr ()) (Sum.inr ()) := by
              rw [hi, one_mul]
          _ = (y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ())) *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by ring
          _ = _ := by rw [a4, one_mul]
      ext (p | u) (q | v)
      · simp only [emb, Matrix.fromBlocks_apply₁₁, hg, hres, Matrix.toBlocks₁₁, Matrix.of_apply]
      · simp only [emb, Matrix.fromBlocks_apply₁₂, a1, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₁, a2, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        exact hcorner
  · rintro ⟨g, hg, rfl⟩
    have hco : ∀ i j k, coordOf c (emb b g) i j k = b.repr ((g : Matrix (Fin n) (Fin n) A) i j) k :=
      fun i j k => by
        simp only [coordOf, emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply, hc]
        exact sum_leftMul_one b _ k
    refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
    · simp [emb]
    · simp [emb]
    · simp only [hco]
      rw [← leftMul_expand]
      simp only [emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply]
    · simp only [emb, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      exact hinv g
    · simp only [hco]
      rw [← hQ P R A b hb (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) k, hg P hP]
      simp

end GlobalTheory.ClassFin.WeilEqs
end
end

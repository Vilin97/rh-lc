module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestriction
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHomStatement
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.TensorProduct.Free

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalEquationsWeilRestrictionStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_equations_weil_restriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  first | exact @GlobalTheory.ClassFin.WeilEqs.exists_equations | exact GlobalTheory.ClassFin.WeilEqs.exists_equations | (intros; apply GlobalTheory.ClassFin.WeilEqs.exists_equations <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReduced

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReducedStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R), (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧ (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  first | exact @GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | exact GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | (intros; apply GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestriction

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem ev_map_complexAut {ι : Type} (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) : ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  have h := MvPolynomial.comp_aeval (f := fun ij : ι × ι => g ij.1 ij.2) (σ.toRingHom.toRatAlgHom)
  have h2 := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, RingHom.toRatAlgHom_apply] at h2
  exact h2.symm

theorem exists_isQGroup_weilRestriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  intro F β _ _ _ _ ω n S hS
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_rational_equations_weil_restriction F β ω n S
  letI : Algebra F (ℂ ⊗[ℚ] F) := Algebra.TensorProduct.rightAlgebra
  have hb : ∀ i, Algebra.TensorProduct.basis ℂ ω i = algebraMap F (ℂ ⊗[ℚ] F) (ω i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hC := hS' ℂ (ℂ ⊗[ℚ] F) (Algebra.TensorProduct.basis ℂ ω) hb
  obtain ⟨h1, hm, hi⟩ := hS (ℂ ⊗[ℚ] F)
  obtain ⟨e1, em, ed, -⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom ℂ (ℂ ⊗[ℚ] F) β (Fin n) (Algebra.TensorProduct.basis ℂ ω)
  refine ⟨{g | ∀ f ∈ S', ev f g = 0}, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (hC 1).2 ⟨1, h1, e1.symm⟩
  · intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    obtain ⟨h', hh', rfl⟩ := (hC h).1 hh
    exact (hC _).2 ⟨g' * h', hm g' h' hg' hh', (em g' h').symm⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨g'⁻¹, hi g' hg', (ed g').2⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (ed g').1
  · intro σ g hg f hf
    rw [ev_map_complexAut, hg f hf, map_zero]
  · intro y hy
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' ℂ y).1 hy
  · intro R A _ _ _ _ _ b hbb
    refine ⟨fun y hy => (hS' R A b hbb y).1 ((GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R y).1 hy), fun hR g hg => ?_⟩
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R _).2 hR ((hS' R A b hbb _).2 ⟨g, hg, rfl⟩)

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestrictionStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_isQGroup_weilRestriction_alt : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  first | exact @GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | exact GlobalTheory.ClassFin.exists_isQGroup_weilRestriction | (intros; apply GlobalTheory.ClassFin.exists_isQGroup_weilRestriction <;> assumption)
end
end

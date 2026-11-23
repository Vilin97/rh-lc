module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlIntegerBasisSmulLatticeBasis
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CoeffEqZeroOfSumTmulLinearIndependentEqZero

section

@[expose] public section

open TensorProduct

theorem _root_.UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero :
    ∀ (K V C ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C] [Fintype ι] (v : ι → V), LinearIndependent K v → ∀ c : ι → C, ∑ i, v i ⊗ₜ[K] c i = 0 → ∀ i, c i = 0 := by
  intro K V C ι _ _ _ _ _ _ v hv c hsum i
  classical
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hfv : ∀ j, f (v j) = if j = i then 1 else 0 := by
    intro j
    have h1 : f (v j) = (Module.Basis.span hv).coord i ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
      rw [← hf]
      rfl
    rw [h1, ← Module.Basis.span_apply hv j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have h2 := congrArg (⇑((TensorProduct.lid K C).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id)) hsum

  simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
  LinearEquiv.coe_coe, TensorProduct.lid_tmul, hfv, map_zero] at h2
  simpa using h2
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSumTmul

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlProductBasisOfZlLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem exists_sum_tmul {R O B σ : Type} [CommRing R] [AddCommGroup O] [Module R O]
    [AddCommGroup B] [Module R B] [Fintype σ] (ω : Module.Basis σ R O) (x : O ⊗[R] B) :
    ∃ y : σ → B, x = ∑ s, ω s ⊗ₜ[R] y s :=
  _root_.UpperTheory.Reformulated.B.Qj2.exists_sum_tmul ω x

private theorem abstract_indep {R K O B V C σ κ : Type} [CommRing R] [Field K] [AddCommGroup O]
    [Module R O] [AddCommGroup B] [Module R B] [AddCommGroup V] [Module K V] [AddCommGroup C]
    [Module K C] [Fintype σ] [Fintype κ] (ω : Module.Basis σ R O)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C)) (e : κ → V ⊗[K] C) (w : σ × κ → V) (f : B → C)
    (hf : ∀ y, f y = 0 → y = 0) (hw : LinearIndependent K w)
    (hact : ∀ s k y, act (ω s ⊗ₜ[R] y) (e k) = w (s, k) ⊗ₜ[K] f y)
    (d : κ → O ⊗[R] B) (hd : ∑ k, act (d k) (e k) = 0) (k : κ) : d k = 0 := by
  choose y hy using fun k => exists_sum_tmul ω (d k)
  have h : ∑ p : σ × κ, w p ⊗ₜ[K] f (y p.2 p.1) = 0 := by
    rw [← hd, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_

    rw [hy k, map_sum]
    have hsum (S : Finset σ) :
        (∑ s ∈ S, act (ω s ⊗ₜ[R] y k s)) (e k) =
          ∑ s ∈ S, act (ω s ⊗ₜ[R] y k s) (e k) := by
      classical
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih => simp [ha, ih]
    rw [hsum]
    exact Finset.sum_congr rfl fun s _ => (hact s k _).symm
  have h0 := UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero K V C (σ × κ) w hw _ h
  rw [hy k]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hf _ (h0 (s, k)), TensorProduct.tmul_zero]

theorem _root_.UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hact κ _ b d hd k
  haveI : Module.Free ℤ_[l] ↥(OL LL) := inferInstance
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := inferInstance
  have hinj := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td LL).2
  refine abstract_indep (Module.Free.chooseBasis ℤ_[l] ↥(OL LL)) act
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) _
    (fun y => GlobalTheory.BKGal.JumpDR.cD Td y) (fun y hy => hinj (hy.trans (map_zero _).symm))
    (UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis l LL T κ _ b (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))) ?_ d hd k
  intro s k y
  refine (hact _ _ _ _).trans ?_
  rw [mul_one]
end
end

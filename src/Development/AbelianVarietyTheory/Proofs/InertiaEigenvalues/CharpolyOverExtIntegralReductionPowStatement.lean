module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftEqMapOfSpanningLatticeStatement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNilpotentResidueToMatrixMulLeftStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyNilpotentAddScalar

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem charpoly_nilpotent_add_scalar : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  intro k _ n N c hN
  have hc : N.charpoly = X ^ n := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.mp this.eq_zero
  have h1 := Matrix.charpoly_sub_scalar (N + Matrix.scalar (Fin n) c) c
  rw [add_sub_cancel_right, hc] at h1
  have hXC : ((X : k[X]) + C c).comp (X - C c) = X := by simp
  calc (N + Matrix.scalar (Fin n) c).charpoly
      = ((N + Matrix.scalar (Fin n) c).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [comp_assoc, hXC, comp_X]
    _ = (X - C c) ^ n := by rw [← h1]; simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyNilpotentAddScalarStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.charpoly_nilpotent_add_scalar' : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  first | exact @GlobalTheory.charpoly_nilpotent_add_scalar | exact GlobalTheory.charpoly_nilpotent_add_scalar | (intros; apply GlobalTheory.charpoly_nilpotent_add_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparable

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem span_pow_eq_top_of_separable (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  have hint : IsIntegral K.E B.g := Algebra.IsIntegral.isIntegral _
  have hz : minpoly K.E B.g ≠ 0 := minpoly.ne_zero hint
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hdvd : B.P ∣ minpoly K.E B.g := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
      Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
    intro p hp
    rw [Polynomial.mem_normalizedFactors_iff hP] at hp
    rw [Polynomial.mem_normalizedFactors_iff hz]
    exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
  have hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree := by
    have h1 : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [← h1]
    exact natDegree_le_of_dvd hdvd hz
  have hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ) :=
    linearIndependent_pow B.g
  have hge := hli.fintype_card_le_finrank
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.Unr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparableStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | exact GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | (intros; apply GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedInvolutionExtMapsIntegersToIntegers

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedInvolutionExtMapsIntegersToIntegersStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ x : K.O, ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  first | exact @GlobalTheory.UnitLemma.Unr.map_int | exact GlobalTheory.UnitLemma.Unr.map_int | (intros; apply GlobalTheory.UnitLemma.Unr.map_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPow

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_integral_reduction : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  intro K K' d φ hU B ψ hψ hσ hO hl hsep hint s hres
  set S := Algebra.adjoin K.O ({B.g} : Set B.A) with hSdef
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  let f0 : K'.O →+* S := (ψ.comp (algebraMap K'.O K'.E)).codRestrict S hO
  letI : Algebra K'.O S := f0.toAlgebra
  let ι : S →ₐ[K'.O] B.A := { S.val.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ι := Subtype.val_injective
  haveI : Module.Finite K.O S := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : Module.Finite K'.O S := by
    obtain ⟨T, hT⟩ := (inferInstance : Module.Finite K.O S).fg_top
    refine ⟨⟨T, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.O (T : Set S) := hT ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨y', hy'⟩ := GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers K K' d φ hU a
      have h : a • x = y' • x := by
        apply Subtype.ext
        rw [Algebra.smul_def, Algebra.smul_def, MulMemClass.coe_mul, MulMemClass.coe_mul]
        change algebraMap K.O B.A a * (x : B.A) = ψ (algebraMap K'.O K'.E y') * (x : B.A)
        rw [hy', hψ, ← IsScalarTower.algebraMap_apply]
      rw [h]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span K'.E (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun y hy0 => ?_
    clear hy0
    have hy : y ∈ Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) := GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable K B hsep ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨B.g ^ i, pow_mem (Algebra.self_mem_adjoin_singleton K.O B.g) i⟩, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  haveI : IsLocalRing S := hl
  obtain ⟨n, b, hb⟩ := GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq K'.O K'.E B.A S ι hinj hspan
  let x0 : S := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  refine ⟨(LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0)).charpoly, (hb x0).symm, ?_⟩
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← Matrix.charpoly_map]
  set t : S := x0 - algebraMap K'.O S s with ht
  have htm : t ∈ IsLocalRing.maximalIdeal S := by
    rw [ht, ← Ideal.Quotient.eq]; exact hres
  have hsplit : LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0) =
      LinearMap.toMatrix b b (LinearMap.mulLeft K'.O t) + Matrix.scalar (Fin n) s := by
    have : LinearMap.mulLeft K'.O x0 = LinearMap.mulLeft K'.O t + s • LinearMap.id := by
      ext y; simp [ht, Algebra.smul_def, sub_mul]
    rw [this, map_add (f := _), map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]; rfl
  rw [hsplit, Matrix.map_add _ (map_add _)]
  have hsc : (Matrix.scalar (Fin n) s).map (IsLocalRing.residue K'.O) = Matrix.scalar (Fin n) (IsLocalRing.residue K'.O s) := by
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp
  rw [hsc]
  exact GlobalTheory.T.charpoly_nilpotent_add_scalar' _ n _ _ (GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' K'.O S n b t htm)

end GlobalTheory.UnitLemma.Unr
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPowStatement

section

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.charpoly_overExt_integral_reduction_pow : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction <;> assumption)
end
end

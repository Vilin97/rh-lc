module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.ZMod.QuotientRing
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMulPrimeZmodTensorComplexStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.Finiteness

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiples

section

@[expose] public section

open CategoryTheory Limits

namespace GlobalTheory

theorem ideal_span_natCast_smul_top_eq_range (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ M) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, Nat.cast_smul_eq_nsmul]

noncomputable def intQuotSpanNatLinearEquivZMod (p : ℕ) :
    (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃ₗ[ℤ] ZMod p :=
  LinearEquiv.ofBijective (Int.quotientSpanNatEquivZMod p).toRingHom.toIntAlgHom.toLinearMap
    (Int.quotientSpanNatEquivZMod p).bijective

theorem card_zmod_tensor_eq_card_quot (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  rw [← Nat.card_congr ((intQuotSpanNatLinearEquivZMod p).rTensor M).toEquiv,
    Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(p : ℤ)})).toEquiv,
    ideal_span_natCast_smul_top_eq_range]

theorem card_zmod_tensor_eq_card_quot' : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) :=
  fun M _ _ p => card_zmod_tensor_eq_card_quot M p

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiplesStatement

section

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  first | exact @GlobalTheory.card_zmod_tensor_eq_card_quot' | exact GlobalTheory.card_zmod_tensor_eq_card_quot' | (intros; apply GlobalTheory.card_zmod_tensor_eq_card_quot' <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMul

section

@[expose] public section

open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by
  have h1 : Nat.card B = Nat.card (B ⧸ LinearMap.ker d) * Nat.card (LinearMap.ker d) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker d).toAddSubgroup
  rw [h1, Nat.card_congr d.quotKerEquivRange.toEquiv, e₃, e₁,
    Nat.card_congr g.quotKerEquivRange.toEquiv, e₂, mul_comm]

theorem natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMulStatement

section

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.natCard_homology_of_shortExact_mul' : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  first | exact @GlobalTheory.natCard_homology_of_shortExact_mul | exact GlobalTheory.natCard_homology_of_shortExact_mul | (intros; apply GlobalTheory.natCard_homology_of_shortExact_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalars

section

@[expose] public section

open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalarsStatement

section

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  first | exact @GlobalTheory.natCard_homology_restrictScalars | exact GlobalTheory.natCard_homology_restrictScalars | (intros; apply GlobalTheory.natCard_homology_restrictScalars <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyModPrimeUniversalCoefficients

section

@[expose] public section

open CategoryTheory Limits

namespace GlobalTheory

theorem uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  intro C p _ hinj hfin n
  obtain ⟨π, hz, hS⟩ := GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex C p hinj
  have e := GlobalTheory.T.natCard_homology_of_shortExact_mul' p C _ π hz hS n
  rw [GlobalTheory.T.natCard_homology_restrictScalars_alt] at e
  haveI := hfin n
  haveI := hfin (n + 1)
  have a1 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p
  have a2 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p
  rw [← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples] at a1 a2 e
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcp : Nat.card (ZMod p) = p := by simp
  have c1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))
  have c2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))
  rw [hcp] at c1 c2
  set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n
  have hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0 := by
    intro h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))
  have hD : Nat.card D ≠ 0 := by
    rw [e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite
  have c0 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
  rw [hcp] at c0
  have key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1)))) := by
    rw [pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]; ring
  have := Nat.pow_right_injective hp key
  push_cast; omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyModPrimeUniversalCoefficientsStatement

section

@[expose] public section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  first | exact @GlobalTheory.uct_mod_p | exact GlobalTheory.uct_mod_p | (intros; apply GlobalTheory.uct_mod_p <;> assumption)
end
end

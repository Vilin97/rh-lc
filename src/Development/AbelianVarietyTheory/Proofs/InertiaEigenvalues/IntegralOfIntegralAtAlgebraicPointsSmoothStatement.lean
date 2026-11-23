module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsExtendOfPowDenom
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsMulEqOfSubfieldClosureEqTop
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.InjectiveAlgebraMapOfDvrOfIsIntegral
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.PicardGroup
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom

section

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro m ⟨⟨r, hr⟩, hm⟩
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hmul : algebraMap O A r * m = 0 := by rw [← Algebra.smul_def]; exact hm
  exact (mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)

theorem one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  have key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by
  obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI
  have hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B) :=
    Ideal.map_le_iff_le_comap.mp (hm.trans hIN)
  letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (B ⧸ N)))
  let f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    (Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))
  let g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    ((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)
  refine ⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩
  · rw [RingHom.mem_ker]
    have h0 : IsLocalRing.residue O' a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]
  · rw [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mk N b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]

theorem exists_integral_point_of_complete_case :
    (∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B] (M : Ideal B), M.IsMaximal → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ M → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V := by
  intro H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he
  haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'
  haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB
  obtain ⟨M, hM, hM1, hM2⟩ := exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI
  obtain ⟨P, hPmin, hPM⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)
  haveI : P.IsPrime := hPmin.isPrime
  haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0 := ha
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha')
      hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)
  haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj
  haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P)
      (Ideal.Quotient.mkₐ_surjective O' P)
  have hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_
    intro htop
    have h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, hm1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have hmP : m - 1 ∈ P := Ideal.Quotient.eq.mp (by rw [hm1, map_one])
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))
  have hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤
      M.map (Ideal.Quotient.mk P) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)
  have he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0 := by
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)
  obtain ⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩ :=
    H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'
  refine ⟨V, i₁, i₂, i₃, i₄, i₅,
    φ.toRingHom.comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩
  · ext o
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) =
        algebraMap O' (O' ⊗[O] B) (algebraMap O O' o) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]
    exact φ.commutes _
  · intro x hx
    exact hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv

section

@[expose] public section

namespace GlobalTheory

open Polynomial


open Polynomial in
theorem _root_.GlobalTheory.isIntegral_mul_of_bounded_at_points :
    ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → (∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω], Function.Injective (algebraMap O A) → ∀ (e : A), e ≠ 0 → ∀ f : Ω, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O' V] [Module.Finite O' V] (φ : A →+* V), φ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') → φ e ≠ 0 → ∀ a b : A, f * algebraMap A Ω b = algebraMap A Ω a → φ b ≠ 0 → φ b ∣ φ a) → ∃ s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧ IsIntegral A (algebraMap A Ω s * f) := by
  intro O O' _ _ _ _ _ _ _ _ _ _ _ hpts A Ω _ _ _ _ _ _ _ hOA e he f hf
  by_cases hf0 : f = 0
  · exact ⟨1, by simp, by simp [hf0, isIntegral_zero]⟩
  obtain ⟨d, c, hc, hdc⟩ := IsFractionRing.div_surjective (A := A) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hcΩ : algebraMap A Ω c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hfc : f * algebraMap A Ω c = algebraMap A Ω d := by rw [← hdc, div_mul_cancel₀ _ hcΩ]
  set g : Ω := f⁻¹ with hg
  have hgf : g * f = 1 := inv_mul_cancel₀ hf0
  have hgd : g * algebraMap A Ω d = algebraMap A Ω c := by
    rw [← hfc, ← mul_assoc, hgf, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : π ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hπ.not_isUnit
  let B := Algebra.adjoin A ({g} : Set Ω)
  letI : Algebra O B := ((algebraMap A B).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B :=
    ⟨(Subalgebra.fg_top B).2 (by simpa using Subalgebra.fg_adjoin_finset (R := A) {g})⟩
  haveI : Algebra.FiniteType O B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hOB : Function.Injective (algebraMap O B) := by
    intro x y hxy
    exact hOA (hinj (congrArg Subtype.val hxy))
  let gB : B := ⟨g, Algebra.self_mem_adjoin_singleton A g⟩
  let I : Ideal B := Ideal.span ({gB, algebraMap O B π} : Set B)
  have hI : I = ⊤ := by
    by_contra hI
    have hmI : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    have hec : algebraMap A B (e * c) ≠ 0 := by
      intro h
      exact mul_ne_zero he hc0 (hinj (by simpa using congrArg Subtype.val h))
    obtain ⟨V, _, _, _, _, _, φ, hφ, hφe, hφI⟩ := hpts B hOB I hI hmI _ hec
    let ψ : A →+* V := φ.comp (algebraMap A B)
    have hψ : ψ.comp (algebraMap O A) = (algebraMap O' V).comp (algebraMap O O') := hφ
    have hψec : ψ e * ψ c ≠ 0 := by
      simpa [ψ, map_mul] using hφe
    have hψc : ψ c ≠ 0 := right_ne_zero_of_mul hψec
    obtain ⟨t, ht⟩ := hf V ψ hψ (left_ne_zero_of_mul hψec) d c hfc hψc
    have hmem : φ gB ∈ IsLocalRing.maximalIdeal V := hφI gB (Ideal.subset_span (by simp))
    have h1 : φ gB * ψ d = ψ c := by
      simp only [ψ, RingHom.comp_apply, ← map_mul]
      congr 1
      exact Subtype.ext hgd
    have hu : IsUnit (φ gB) := by
      refine IsUnit.of_mul_eq_one t ?_
      have h2 : ψ c * (φ gB * t) = ψ c * 1 := by linear_combination (-φ gB) * ht + h1
      exact mul_left_cancel₀ hψc h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 hmem) hu
  have hone : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hone
  have hpoly : ∀ x : B, ∃ p : A[X], aeval g p = (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin A ({g} : Set Ω) := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    exact (AlgHom.mem_range _).1 hx
  obtain ⟨p, hp⟩ := hpoly a
  obtain ⟨r, hr⟩ := hpoly b
  have hΩ : (a : Ω) * g + (b : Ω) * algebraMap A Ω (algebraMap O A π) = 1 :=
    congrArg Subtype.val hab
  let H : A[X] := 1 - X * p - C (algebraMap O A π) * r
  have hH : aeval g H = 0 := by
    simp only [H, map_sub, map_one, map_mul, aeval_X, aeval_C, hp, hr]
    linear_combination -hΩ
  letI : Invertible g := invertibleOfNonzero (inv_ne_zero hf0)
  have hrev : aeval f (reverse H) = 0 := by
    have key := eval₂_reverse_mul_pow (algebraMap A Ω) g H
    have hinv : ⅟g = f := by rw [invOf_eq_inv, hg, inv_inv]
    rw [hinv, ← aeval_def, ← aeval_def, hH] at key
    exact (mul_eq_zero.1 key).resolve_right (pow_ne_zero _ (inv_ne_zero hf0))
  have hint := isIntegral_leadingCoeff_smul (reverse H) f hrev
  have hcoeff : H.coeff 0 = 1 - algebraMap O A π * r.coeff 0 := by simp [H]
  refine ⟨H.coeff 0, ?_, ?_⟩
  · rw [hcoeff, sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπm))
  · by_cases h0 : H.coeff 0 = 0
    · rw [h0, map_zero, zero_mul]
      exact isIntegral_zero
    · have hlead : (reverse H).leadingCoeff = H.coeff 0 := by
        rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.2 (Or.inr h0)]
      rw [← hlead, ← Algebra.smul_def]
      exact hint

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfIntegralAtAlgebraicPointsSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.ChartIntegral

open GlobalTheory.Reg.NormalCharts GlobalTheory.PlaceCompletion

theorem exists_quotient_of_bounded (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing A] [IsDomain A]
    [Algebra O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (hOA : Function.Injective (algebraMap O A)) (e : A) (he : e ≠ 0) (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →+* V), (∀ a, φ (algebraMap O A a) = algebraMap O V a) → φ e ≠ 0 →
      ∀ a b : A, f * algebraMap A _ b = algebraMap A _ a → φ b ≠ 0 → φ b ∣ φ a) :
    ∃ x s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧
      f * algebraMap A _ s = algebraMap A _ x := by
  have hid : Function.Injective (algebraMap O O) := fun _ _ h => h
  have : IsLocalHom (algebraMap O O) := ⟨fun _ h => h⟩
  obtain ⟨s, hs, hint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points O O hid
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      O O hid) A (FractionRing A) hOA e he f
    (fun V _ _ _ _ _ φ hφ => hf V φ (fun a => RingHom.congr_fun hφ a))
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨x, s, hs, by rw [hx, _root_.mul_comm]⟩

theorem integral_of_integral_at_algebraic_points :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  intro K Ω _ _ _ _ la gens e hgen he hemem hsm r hr T io n ho ψ hψK hψg
  obtain ⟨T₀, io₀, hov, hfin, hinit⟩ := exists_initial_completion K la
  have hβ : ∀ a : (la.valuation K).valuationSubring,
      io₀ ((la.valuation K).valuationSubring.subtype a) ∈ Set.range (algebraMap T₀.V T₀.Fr) := fun a =>
    exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa hov]
      exact pow_le_one₀ zero_le a.2)
  obtain ⟨J, finJ, A, acr, adom, alg, α, hA, hK, hg, hcov⟩ :=
    GlobalTheory.exists_normal_charts_over_dvr K Ω T₀.V io₀ gens {e} hgen
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        refine ⟨he, Subring.closure_mono ?_ hemem⟩
        refine Set.union_subset_union_left _ ?_
        rintro _ ⟨a, rfl⟩
        exact ⟨_, hβ a, rfl⟩)
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        exact hsm)
  obtain ⟨g, χ, hloc, hχio, hχg, -⟩ := hinit T io n ho
  have hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) :=
    fun a => RingHom.congr_fun hχg a
  obtain ⟨j, φ, hφW, hφO, hφψ⟩ := hcov e (Finset.mem_singleton_self e) T.Fr (imageVal T.V T.Fr) χ ψ
    (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm)
    (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩)
    (fun x hx => (mem_imageVal _).2 (hψg x hx))
  obtain ⟨φ', hφ'⟩ := exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)
  have hc : ∀ a, φ' (algebraMap T₀.V (A j) a) = g a := fun a =>
    IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])
  obtain ⟨hft, -, hic⟩ := hA j
  have hOA : Function.Injective (algebraMap T₀.V (A j)) := by
    intro a b hab
    apply IsFractionRing.injective T₀.V T₀.Fr
    apply χ.injective
    exact (hφO a).symm.trans ((congrArg φ hab).trans (hφO b))
  obtain ⟨eb, heb⟩ : α j e ∈ Set.range (algebraMap (A j) (FractionRing (A j))) := by
    refine (Subring.closure_le (t := (algebraMap (A j) (FractionRing (A j))).range.comap (α j))).2 ?_ hemem
    rintro x (⟨a, rfl⟩ | hx)
    · obtain ⟨x, hx⟩ := hβ a
      have := hK j ((la.valuation K).valuationSubring.subtype a) x 1 (by rw [map_one, _root_.mul_one, hx])
      rw [map_one, map_one, _root_.mul_one] at this
      exact ⟨_, this.symm⟩
    · exact hg j x hx
  have heb0 : eb ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at heb
    exact he heb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T₀.V
  obtain ⟨x, s, hs, hxs⟩ := exists_quotient_of_bounded T₀.V (A j) hOA eb heb0 (α j r) (by
    intro V _ _ _ _ _ ρ hρ h0 a b hab hb
    obtain ⟨hinj, hlocV, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr T₀.V V
    obtain ⟨χ', m, hm, hχ', hv⟩ := exists_ramification (K' := FractionRing V) (F := T₀.Fr)
      (algebraMap T₀.V V) hinj hlocV
    obtain ⟨ψ', hψ'⟩ := (GlobalTheory.Reg.openChart_regular_away K Ω T₀.V (A j) io₀ gens e (α j) eb ϖ hϖ he heb
      (hK j) (hg j)).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp ρ) (by
        change algebraMap V (FractionRing V) (ρ _) ≠ 0
        rw [map_mul, hρ]
        simpa using mul_ne_zero ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) h0)
    replace hψ' : ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j),
        α j r * algebraMap (A j) _ s = algebraMap (A j) _ x →
        ψ' r * algebraMap V _ (ρ s) = algebraMap V _ (ρ x) := hψ'
    let T' : CDVR := { V := V }
    have hψK' : ∀ k : K, ψ' (algebraMap K _ k) = (χ'.comp io₀) k := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := T₀.V) (io₀ k)
      have hb0 : algebraMap T₀.V T₀.Fr b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
      have h1 : io₀ k * algebraMap T₀.V _ b = algebraMap T₀.V _ a := by
        rw [← hab, div_mul_cancel₀ _ hb0]
      have h2 := hψ' (algebraMap K _ k) _ _ (hK j k a b h1)
      rw [hρ, hρ, ← hχ', ← hχ', ← h1, map_mul] at h2
      exact mul_right_cancel₀ ((map_ne_zero χ').2 hb0) h2
    obtain ⟨v, hv'⟩ : ψ' r ∈ Set.range (algebraMap V (FractionRing V)) :=
      hr T' (χ'.comp io₀) (m * 1) (hov.bc χ' hm hv) (hfin' hfin) ψ' hψK' (fun y hy => by
        obtain ⟨x, hx⟩ := hg j y hy
        have := hψ' y x 1 (by rw [map_one, _root_.mul_one, hx])
        rw [map_one, map_one, _root_.mul_one] at this
        exact ⟨ρ x, this.symm⟩)
    refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [← hψ' r a b hab, ← hv', map_mul, _root_.mul_comm])
  have hm : φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := by
    refine (Ideal.map_le_iff_le_comap (K := (IsLocalRing.maximalIdeal T.V).comap φ')).2 ?_ hs
    intro a ha
    change φ' (algebraMap T₀.V (A j) a) ∈ IsLocalRing.maximalIdeal T.V
    rw [hc]
    exact fun hu => ha (hloc.map_nonunit a hu)
  have hu : IsUnit (φ' s) := by
    by_contra hnu
    have h1 : φ' s - φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := sub_mem hnu hm
    rw [← map_sub, sub_sub_cancel, map_one] at h1
    exact h1 isUnit_one
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 := hφψ r x s hxs
  refine ⟨φ' x * w, ?_⟩
  rw [map_mul, hφ', ← h2, ← hφ', _root_.mul_assoc, ← map_mul, hw, map_one, _root_.mul_one]

end GlobalTheory.ChartIntegral
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfIntegralAtAlgebraicPointsSmoothStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  first | exact @GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | exact GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points | (intros; apply GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points <;> assumption)
end
end

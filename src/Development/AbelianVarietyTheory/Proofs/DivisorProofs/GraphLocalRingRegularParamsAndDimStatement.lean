module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulKerMemSpanTrBasisDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegComplexBaseChangeEq

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem algebraicIndependent_one_tmul_of_field {k K L ι : Type} [Field k] [Field K] [CommRing L] [Algebra k K] [Algebra k L]
    {t : ι → L} (ht : AlgebraicIndependent k t) :
    AlgebraicIndependent K (fun i => (1 : K) ⊗ₜ[k] t i) := by
  rw [algebraicIndependent_iff_injective_aeval] at ht ⊢
  have h1 : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L).toLinearMap ht
  have h2 : (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[k] t i) : MvPolynomial ι K →ₐ[K] K ⊗[k] L) =
      (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval t : MvPolynomial ι k →ₐ[k] L)).comp
        (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.toAlgHom := by
    ext i
    simp
  rw [h2]
  exact h1.comp (MvPolynomial.algebraTensorAlgEquiv k K (σ := ι)).symm.injective

theorem trdeg_tensorProduct_eq {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsDomain (K ⊗[k] L)] : Algebra.trdeg K (K ⊗[k] L) = Algebra.trdeg k L := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hi := algebraicIndependent_one_tmul_of_field (K := K) hs.1
  set S := Algebra.adjoin K (Set.range fun i : s => (1 : K) ⊗ₜ[k] (i : L)) with hS
  have halg : Algebra.IsAlgebraic S (K ⊗[k] L) := by
    have hA := hs.isAlgebraic
    set T := Algebra.adjoin k (Set.range (Subtype.val : s → L)) with hT
    have hmem : ∀ x : T, (1 : K) ⊗ₜ[k] (x : L) ∈ S := by
      rintro ⟨x, hx⟩
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      | algebraMap r =>
        have : (1 : K) ⊗ₜ[k] (algebraMap k L r) = algebraMap K (K ⊗[k] L) (algebraMap k K r) := by
          rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] L)]
        simp only [this]
        exact S.algebraMap_mem _
      | add x y hx hy ihx ihy =>
        simp only [TensorProduct.tmul_add]
        exact S.add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
        have : (1 : K) ⊗ₜ[k] (x * y) = ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) := by simp
        simp only [this]
        exact S.mul_mem ihx ihy
    let g : L →+* K ⊗[k] L := (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := L)).toRingHom
    let f : T →+* S := (g.comp T.val.toRingHom).codRestrict S hmem
    have hf : Function.Injective f := by
      intro x y hxy
      have : g x = g y := congrArg Subtype.val hxy
      exact Subtype.ext (g.injective this)
    refine ⟨fun z => ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => exact isAlgebraic_zero
    | add x y hx hy => exact hx.add hy
    | tmul a b =>
      have h1 : IsAlgebraic S (g b) :=
        (hA.isAlgebraic b).ringHom_of_comp_eq f g hf (by ext; rfl)
      have h2 : IsAlgebraic S (algebraMap S (K ⊗[k] L) (algebraMap K S a)) := isAlgebraic_algebraMap _
      have h3 : a ⊗ₜ[k] b = algebraMap S (K ⊗[k] L) (algebraMap K S a) * g b := by
        simp [g]
      rw [h3]
      exact h2.mul h1
  have hb : IsTranscendenceBasis K (fun i : s => (1 : K) ⊗ₜ[k] (i : L)) :=
    hi.isTranscendenceBasis_iff_isAlgebraic.mpr halg
  rw [← hb.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]

theorem trdeg_complex_baseChange_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' :=
  trdeg_tensorProduct_eq

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegComplexBaseChangeEqStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.trdeg_tensor_complex_eq : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] [IsDomain (K ⊗[ℂ] κ')], Algebra.trdeg K (K ⊗[ℂ] κ') = Algebra.trdeg ℂ κ' := by
  first | exact @GlobalTheory.trdeg_complex_baseChange_eq | exact GlobalTheory.trdeg_complex_baseChange_eq | (intros; apply GlobalTheory.trdeg_complex_baseChange_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDim

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem ennreal_volume_ratio_step_cancel (d : WithBot ℕ∞) (m n : ℕ) (hd : d + m = ((n + m : ℕ) : WithBot ℕ∞)) : d = n := by
  induction d using WithBot.recBotCoe with
  | bot =>
    exfalso
    simp at hd
    exact absurd hd.symm (by simp [WithBot.add_eq_bot])
  | coe e =>
    have h1 : e + (m : ℕ∞) = (n : ℕ∞) + (m : ℕ∞) := by exact_mod_cast hd
    have h2 : e = n := WithTop.add_right_cancel (ENat.natCast_ne_top m) h1
    subst h2
    rfl

theorem isLocModel_top {K : Type} [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K] :
    IsLocModel (algebraMap ℂ K) (⊤ : Subring K) :=
  { const_mem := fun _ => Subring.mem_top _
    isLocalRing := (Subring.topEquiv (R := K)).symm.isLocalRing
    essFiniteType := by
      let e := (Subring.topEquiv (R := K)).symm
      exact RingHom.EssFiniteType.comp (RingHom.essFiniteType_algebraMap.mpr inferInstance)
        (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    frac := fun f => ⟨f, Subring.mem_top _, 1, Subring.mem_top _, one_ne_zero, mul_one f⟩ }

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']
  (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]

theorem maximalIdeal_eq_span (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] (hx : TrBasis (algebraMap ℂ K) x) :
    IsLocalRing.maximalIdeal (loc L σ) =
      Ideal.span (Set.range fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) := by
  obtain ⟨e, he1, he⟩ := GlobalTheory.FieldPair.exists_mul_ker_mem_span_trBasis_diff n x σ (⊤ : Subring K) hx
    isLocModel_top
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime :=
    RingHom.ker_isPrime _
  have heP : e ∈ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro h
    rw [RingHom.mem_ker] at h
    rw [h] at he1
    exact zero_ne_one he1
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
      ↥(loc L σ) := by
    exact Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))) ↥(loc L σ)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    obtain ⟨u, hu⟩ := IsLocalization.map_units
      (M := (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl)
      (S := ↥(loc L σ)) ⟨e, heP⟩
    have h1 := Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) (he a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h1
    have h2 : algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) a =
        ((u⁻¹ : (↥(loc L σ))ˣ) : ↥(loc L σ)) * algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (e * a) := by
      rw [map_mul, show algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) e = (u : ↥(loc L σ)) from hu.symm,
        ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) ?_
    rw [RingHom.mem_ker]
    simp

theorem ringKrullDim_loc (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] [Algebra.EssFiniteType ℂ κ'] (hx : TrBasis (algebraMap ℂ K) x) :
    ringKrullDim (loc L σ) = n := by
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime := RingHom.ker_isPrime _
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl ↥(loc L σ) :=
    Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  letI : Algebra ℂ ↥(loc L σ) :=
    ((algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') ↥(loc L σ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')
  haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') ↥(loc L σ) :=
    Algebra.EssFiniteType.of_isLocalization _ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  haveI : Algebra.EssFiniteType ℂ ↥(loc L σ) := Algebra.EssFiniteType.comp ℂ (K ⊗[ℂ] κ') ↥(loc L σ)
  have hg : ∀ y : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl,
      IsUnit ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).toRingHom (y : K ⊗[ℂ] κ')) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact y.2 (RingHom.mem_ker.mpr h)
  letI : Algebra ↥(loc L σ) κ' := (IsLocalization.lift hg).toAlgebra
  haveI : IsScalarTower ℂ ↥(loc L σ) κ' := IsScalarTower.of_algebraMap_eq fun c =>
    ((IsLocalization.lift_eq hg (algebraMap ℂ (K ⊗[ℂ] κ') c)).trans
      ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).commutes c)).symm
  have hsurj : Function.Surjective (algebraMap ↥(loc L σ) κ') := fun b =>
    ⟨algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (1 ⊗ₜ b), by
      show IsLocalization.lift hg _ = b
      rw [IsLocalization.lift_eq]
      simp⟩
  have hx' : IsTranscendenceBasis ℂ x := by
    unfold TrBasis at hx
    rwa [toAlgebra_algebraMap] at hx
  have hK : Algebra.trdeg ℂ K = n := by
    rw [← hx'.cardinalMk_eq_trdeg, Cardinal.mk_fin]
  have hfin : Algebra.trdeg ℂ κ' < Cardinal.aleph0 := by
    exact trdeg_lt_aleph0 ℂ κ'
  have hm : Algebra.trdeg ℂ κ' = ((Algebra.trdeg ℂ κ').toNat : Cardinal) :=
    (Cardinal.cast_toNat_of_lt_aleph0 hfin).symm
  haveI : FaithfulSMul ℂ K :=
    (faithfulSMul_iff_algebraMap_injective ℂ K).mpr (algebraMap ℂ K).injective
  haveI : FaithfulSMul K (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective K (K ⊗[ℂ] κ')).mpr (algebraMap K (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul ℂ (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective ℂ (K ⊗[ℂ] κ')).mpr (algebraMap ℂ (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul (K ⊗[ℂ] κ') ↥(loc L σ) :=
    (faithfulSMul_iff_algebraMap_injective (K ⊗[ℂ] κ') ↥(loc L σ)).mpr
      (IsLocalization.injective ↥(loc L σ) (Ideal.primeCompl_le_nonZeroDivisors (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')))))
  haveI : Algebra.IsAlgebraic (K ⊗[ℂ] κ') ↥(loc L σ) :=
    IsLocalization.isAlgebraic ↥(loc L σ) (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  have hR : Algebra.trdeg ℂ ↥(loc L σ) = ((n + (Algebra.trdeg ℂ κ').toNat : ℕ) : Cardinal) := by
    have h0 : Algebra.trdeg (K ⊗[ℂ] κ') ↥(loc L σ) = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℂ (K ⊗[ℂ] κ') (A := ↥(loc L σ)), h0, add_zero,
      ← trdeg_add_eq ℂ K (A := K ⊗[ℂ] κ'), GlobalTheory.T.trdeg_tensor_complex_eq, hK, hm]
    push_cast
    rfl
  exact ennreal_volume_ratio_step_cancel _ _ _
    (GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := ℂ) (R := ↥(loc L σ)) (Ω := κ') hsurj hm hR)

theorem maximalIdeal_eq_span_and_ringKrullDim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n x hK hκ hx
  exact ⟨maximalIdeal_eq_span L σ n x hx, ringKrullDim_loc L σ n x hx⟩

end GlobalTheory.DiagLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDimStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.graphLocalRing_regular_params_and_dim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  first | exact @GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | exact GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | (intros; apply GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim <;> assumption)
end
end

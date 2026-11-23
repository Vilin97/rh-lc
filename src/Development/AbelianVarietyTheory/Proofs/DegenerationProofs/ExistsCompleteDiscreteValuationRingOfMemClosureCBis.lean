module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureC

section

@[expose] public section

open scoped BigOperators
open IsLocalRing

namespace GlobalTheory

theorem coeff_aeval_C_mul_X {K A J : Type*} [CommRing K] [CommRing A] [Algebra K A] (w : J → A)
    (G : MvPolynomial J K) (d : ℕ) :
    (MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X) G).coeff d =
      MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X)
        (MvPolynomial.monomial u a) =
        Polynomial.C (MvPolynomial.aeval w (MvPolynomial.monomial u a)) *
          Polynomial.X ^ u.degree := by
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply,
        mul_assoc]
      rfl
    rw [h, Polynomial.coeff_C_mul_X_pow, MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.isHomogeneous_monomial a (rfl : u.degree = u.degree))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem exists_complete_discreteValuationRing_of_mem_closure_cone :
    ∀ (K A J : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Fintype J], Algebra.FiniteType K A → ∀ (w : J → A) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d → MvPolynomial.aeval w G = 0 → MvPolynomial.eval v G = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A →ₐ[K] FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro K A J _ _ _ _ _ hA w v hv hG
  let L := FractionRing (Polynomial A)
  have hinj : Function.Injective (algebraMap (Polynomial A) L) := IsFractionRing.injective _ _
  have : Algebra.EssFiniteType (Polynomial A) L := .of_isLocalization L (nonZeroDivisors _)
  have : Algebra.FiniteType K (Polynomial A) := .trans hA inferInstance
  have : Algebra.EssFiniteType K L := .comp K (Polynomial A) L
  let ψ : MvPolynomial J K →ₐ[K] Polynomial A :=
    MvPolynomial.aeval fun j => Polynomial.C (w j) * Polynomial.X
  let Φ : MvPolynomial J K →+* L := (algebraMap (Polynomial A) L).comp ψ.toRingHom
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval v) := by
    intro G h
    have h1 : ψ G = 0 := hinj (h.trans (map_zero _).symm)

    rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent G, map_sum]
    refine Finset.sum_eq_zero fun d _ => hG _ d (MvPolynomial.homogeneousComponent_isHomogeneous d G) ?_
    rw [← coeff_aeval_C_mul_X]
    change (ψ G).coeff d = 0
    rw [h1, Polynomial.coeff_zero]
  have hne : (RingHom.ker (MvPolynomial.eval v)).map Φ.rangeRestrict ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, Ideal.mem_map_iff_of_surjective _ Φ.rangeRestrict_surjective]
    rintro ⟨G, h1, h2⟩
    have h3 : G - 1 ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_one, sub_eq_zero]
      exact congrArg Subtype.val h2
    have h4 := hker h3
    rw [RingHom.mem_ker] at h1 h4
    simp [h1] at h4
  obtain ⟨U, hU, hU'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := Φ.range) _ hne
  have hC : ∀ r : K, Φ (MvPolynomial.C r) = algebraMap K L r := fun r => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial A) L, ← ψ.commutes]
    rfl
  let t : J → L := fun j => Φ (MvPolynomial.X j - MvPolynomial.C (v j))
  have ht : ∀ j, t j = algebraMap (Polynomial A) L
      (Polynomial.C (w j) * Polynomial.X - Polynomial.C (algebraMap K A (v j))) := fun j => by
    simp [t, Φ, ψ]
  obtain ⟨V, hV, hKV, -, htV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := K) U
    (fun r => hU ⟨_, hC r⟩) Set.finite_empty (Set.finite_range t) (by simp)
    (by
      rintro _ ⟨j, rfl⟩
      exact hU' ⟨_, Ideal.mem_map_of_mem _
        (show MvPolynomial.X j - MvPolynomial.C (v j) ∈ _ by simp [RingHom.mem_ker]), rfl⟩)
    (by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      refine ⟨_, ⟨j, rfl⟩, fun h => hj ?_⟩
      rw [ht, map_eq_zero_iff _ hinj] at h
      simpa using congrArg (fun p : Polynomial A => p.coeff 0) h)
  let W := AdicCompletion (maximalIdeal V) V
  let κ : K →+* V := (algebraMap K L).codRestrict V hKV
  let ι : V →+* W := algebraMap V W
  letI : Algebra K W := (ι.comp κ).toAlgebra
  have hι : Function.Injective ((algebraMap W (FractionRing W)).comp ι) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let g : L →+* FractionRing W := IsFractionRing.lift hι
  have hg : ∀ x : V, g x = algebraMap W (FractionRing W) (ι x) := fun x =>
    IsFractionRing.lift_algebraMap hι x
  let f : A →ₐ[K] FractionRing W :=
    { g.comp ((algebraMap (Polynomial A) L).comp Polynomial.C) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply K W (FractionRing W)]
        exact hg (κ r) }
  have htm : ∀ j, t j ∈ V := fun j => V.nonunits_subset (htV _ ⟨j, rfl⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, f,
    g (algebraMap (Polynomial A) L Polynomial.X), fun j => ι (⟨t j, htm j⟩ + κ (v j)),
    inferInstance, ?_, fun j => ⟨?_, ?_⟩⟩
  · rw [map_ne_zero, map_ne_zero_iff _ hinj]
    exact Polynomial.X_ne_zero
  · rw [← hg]
    change g (t j + algebraMap (Polynomial A) L (Polynomial.C (algebraMap K A (v j)))) =
      _ * g (algebraMap (Polynomial A) L (Polynomial.C (w j)))
    rw [ht, ← map_add (f := _), sub_add_cancel, mul_comm, map_mul, map_mul]
  · change ι _ - ι (κ (v j)) ∈ _
    rw [← map_sub, add_sub_cancel_right]
    exact map_nonunit ι _
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨t j, htm j⟩)).mp (htV _ ⟨j, rfl⟩))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureCones

section

@[expose] public section

open scoped BigOperators TensorProduct

namespace GlobalTheory

theorem sum_mul_eq_zero_of_forall_dual {F K σ : Type} [Field F] [Field K] [Algebra F K]
    (S : Finset σ) (c m : σ → K)
    (h : ∀ l : K →ₗ[F] F, ∑ s ∈ S, l (c s) • m s = 0) : ∑ s ∈ S, c s * m s = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F K
  let T := S.biUnion fun s => (b.repr (c s)).support
  have hc : ∀ s ∈ S, c s = ∑ j ∈ T, b.coord j (c s) • b j := fun s hs => by
    conv_lhs => rw [← b.linearCombination_repr (c s)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := T)]
    · rfl
    · exact Finset.subset_biUnion_of_mem (fun s => (b.repr (c s)).support) hs
    · simp
  calc ∑ s ∈ S, c s * m s = ∑ s ∈ S, ∑ j ∈ T, b j * (b.coord j (c s) • m s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        conv_lhs => rw [hc s hs]
        rw [Finset.sum_mul]
        simp
    _ = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.mul_sum, h, mul_zero]

theorem eval_eq_zero_of_aeval_tmul_eq_zero {F K J ι : Type} [Field F] [Field K] [Algebra F K]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (w : ∀ i, J → A i) (v : J → K)
    (h : ∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0)
    (G : MvPolynomial J K) (d : ℕ) (hG : G.IsHomogeneous d)
    (h0 : ∀ i, MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) G = 0) :
    MvPolynomial.eval v G = 0 := by
  rw [MvPolynomial.eval_eq]
  refine sum_mul_eq_zero_of_forall_dual (F := F) _ _ _ fun l => ?_
  have key : ∀ (B : Type) [CommRing B] [Algebra F B] (u : J → B),
      MvPolynomial.aeval u (∑ s ∈ G.support, MvPolynomial.monomial s (l (G.coeff s))) =
        ∑ s ∈ G.support, l (G.coeff s) • ∏ j ∈ s.support, u j ^ s j := fun B _ _ u => by

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.aeval_monomial, Algebra.smul_def]
    rfl
  rw [← key]
  refine h _ d (MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_) fun i => ?_
  · refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hG (MvPolynomial.mem_support_iff.mp hs)
  · rw [key]
    have h1 := congrArg ((TensorProduct.lid F (A i)).toLinearMap ∘ₗ l.rTensor (A i)) (h0 i)

    rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h2 : algebraMap K (K ⊗[F] A i) (G.coeff s) * ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
        = G.coeff s ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
      have : ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
          = (1 : K) ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
        simp only [← Algebra.TensorProduct.includeRight_apply (R := F) (A := K), map_prod, map_pow]
      rw [this]
      simp
    rw [h2]
    simp

theorem exists_complete_discreteValuationRing_of_mem_closure_cones :
    ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro F K J ι _ _ _ _ _ A _ _ hA w v hv h
  classical
  have hN : ∀ i, IsNoetherianRing (K ⊗[F] A i) := fun i =>
    Algebra.FiniteType.isNoetherianRing K _
  by_cases hex : ∃ (i : ι) (P : Ideal (K ⊗[F] A i)), P ∈ minimalPrimes (K ⊗[F] A i) ∧
      ∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d →
        MvPolynomial.aeval (fun j => Ideal.Quotient.mk P ((1 : K) ⊗ₜ[F] w i j)) G = 0 →
        MvPolynomial.eval v G = 0
  · obtain ⟨i, P, hP, hG⟩ := hex
    have : P.IsPrime := hP.1.1
    obtain ⟨W, _, _, _, _, f, s, w', h1, h2, h3⟩ :=
      exists_complete_discreteValuationRing_of_mem_closure_cone K ((K ⊗[F] A i) ⧸ P) J
        inferInstance _ v hv hG
    refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance,
      f.toRingHom.comp ((Ideal.Quotient.mk P).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := A i)).toRingHom),
      s, w', h1, h2, fun x => ?_, h3⟩
    rw [← IsScalarTower.algebraMap_apply K W (FractionRing W), ← f.commutes]
    change f (Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (R := F) (A := K)
      (algebraMap F (A i) x))) = f (Ideal.Quotient.mk P (algebraMap K _ (algebraMap F K x)))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · exfalso
    push_neg at hex
    choose G d hG hG0 hGv using hex
    have : ∀ i, Finite (minimalPrimes (K ⊗[F] A i)) := fun i =>
      (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
    letI : Fintype (Σ i, minimalPrimes (K ⊗[F] A i)) := Fintype.ofFinite _
    let H : MvPolynomial J K := ∏ x : Σ i, minimalPrimes (K ⊗[F] A i), G x.1 x.2.1 x.2.2
    have hH : H.IsHomogeneous (∑ x : Σ i, minimalPrimes (K ⊗[F] A i), d x.1 x.2.1 x.2.2) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun x _ => hG _ _ _
    have hHv : MvPolynomial.eval v H ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun x _ => hGv _ _ _
    have hnil : ∀ i, IsNilpotent (MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) H) := by
      intro i
      rw [nilpotent_iff_mem_prime]
      intro Q hQ
      obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
      refine hPQ ?_
      rw [map_prod]
      refine Ideal.prod_mem P (Finset.mem_univ
        (⟨i, P, hP⟩ : Σ i, minimalPrimes (K ⊗[F] A i))) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG0 i P hP]
      exact MvPolynomial.comp_aeval_apply _ (Ideal.Quotient.mkₐ K P) _
    choose n hn using hnil
    letI : Fintype ι := Fintype.ofFinite ι
    refine pow_ne_zero (∑ i, n i) hHv ?_
    rw [← map_pow]
    refine eval_eq_zero_of_aeval_tmul_eq_zero A w v h _ _ (hH.pow _) fun i => ?_
    rw [map_pow]
    exact pow_eq_zero_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)) (hn i)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureCBis

section

@[expose] public section

open scoped BigOperators TensorProduct

theorem _root_.GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt : ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  first | exact @GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones | exact GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones | (intros; apply GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones <;> assumption)
end
end

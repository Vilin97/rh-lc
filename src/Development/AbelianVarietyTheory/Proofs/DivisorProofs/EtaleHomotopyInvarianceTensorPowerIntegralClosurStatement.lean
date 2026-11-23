module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyCloseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDim
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdealsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRootsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFgStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDimStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  first | (exact @GlobalTheory.hInv_of_integral_killed_of_lower) | (exact GlobalTheory.hInv_of_integral_killed_of_lower) | (intros; apply GlobalTheory.hInv_of_integral_killed_of_lower  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosuStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirst

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  intro R A _ _ _ k F
  classical
  set S := firstAndFinite R A k F with hS
  let g : Fin (k + 1) × F → S := fun p =>
    ⟨PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) p.1 p.2.1,
      Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨p.1, p.2.1, p.2.2, rfl⟩))⟩
  refine ⟨Finset.univ.image g, ?_⟩
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  conv_rhs => rw [hS, firstAndFinite]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨⟨i, a, ha⟩, rfl⟩, rfl⟩
      exact ⟨i, a, ha, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨g (i, ⟨a, ha⟩), ⟨(i, ⟨a, ha⟩), rfl⟩, rfl⟩

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirstStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_fg_over_first) | (exact GlobalTheory.EtC.firstAndFinite_fg_over_first) | (intros; apply GlobalTheory.EtC.firstAndFinite_fg_over_first  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegral

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegralStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem hInv_of_finite_over_aic (q : ℕ) [NeZero q] (d : ℕ) (hH : (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R))
    (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D] (hq : IsUnit (q : D))
    (hd : ringKrullDim D ≤ d) (T : Type) [CommRing T] [IsDomain T] [Algebra D T]
    [Algebra.IsIntegral D T] (hT : AIC T) (hTq : HInv q T) (E : Type) [CommRing E] [Algebra D E]
    [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) : HInv q E := by
  have hlow := GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim q d hH D hq hd
  have hqE : IsUnit (q : E) := by simpa using hq.map (algebraMap D E)
  set X : Finset (E →ₐ[D] T) := (GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain D T E ι F hF).toFinset with hX
  have hXid : ∀ χ ∈ X, χ.comp ι = AlgHom.id D T := fun χ hχ => by simpa [hX] using hχ
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals D E (E →ₐ[D] T) X (fun χ => RingHom.ker χ)
    (fun χ hχ => GlobalTheory.T.ker_retraction_fg_of_adjoin_finset D T E ι F hF χ (hXid χ hχ))
    (fun Q hQ hQc => by
      obtain ⟨χ, hχι, hχQ⟩ := GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots D T E hT ι Q hQ hQc
      have hmem : χ ∈ X := by simpa [hX] using hχι
      rw [← hχQ]
      exact iInf₂_le χ hmem)
  set I : Ideal E := ⨅ χ ∈ X, RingHom.ker χ with hI
  set J : Ideal E := Ideal.span {algebraMap D E s} with hJ
  have hIJ : I ⊓ J ≤ nilradical E := by
    intro y hy
    obtain ⟨hyI, hyJ⟩ := Ideal.mem_inf.mp hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyJ
    obtain ⟨m, hm⟩ := hs _ hyI
    refine ⟨2 * m, ?_⟩
    calc (a * algebraMap D E s) ^ (2 * m)
        = a ^ m * (algebraMap D E s * (a * algebraMap D E s)) ^ m := by ring
      _ = 0 := by rw [hm, mul_zero]
  have hJs : ∀ K : Ideal E, J ≤ K → algebraMap D (E ⧸ K) s = 0 := by
    intro K hK
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ K), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hK (Ideal.mem_span_singleton_self _)
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q E I J hIJ hqE (GlobalTheory.T.hInv_quot_iInf_ker_retractions q D T E hq hTq hlow ι X hXid)
    (hlow (E ⧸ J) s hs0 (hJs J le_rfl)) (hlow (E ⧸ (I ⊔ J)) s hs0 (hJs _ le_sup_right))

def subalgebraOfSubringEquiv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    S ≃+* subalgebraOfSubring S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem hInv_tensorPower_integralClosure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  intro q _ d hH D _ _ _ hq hd k
  have hqDp : IsUnit (q : integralClosure D (AlgebraicClosure (FractionRing D))) := by
    simpa using hq.map (algebraMap D (integralClosure D (AlgebraicClosure (FractionRing D))))
  have hTq := GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed q _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hqDp
  have hqS : ∀ F, IsUnit (q : firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F) :=
    fun F => by simpa using hq.map (algebraMap D (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  refine GlobalTheory.T.hInv_of_directed_union_subalgebras q _ (Finset (integralClosure D (AlgebraicClosure (FractionRing D))))
    (fun F => subalgebraOfSubring (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F).toSubring)
    ?_ ?_ ?_ ?_
  · intro F G hFG x hx
    rw [mem_subalgebraOfSubring] at hx ⊢
    exact Algebra.adjoin_mono (Set.union_subset_union_right _
      (Set.iUnion_mono fun i => Set.image_mono (Finset.coe_subset.mpr hFG))) hx
  · intro x
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset D _ k x
    exact ⟨F, (mem_subalgebraOfSubring).mpr hF⟩
  · intro F
    simpa using (hqS F).map (subalgebraOfSubringEquiv (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  · intro F
    haveI := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    obtain ⟨F', hF'⟩ := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (subalgebraOfSubringEquiv _)
      (hInv_of_finite_over_aic q d hH D hq hd _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hTq _ (firstIncl D _ k F) F' hF')

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosurStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  first | (exact @GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (exact GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (intros; apply GlobalTheory.EtC.hInv_tensorPower_integralClosure  <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosurStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLt

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem hInv_quot_inf (q : ℕ) [NeZero q] (R : Type) [CommRing R] (I J : Ideal R)
    (hq : IsUnit (q : R)) (hI : HInv q (R ⧸ I)) (hJ : HInv q (R ⧸ J))
    (hIJ : HInv q (R ⧸ (I ⊔ J))) : HInv q (R ⧸ (I ⊓ J)) := by
  set K := I ⊓ J with hK
  let f := Ideal.Quotient.mk K
  have hqA : IsUnit (q : R ⧸ K) := by simpa using hq.map f
  have hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2
    have h1 : b - a ∈ K := Ideal.Quotient.eq.mp hab
    have haJ : a ∈ J := by
      have := J.sub_mem hb h1.2
      simpa using this
    have : f a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩
    rw [this]
    exact (nilradical (R ⧸ K)).zero_mem
  have eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
  have eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE inf_le_right
  have eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J) :=
    (Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ)
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eIJ.symm hIJ)

theorem ringKrullDim_quot_sup_succ_le (R : Type) [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : ¬ J ≤ p) : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hJ
  let g := Ideal.Quotient.mk p
  have hx0 : g x ≠ 0 := fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : g x ∈ nonZeroDivisors (R ⧸ p) := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE le_sup_left
  have h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) :=
    ringKrullDim_le_of_surjective e.toRingHom e.surjective
  have h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1 := by
    gcongr
    exact h3.trans h2
  exact h4.trans h1

theorem withBot_lt_of_add_one_le (a : WithBot ℕ∞) (d : ℕ) (h : a + 1 ≤ (d : WithBot ℕ∞)) :
    a < (d : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe] at h2
      simp at h2
    | coe n =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h
      have : n + 1 ≤ d := by exact_mod_cast h'
      have : n < d := by omega
      exact_mod_cast this

end GlobalTheory

namespace GlobalTheory

theorem hInv_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ),
    (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) →
    (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) →
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  intro q _ d hlt hdom R _ _ hq hd
  have key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance
    | insert p s hps ih =>
      intro hs
      have hp : p.IsPrime := hs p (Finset.mem_insert_self p s)
      have ihs := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      rw [Finset.inf_insert, id]
      by_cases hJ : s.inf id ≤ p
      · rw [inf_eq_right.mpr hJ]; exact ihs
      · haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ p))
          all_goals first | rfl | exact Subsingleton.elim _ _
        haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))
          all_goals first | rfl | exact Subsingleton.elim _ _
        refine hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_
        · exact hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p))
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
        · refine hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_
          refine withBot_lt_of_add_one_le _ d ?_
          exact (ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hN : hfin.toFinset.inf id = nilradical R := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]
    rfl
  have hred : HInv q (R ⧸ nilradical R) := by
    rw [← hN]
    refine key _ (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    exact hp.1.1
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLtStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  first | (exact @GlobalTheory.hInv_of_domains_of_dim_lt) | (exact GlobalTheory.hInv_of_domains_of_dim_lt) | (intros; apply GlobalTheory.hInv_of_domains_of_dim_lt  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselian

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem GlobalTheory.homotopyInvariance_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  classical
  intro q _ A _ _ hq
  have hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R := by
    intro d
    induction d with
    | zero =>
      intro R _ _ _ hd
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
    | succ d ih =>
      intro R _ _ hR hd
      have hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D := by
        intro D _ _ _ hD hDd
        refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)
        intro x hx
        have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
          rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
          exact (algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))
        have h0 : x = 0 := by
          apply hinj
          have := congrArg Subtype.val (RingHom.mem_ker.mp hx)
          simpa using this
        rw [h0]; exact zero_mem _
      refine GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_
      revert hd
      induction ringKrullDim R with
      | bot => intro _; exact bot_le
      | coe n =>
        intro h
        have h' : n < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))
  let S : Finset A → Subalgebra ℤ A := fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))
  have hmono : Monotone S := fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))
  have hcov : ∀ a, ∃ s, a ∈ S s := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  have hunit : ∀ s, IsUnit (q : S s) := by
    intro s
    have hm : (↑(hq.unit⁻¹) : A) ∈ S s := Algebra.subset_adjoin (Set.mem_insert _ _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    simp
  have hinv : ∀ s, HInv q (S s) := by
    intro s
    have : Algebra.FiniteType ℤ (S s) := by
      have hfg' : (S s).FG := by
        have : (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A) := by simp
        rw [show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]
        exact Subalgebra.fg_adjoin_finset _
      exact Subalgebra.fg_iff_finiteType _ |>.mp hfg'
    have hlt := GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d := by
      revert hlt
      induction ringKrullDim (S s) with
      | bot => intro _; exact ⟨0, bot_le⟩
      | coe n =>
        intro h
        induction n with
        | top => exact absurd h (lt_irrefl _)
        | coe m => exact ⟨m, le_rfl⟩
    exact hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  intro i
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselianStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  first | (exact @GlobalTheory.homotopyInvariance_strictlyHenselian) | (exact GlobalTheory.homotopyInvariance_strictlyHenselian) | (intros; apply GlobalTheory.homotopyInvariance_strictlyHenselian  <;> assumption)
end
end

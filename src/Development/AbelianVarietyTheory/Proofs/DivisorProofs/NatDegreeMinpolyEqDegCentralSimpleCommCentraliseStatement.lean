module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.PicardGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import GroundTheory.Brauer.Degree

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenspacesOfSeparableMinpoly

section

@[expose] public section

open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.EigSum

theorem finrank_eigenspaces_of_separable_minpoly
    (Ω V : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] (T : Module.End Ω V) (f : Polynomial Ω) (hm : f.Monic)
    (hs : f.Separable) (h0 : Polynomial.aeval T f = 0)
    (hmin : ∀ g : Polynomial Ω, Polynomial.aeval T g = 0 → f ∣ g) :
    ∑ z ∈ f.roots.toFinset, Module.finrank Ω (T.eigenspace z) = Module.finrank Ω V ∧
      ∀ z ∈ f.roots, T.eigenspace z ≠ ⊥ := by
  have hf : f = minpoly Ω T := by
    apply Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    exact associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)
  have hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots := by
    intro z
    rw [Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  refine ⟨?_, fun z hz => (hroot z).2 hz⟩
  set s := f.roots.toFinset
  let N : s → Submodule Ω V := fun z => T.eigenspace z
  have hind : iSupIndep N :=
    iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective
  have htop : ⨆ z, N z = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top T
    simp only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    rw [eq_top_iff, ← h1]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup N ⟨μ, hμ⟩
    · have : ¬ T.HasEigenvalue μ := by
        rw [hroot]; simpa [s] using hμ
      rw [Module.End.hasEigenvalue_iff, not_not] at this
      simp [this]
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq,
    Module.finrank_directSum]
  exact (Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm

end GlobalTheory.EigSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegCommutant

theorem exists_not_commute_of_two_le_finrank {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (h : 2 ≤ Module.finrank K E) :
    ∃ S₁ S₂ : Module.End K E, S₁ * S₂ ≠ S₂ * S₁ := by
  let b := Module.finBasis K E
  let e := LinearMap.toMatrixAlgEquiv b
  let i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨e.symm (Matrix.single i0 i1 1), e.symm (Matrix.single i1 i0 1), ?_⟩
  intro hc
  have h2 := congrArg e hc
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h2
  have h3 := congrFun (congrFun h2 i0) i0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h3
  simp [Matrix.single_apply, hne.symm] at h3

theorem finrank_le_natDegree_minpoly (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hs : (minpoly K T).Separable)
    (hc : ∀ a b : Module.End K V, Commute a T → Commute b T → Commute a b) :
    Module.finrank K V ≤ (minpoly K T).natDegree := by
  classical
  set f := minpoly K T with hf
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  obtain ⟨hsum, -⟩ := GlobalTheory.EigSum.finrank_eigenspaces_of_separable_minpoly K V T f hmon hs
    (minpoly.aeval K T) (fun g hg => minpoly.dvd K T hg)
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  by_contra hlt
  push_neg at hlt
  obtain ⟨μ, hμ, h2⟩ : ∃ μ ∈ f.roots.toFinset, 2 ≤ Module.finrank K (T.eigenspace μ) := by
    by_contra hno
    push_neg at hno
    have : ∑ z ∈ f.roots.toFinset, Module.finrank K (T.eigenspace z) ≤
        ∑ z ∈ f.roots.toFinset, 1 :=
      Finset.sum_le_sum fun z hz => Nat.lt_succ_iff.mp (hno z hz)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hroot : f.IsRoot μ := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero] at hμ; exact hμ
  set q := f /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfq : (Polynomial.X - Polynomial.C μ) * q = f :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqμ : q.eval μ ≠ 0 := by
    intro h0
    have hq' : (Polynomial.X - Polynomial.C μ) * (q /ₘ (Polynomial.X - Polynomial.C μ)) = q :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h0
    obtain ⟨q2, hq2⟩ : ∃ q2, (Polynomial.X - Polynomial.C μ) * q2 = q := ⟨_, hq'⟩
    have hu : IsUnit (Polynomial.X - Polynomial.C μ) :=
      hs.squarefree _ ⟨q2, by rw [← hfq, ← hq2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C μ hu
  set c := q.eval μ with hc_def
  set Q := Polynomial.aeval T q with hQ
  set E := T.eigenspace μ with hE
  have hTQ : ∀ v, T (Q v) = μ • Q v := by
    intro v
    have h0 : Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) * q) = 0 := by
      rw [hfq]; exact minpoly.aeval K T
    have h1 := congrArg (fun g : Module.End K V => g v) h0
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  have hQT : ∀ v, Q (T v) = T (Q v) := by
    intro v
    have h := congrArg (Polynomial.aeval T) (mul_comm q Polynomial.X)
    simp only [map_mul, Polynomial.aeval_X] at h
    exact congrArg (fun g : Module.End K V => g v) h
  have hQE : ∀ v, Q v ∈ E := by
    intro v
    rw [hE, Module.End.mem_eigenspace_iff]
    exact hTQ v
  have hQid : ∀ u ∈ E, Q u = c • u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hu, hu0⟩
  let π : V →ₗ[K] E := Q.codRestrict E hQE
  let ι : E →ₗ[K] V := E.subtype
  have hπι : ∀ x : E, π (ι x) = c • x := by
    intro x; apply Subtype.ext; simp [π, ι, hQid x.1 x.2]
  have hπT : ∀ v, π (T v) = μ • π v := by
    intro v; apply Subtype.ext; simp [π, hQT v, hTQ v]
  have hcomm : ∀ S : Module.End K E, Commute (ι ∘ₗ S ∘ₗ π) T := by
    intro S
    apply LinearMap.ext
    intro v
    have hm : T (S (π v) : V) = μ • (S (π v) : V) := Module.End.mem_eigenspace_iff.mp (S (π v)).2
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hπT v, map_smul]
    simp [ι, hm]
  obtain ⟨S₁, S₂, hS⟩ := exists_not_commute_of_two_le_finrank h2
  have hab := hc _ _ (hcomm S₁) (hcomm S₂)
  apply hS
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun g : Module.End K V => g (ι (c⁻¹ • c⁻¹ • w))) hab.eq
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_smul, hπι, smul_smul] at h1
  apply Subtype.ext
  simpa [ι, mul_inv_cancel₀ hqμ, inv_mul_cancel₀ hqμ, mul_assoc, mul_left_comm] using h1

theorem natDegree_minpoly_eq_of_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ)
    (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable →
    (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) →
    (minpoly K N).natDegree = k := by
  intro K _ _ k N hs hc
  have hmin : minpoly K (Matrix.toLin' N) = minpoly K N := Matrix.minpoly_toLin' N
  apply le_antisymm
  · calc (minpoly K N).natDegree ≤ N.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N) (Matrix.charpoly_monic N).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · have h := finrank_le_natDegree_minpoly K (Fin k → K) (Matrix.toLin' N) (hmin ▸ hs) ?_
    · simpa [hmin] using h
    · intro a b ha hb
      let e : Matrix (Fin k) (Fin k) K ≃ₐ[K] Module.End K (Fin k → K) := Matrix.toLinAlgEquiv'
      have hN : e.symm (Matrix.toLin' N) = N := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      have hA := ha.map e.symm
      have hB := hb.map e.symm
      rw [hN] at hA hB
      simpa only [AlgEquiv.apply_symm_apply] using (hc _ _ hA hB).map e

end GlobalTheory.RegCommutant
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantCommStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable → (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) → (minpoly K N).natDegree = k := by
  first | (exact @GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (exact GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (intros; apply GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentralise

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegDeg

open Polynomial

theorem natDegree_minpoly_eq : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C]
    [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C,
    (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) →
    (minpoly F c).natDegree = n := by
  intro F C _ _ _ _ _ _ n hC c hsep hcomm
  obtain ⟨k, hk0, hkC, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F C
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkC.symm.trans hC)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] C := (1 : K) ⊗ₜ[F] c with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x
  have hxr : x = Algebra.TensorProduct.includeRight c := rfl
  have hdvd : minpoly K x ∣ (minpoly F c).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K c hxi
  have hmap : (minpoly F c).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr
      (minpoly.ne_zero (IsIntegral.of_finite F c))
  have hle : (minpoly K x).natDegree ≤ (minpoly F c).natDegree := by
    calc (minpoly K x).natDegree ≤ ((minpoly F c).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = (minpoly F c).natDegree := natDegree_map _
  have hxsep : (minpoly K x).Separable := (hsep.map).of_dvd hdvd

  let S := Subalgebra.centralizer F ({c} : Set C)
  letI : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (by
        have ha : Commute (a : C) c := ((Subalgebra.mem_centralizer_iff F).mp a.2 c rfl).symm
        have hb : Commute (b : C) c := ((Subalgebra.mem_centralizer_iff F).mp b.2 c rfl).symm
        exact (hcomm _ _ ha hb).eq) }
  have hcent : ∀ y : C, y * c = c * y ↔ y ∈ Set.range (S.val) := by
    intro y
    constructor
    · intro h
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h.symm
    · rintro ⟨w, rfl⟩
      exact ((Subalgebra.mem_centralizer_iff F).mp w.2 c rfl).symm
  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hNcomm : ∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B := by
    intro A B hA hB
    have hA' : e.symm A * x = x * e.symm A := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hA.eq
    have hB' : e.symm B * x = x * e.symm B := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hB.eq
    have h := GlobalTheory.LKCentAf.commute_of_centralizer F K C S c S.val hcent _ _ hA' hB'
    have h2 := congrArg e h
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  have hdegN := GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm K k N (by rw [hmN]; exact hxsep) hNcomm
  have hxk : (minpoly K x).natDegree = k := by rw [← hmN]; exact hdegN
  rw [← hxk]
  exact le_antisymm hge hle

end GlobalTheory.RegDeg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentraliseStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
end
end

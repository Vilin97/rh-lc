module

public import GroundTheory.ProfiniteCohomology.PoitouTate.Deduction
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsLocalInvRootsOfPlaces
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BasePairing
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseMain

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))


include hℓ hnk hS in
theorem gsBaseBijective_of_fixing (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) :
    GsBaseBijective S ιs n U (gsCompactInv S ιs n hodd h3) := by
  obtain ⟨L, hKL, hL, hUeq⟩ := exists_gsOpenSubgroup_eq K S U
  subst U
  -- Infer the application type before comparing it with the goal.
  have hbase := @gsBaseBijective_of_le K S ‹Fintype S› ιs n ℓ k ‹NeZero n›
    hℓ hnk hS hodd h3 hP hcores W₀ hW₀ L hKL hL hU
  assumption



include hℓ hnk hS in
theorem exists_compactDualityHypotheses_gs_of_pairing (hP : GsPairingInput n ℓ) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have hSn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    mem_of_natCast_pow_mem S n ℓ k hnk hS
  have hD := nonempty_addEquiv_gsRoots_of_places S n hnS
  have hfin : Finite (gsRoots S n) := hD.elim fun e => Finite.of_equiv (ZMod n) e.toEquiv.symm
  have hn : n ≠ 0 := NeZero.ne n
  have hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom := fun U =>
    @surjective_gs_compactCores_three K S ιs n hn hSn hodd U (gsRoots S n)
      (isDiscreteRep_gsRoots S n) hfin (nsmul_gsRoots S n)
  obtain ⟨W₀, hW₀⟩ := exists_openSubgroup_fixing_rootsOfUnity K S n hn
  refine ⟨W₀, { nonempty_addEquiv := hD, subsingleton_four := ?_, bijective_base := ?_ }⟩
  · intro M hdiscrete _ hM
    exact @subsingleton_compactCohomology_four K S n hn hSn hodd ιs M hdiscrete hM
  · intro U hU
    have hbase := @gsBaseBijective_of_fixing K S ‹Fintype S› ιs n ℓ k ‹NeZero n›
      hℓ hnk hS hodd h3 hP hcores W₀ hW₀ U hU
    -- The field uses the same map with a different proof of the torsion condition.
    unfold GsBaseBijective at hbase
    with_reducible assumption


include hℓ hnk in
theorem gsPairingInput : GsPairingInput n ℓ := fun _ S' _ ιs' hS' _ hodd' h3' =>
  ⟨gsCompactInv_ker_left S' ιs' n ℓ k hℓ hnk hS' hodd' h3', gsCompactInv_ker_right S' ιs' n ℓ k hℓ hnk hS' hodd' h3'⟩


include hℓ hnk hS in
theorem exists_compactDualityHypotheses_gs :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ :=
  exists_compactDualityHypotheses_gs_of_pairing S ιs n ℓ k hℓ hnk hS hodd h3 (gsPairingInput n ℓ k hℓ hnk)

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)


omit [NeZero N] in
theorem gsBaseCase : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀ :=
  fun p hp => exists_compactDualityHypotheses_gs S ιs _ p _ (Nat.prime_of_mem_primeFactors hp) rfl
    (mem_of_natCast_dvd_mem S hS (Nat.dvd_of_mem_primeFactors hp)) _ _

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)


include hM in
theorem poitouTate_duality_gs {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap (gsFinFamily S ιs) (gsRoots S N) h (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_compactDualityMap M hM h


include hM in
theorem poitouTate_sha_gs :
    Finite (ptSha (gsFinFamily S ιs) M 1) ∧ Finite (ptSha (gsFinFamily S ιs) (dualRep (gsRoots S N) M) 2) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))) ∧
      Function.Bijective (ptShaPairing (gsFinFamily S ιs) (gsRoots S N) M (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK))).flip :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).sha M hM


include hM in
theorem poitouTate_nineTerm_gs :
    Function.Injective (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 0).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 0 + 2 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 1 + 2 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 1).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl)) ∧
    Function.Exact (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 1 + 1 = 2 from rfl))
      (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) ∧
    Function.Exact (ptDualToGlobal (gsFinFamily S ιs) (gsRoots S N) (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) M (show 2 + 1 = 3 from rfl)
        ((gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).bijective_ptCompactDualMap M hM _)) (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom ∧
    Function.Exact (ptGlobalToLocal (gsFinFamily S ιs) M 2).hom
      (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) ∧
    Function.Surjective (ptLocalDualMap (gsFinFamily S ιs) (gsRoots S N) M (gsLocalInvRootsQZ S ιs N) (show 2 + 0 = 2 from rfl)) :=
  (gsPoitouTateDualityHypotheses S ιs hS hK (gsBaseCase S ιs hS hK)).nineTerm M hM

end GroundTheory.ProfCoh
end
end
end

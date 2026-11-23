module

public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NormalOfGsOpenSubgroupNormal
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FiniteCohomologyTwoInt
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
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
import Mathlib.Tactic.TypeStar
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
public import GroundTheory.ProfiniteCohomology.PoitouTate.Deduction
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
import GroundTheory.ProfiniteCohomology.TorsionDualFinite
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.InvariantsEqOfPointwise

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem invariants_eq_of_pointwise {k V Γ₁ Γ₂ H : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [Group Γ₁] [Group Γ₂] [Group H] (ρ₁ : Representation k Γ₁ V) (ρ₂ : Representation k Γ₂ V)
    (f₁ : H →* Γ₁) (f₂ : H →* Γ₂) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (h : ∀ g, ρ₁ (f₁ g) = ρ₂ (f₂ g)) : ρ₁.invariants = ρ₂.invariants := by
  ext x
  simp only [Representation.mem_invariants]
  constructor
  · intro hx γ
    obtain ⟨g, rfl⟩ := h₂ γ
    rw [← h g]
    exact hx _
  · intro hx γ
    obtain ⟨g, rfl⟩ := h₁ γ
    rw [h g]
    exact hx _

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem modNRep_actA_one_apply (g : galUnramifiedOutside K.1 ℚ̄ S) :
    (letI := actA hL 1; modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ (gsRestrictGal hL g)) =
      gsH1SUnitsModRep ℓ hL (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun y => ?_
  have h1 := conjActionOf_smul (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL) (galSUnitsMax K.1 ℚ̄ S) 1 g y
  have h2 := conjActionOf_smul (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le (galSUnitsMax K.1 ℚ̄ S) 1 g y
  exact congrArg Submodule.Quotient.mk (h1.trans h2.symm)


omit [Module.Finite (ZMod ℓ) M] in
theorem nRep_gsRestrictGal (g : galUnramifiedOutside K.1 ℚ̄ S) :
    nRep hL hζ M hM (gsRestrictGal hL g) =
      quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (homRep (gsRootsZMod S ℓ) M)
        (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)
        (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  have h1 : (gsQuotientGalEquiv hL).symm (gsRestrictGal hL g) =
      (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) g := by
    rw [MulEquiv.symm_apply_eq, QuotientGroup.mk'_apply, gsQuotientGalEquiv_mk]
  exact congrArg (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (homRep (gsRootsZMod S ℓ) M)
    (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)) h1


omit [Module.Finite (ZMod ℓ) M] in
theorem tprod_gsRestrictGal (g : galUnramifiedOutside K.1 ℚ̄ S) :
    (letI := actA hL 1; (modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)) (gsRestrictGal hL g) =
      ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)))
        (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  exact congrArg₂ TensorProduct.map (modNRep_actA_one_apply hL g) (nRep_gsRestrictGal hL hζ M hM g)

theorem dMod_one_eq_pf [Finite (ModN (AA hL 1) ℓ)] :
    dMod hL (dN hL hζ M hM hΓ) 1 =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
  have hinv : (letI := actA hL 1;
      ((modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)).invariants) =
      ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
    exact invariants_eq_of_pointwise _ _ (gsRestrictGal hL)
      (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
      (gsRestrictGal_surjective hL) (QuotientGroup.mk'_surjective _) (tprod_gsRestrictGal hL hζ M hM)
  have e1 : dMod hL (dN hL hζ M hM hΓ) 1 = (Module.finrank (ZMod ℓ) (letI := actA hL 1;
      ((modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)).invariants) : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact e1.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => (Module.finrank (ZMod ℓ) p : ℤ)) hinv)

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.OddOrTcBasePf

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

local instance oddOrTcBaseScalarTower {K L : FiniteSubfield} [Fact (K ≤ L)] :
    IsScalarTower K.1 L.1 ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem odd_or_tc_base_pf
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) : Odd ℓ ∨ IsTotallyComplex K.1 := by
  have hℓ : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  · right
    subst h2
    have hTC : IsTotallyComplex L.1 := hK.resolve_left (by simp)
    have : IsGalois K.1 L.1 := ⟨⟩
    refine ⟨fun v => ?_⟩
    by_contra hv
    rw [InfinitePlace.not_isComplex_iff_isReal] at hv
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := K.1) (K := L.1) v
    have hw : w.IsComplex := hTC.isComplex w
    have hram : ¬ InfinitePlace.IsUnramified K.1 w :=
      InfinitePlace.not_isUnramified_iff.2 ⟨hw, hv⟩
    have hcard := InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hdvd : 2 ∣ Nat.card (L.1 ≃ₐ[K.1] L.1) :=
      hcard ▸ Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) w)
    have hidx : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index =
        Nat.card (L.1 ≃ₐ[K.1] L.1) := by
      rw [Subgroup.index]
      exact Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
    rw [hidx] at hcop
    have := Nat.Coprime.coprime_dvd_left hdvd hcop
    norm_num at this
  · left
    exact hℓ.odd_of_ne_two h2

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaCount

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

universe u

noncomputable section

section PoitouTateCount

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G} [Fintype ι]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n}
  {inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ}

theorem natCard_cohomology_two_mul_of_poitouTate (P : PoitouTateDualityHypotheses φ D t inv)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep D M) 0) =
      Nat.card (ptSha φ M 2) * ∏ v, Nat.card (cohomology (Rep.res (φ v).toMonoidHom M) 2) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hex, hsurj⟩ := P.nineTerm M hM
  set F := (ptGlobalToLocal φ M 2).hom.toAddMonoidHom
  set Gm := ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have hMD : ∀ f : dualRep D M, n • f = 0 :=
    nsmul_dualRep_eq_zero (nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv)
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (cohomology (dualRep D M) 0) := P.finite_cohomology (dualRep D M) hMD 0
  have h1 : Nat.card (cohomology M 2) = Nat.card F.range * Nat.card (ptSha φ M 2) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (ptSha φ M 2)]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange F).toEquiv
  have hker : Gm.ker = F.range := by
    ext y
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact hex y
  have h2 : Nat.card (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) 2) =
      Nat.card (cohomology (dualRep D M) 0 →+ QZ) * Nat.card F.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Gm.ker, ← hker]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Gm hsurj).toEquiv
  rw [Nat.card_pi, QZ.card_hom] at h2
  rw [h1, h2]
  ring

end PoitouTateCount

section GSPoitouTate

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)
  (H : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)


omit [Fintype S] [NeZero N] in
instance isDiscreteRep_res_gsFinFamily_dualRep (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) :=
  isDiscreteRep_res_dualRep_of_finite (gsRoots S N) M (gsFinFamily S ιs v)


omit [Fintype S] in
include hS hM in
theorem natCard_gs_local_cohomology_two (v : S) :
    Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 2) =
      Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have : Finite (gsRoots S N) := Finite.of_equiv _ hD.some.symm.toEquiv
  have : Finite (dualRep (gsRoots S N) M) := finite_dualRep
  have : Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
    have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)).ρ.invariants :=
      Subtype.finite (α := dualRep (gsRoots S N) M)
    exact Finite.of_equiv _ (H0Iso (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (dualRep (gsRoots S N) M))).toLinearEquiv.toEquiv.symm
  rw [Nat.card_congr (Equiv.ofBijective _ (bijective_gsLocalPairing S ιs N hD M hM v (show 2 + 0 = 2 from rfl))),
    QZ.card_hom]


include H hM in
theorem natCard_gs_cohomology_two_mul :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep (gsRoots S N) M) 0) =
      Nat.card (ptSha (gsFinFamily S ιs) M 2) *
        ∏ v : S, Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  rw [natCard_cohomology_two_mul_of_poitouTate (gsPoitouTateDualityHypotheses S ιs hS hK H) M hM]
  congr 1
  exact Finset.prod_congr rfl fun v _ => natCard_gs_local_cohomology_two S ιs hS M hM v

end GSPoitouTate

end

end GroundTheory.ProfCoh
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PoitouTateH2Nat

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem dMod_one_eq [Finite (ModN (AA hL 1) ℓ)] :
    dMod hL (dN hL hζ M hM hΓ) 1 =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
  exact dMod_one_eq_pf hL hζ M hM hΓ



theorem poitou_tate_H2_nat [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hKK : Odd ℓ ∨ IsTotallyComplex K.1)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    Module.finrank (ZMod ℓ) (cohomology M 2) +
        Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) +
        ∑ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hS' : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  haveI : Finite M := finite_of_moduleFinite M
  have hPT := natCard_gs_cohomology_two_mul S ιs hS' hKK (gsBaseCase S ιs hS' hKK) (intRep M) (nsmul_intRep M)
  apply Nat.pow_right_injective hℓ.two_le
  simp only [pow_add]
  calc ℓ ^ Module.finrank (ZMod ℓ) (cohomology M 2) *
        ℓ ^ Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants
      = Nat.card (cohomology (intRep M) 2) * Nat.card (cohomology (dualRep (gsRoots S ℓ) (intRep M)) 0) := by
        rw [card_H2_integral_module M hℓS, card_H0_dual_module M]
    _ = Nat.card (ptSha (gsFinFamily S ιs) (intRep M) 2) *
        ∏ v : S, Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom
          (dualRep (gsRoots S ℓ) (intRep M))) 0) := hPT
    _ = ℓ ^ Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) *
        ∏ v : S, ℓ ^ Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) :=
        congrArg₂ (· * ·) (card_sha_int M hℓS ιs) (Finset.prod_congr rfl fun v _ => card_H0_dual_local M ιs v)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]



theorem poitou_tate_H2_int [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) [Finite (ModN (AA hL 1) ℓ)]
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    (Module.finrank (ZMod ℓ) (cohomology M 2) : ℤ) +
        Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      dMod hL (dN hL hζ M hM hΓ) 1 +
        ∑ v : S, (Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) : ℤ) := by
  have hℓ : ℓ.Prime := Fact.out
  have hKK : Odd ℓ ∨ IsTotallyComplex K.1 := odd_or_tc_base_pf hL hcop hK
  have hKL : Odd ℓ ∨ IsTotallyComplex L.1 := hK.imp_left fun h => hℓ.odd_of_ne_two h
  have hn := poitou_tate_H2_nat M hℓS hKK ιs
  have hsha := finrank_shaSubmodule_two_eq_finrank_invariants ℓ hL ιs hℓS hKL hcop (roots_trivial hL hζ) M hM
  have e1 := dMod_one_eq hL hζ M hM hΓ
  have hz := congrArg (Nat.cast : ℕ → ℤ) hn
  have hz2 := congrArg (Nat.cast : ℕ → ℤ) hsha
  simp only [Nat.cast_add, Nat.cast_sum] at hz
  rw [e1]
  linarith

end PositivityTheory.Lit1.GEN.X
end
end

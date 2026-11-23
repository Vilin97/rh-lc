module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleCodimOneZeroAmpleSectionFibreStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsCutGenericFibreFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithResidueCharFibreStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZeroStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVertical

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.HSAmp.common_zero_of_le_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  intro k _ X _ p D hX P hA ℓ d
  induction d with
  | zero =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨x, hx⟩ := hC.nonempty
    exact ⟨x, hx, by simp⟩
  | succ d ih =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨C', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre k X p D hX P hA ℓ d (e 0) C (g 0) hℓ hC hCc hCf
      (by exact_mod_cast hd) (hg 0).1 (hg 0).2
    obtain ⟨x, hxC', hx⟩ := ih C' (fun j => e j.succ) (fun j => g j.succ) hℓ h1 h2
      (h3.trans (Set.diff_subset.trans hCf)) h4 (fun j => hg j.succ)
    refine ⟨x, (h3 hxC').1, ?_⟩
    simp only [Set.mem_iUnion, not_exists] at hx ⊢
    intro j
    refine Fin.cases ?_ (fun j => hx j) j
    exact (h3 hxC').2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVerticalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_common_zero_ample_sections_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  first | exact @GlobalTheory.HSAmp.common_zero_of_le_dim | exact GlobalTheory.HSAmp.common_zero_of_le_dim | (intros; apply GlobalTheory.HSAmp.common_zero_of_le_dim <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibre

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped TensorProduct

namespace GlobalTheory.GenFibClosure

theorem finite_of_finite_spec (K S : Type) [Field K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
    [Finite (PrimeSpectrum S)] : Module.Finite K S := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := K)
  have : DiscreteTopology (PrimeSpectrum S) := JacobsonSpace.discreteTopology (Set.toFinite _)
  exact (Module.finite_iff_krullDimLE_zero K S).2
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.1 this).2

theorem isAlgebraic_of_injective {B S : Type} [CommRing B] [CommRing S] [Algebra ℚ S] [Module.Finite ℚ S]
    (f : B →+* S) (hf : Function.Injective f) : Algebra.IsAlgebraic ℤ B := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ S := Algebra.IsAlgebraic.trans ℤ ℚ S
  exact Algebra.IsAlgebraic.of_injective f.toIntAlgHom hf

theorem finiteType_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A]
    (f : A →+* B) (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem isAlgebraic_of_finite (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) : Algebra.IsAlgebraic ℤ B := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  let S := ℚ ⊗[ℤ] B
  letI : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization M S := IsLocalization.tensorRight ℚ (nonZeroDivisors ℤ)
  have hinj := PrimeSpectrum.localization_comap_injective S M
  have hfin : Finite (PrimeSpectrum S) := by
    refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (h.subset ?_) hinj.injOn)
    rintro _ ⟨Q, -, rfl⟩ n hn hQ
    have h1 : (n : S) ∈ Q.asIdeal := by
      have := hQ
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at this
      exact this
    have h2 : IsUnit (n : S) := by
      have : IsUnit (n : ℚ) := (Nat.cast_ne_zero.2 hn).isUnit
      simpa using this.map (algebraMap ℚ S)
    exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 h2)
  have hf : Module.Finite ℚ S := finite_of_finite_spec ℚ S
  have hi : Function.Injective (algebraMap B S) := by
    refine IsLocalization.injective S (M := M) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hz)
  exact isAlgebraic_of_injective _ hi

theorem finite_primes_domain (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (h : {Q : PrimeSpectrum B | ∀ n : ℕ, n ≠ 0 → (n : B) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum B | (l : B) ∈ Q.asIdeal}.Finite := by
  have := isAlgebraic_of_finite B h
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  have hd := GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one B (RingHom.injective_int _)
  rw [trdeg_eq_zero] at hd
  have hd1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff, hd]; simp
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B (Ideal.span {(l : B)})
  refine (hfin.preimage (f := PrimeSpectrum.asIdeal) fun _ _ _ _ e => PrimeSpectrum.ext e).subset ?_
  intro P hP
  refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hP⟩, fun Q hQ hQP => ?_⟩
  have hQ0 : Q ≠ ⊥ := fun e => by
    have := (Ideal.span_singleton_le_iff_mem _).1 hQ.2
    rw [e] at this
    exact Nat.cast_ne_zero.2 hl this
  have hm : Q.IsMaximal := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hd1 Q hQ0 hQ.1
  exact (hm.eq_of_le P.isPrime.ne_top hQP).ge

theorem finite_primes (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] (P : PrimeSpectrum A)
    (hP : ∀ n : ℕ, n ≠ 0 → (n : A) ∉ P.asIdeal)
    (h : {Q : PrimeSpectrum A | P ≤ Q ∧ ∀ n : ℕ, n ≠ 0 → (n : A) ∉ Q.asIdeal}.Finite) (l : ℕ) (hl : l ≠ 0) :
    {Q : PrimeSpectrum A | P ≤ Q ∧ (l : A) ∈ Q.asIdeal}.Finite := by
  let π := Ideal.Quotient.mk P.asIdeal
  have hs : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : CharZero (A ⧸ P.asIdeal) := @CharP.charP_to_charZero _ _ (by
    refine ⟨fun n => ⟨fun hn => ?_, fun hn => by rw [zero_dvd_iff.1 hn, Nat.cast_zero]⟩⟩
    by_contra hne
    refine hP n (fun e => hne (e ▸ dvd_rfl)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn)
  have := finiteType_of_surjective π hs
  have hinj := PrimeSpectrum.comap_injective_of_surjective π hs
  have hr : Set.range (PrimeSpectrum.comap π) = PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := by
    rw [range_comap_of_surjective _ π hs, Ideal.mk_ker]
  have hf := finite_primes_domain (A ⧸ P.asIdeal) ((h.preimage hinj.injOn).subset fun Q hQ => ⟨by
    have : PrimeSpectrum.comap π Q ∈ PrimeSpectrum.zeroLocus (P.asIdeal : Set A) := hr ▸ ⟨Q, rfl⟩
    exact this, fun n hn h1 => hQ n hn (by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h1; exact h1)⟩) l hl
  refine (hf.image (PrimeSpectrum.comap π)).subset ?_
  rintro Q ⟨h1, h2⟩
  have : Q ∈ Set.range (PrimeSpectrum.comap π) := hr ▸ h1
  obtain ⟨Q, rfl⟩ := this
  refine ⟨Q, ?_, rfl⟩
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast] at h2
  exact h2

theorem natCast_eq_zero_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (Q : PrimeSpectrum Γ(X, U)) (n : ℕ) :
    (n : X.residueField (hU.fromSpec Q)) = 0 ↔ (n : Γ(X, U)) ∈ Q.asIdeal := by
  have hx : hU.fromSpec Q ∈ U := by
    have : hU.fromSpec Q ∈ Set.range hU.fromSpec := ⟨Q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hb : hU.fromSpec Q ∈ X.basicOpen (n : Γ(X, U)) ↔ (n : Γ(X, U)) ∉ Q.asIdeal :=
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen _) Q
  rw [← map_natCast (X.evaluation U _ hx).hom n]
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen _ hx _).trans (hb.not.trans not_not)

theorem finite_closure_inter_fib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  intro k _ X _ p D hX W hW hfin l
  have hsub : closure (W ∩ fib X 0) ⊆ W := closure_minimal Set.inter_subset_left hW
  rcases eq_or_ne l 0 with rfl | hl
  · exact hfin.subset (Set.inter_subset_inter_left _ hsub)
  have := hX.isNoetherian
  have hft : LocallyOfFiniteType (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hj ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    infer_instance
  have key (U : X.Opens) (hU : IsAffineOpen U) : (closure (W ∩ fib X 0) ∩ fib X l ∩ U).Finite := by
    have : Algebra.FiniteType ℤ Γ(X, U) := by
      set t := p ≫ spMap (Int.castRingHom k)
      have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
        algebraMap ℤ Γ(X, U) := RingHom.ext_int _ _
      rw [← RingHom.finiteType_algebraMap, ← e, RingHom.finiteType_respectsIso.cancel_left_isIso]
      exact HasRingHomProperty.appLE @LocallyOfFiniteType t hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have hemb := hU.fromSpec.isOpenEmbedding
    have h0 (Q : PrimeSpectrum Γ(X, U)) :
        hU.fromSpec Q ∈ fib X 0 ↔ ∀ n : ℕ, n ≠ 0 → (n : Γ(X, U)) ∉ Q.asIdeal := by
      change ringChar _ = 0 ↔ _
      simp only [← natCast_eq_zero_iff hU, ringChar.spec]
      refine ⟨fun h n hn => by rw [h, zero_dvd_iff]; exact hn, fun h => ?_⟩
      by_contra hne
      exact h _ hne dvd_rfl
    have hS : (hU.fromSpec ⁻¹' (W ∩ fib X 0)).Finite := hfin.preimage hemb.injective.injOn
    have hT := hS.biUnion (t := fun P : PrimeSpectrum Γ(X, U) =>
        {Q : PrimeSpectrum Γ(X, U) | P ≤ Q ∧ (l : Γ(X, U)) ∈ Q.asIdeal}) fun P hP =>
      finite_primes _ P ((h0 P).1 hP.2) (hS.subset fun Q hQ => ⟨hW.stableUnderSpecialization
        (((PrimeSpectrum.le_iff_specializes P Q).1 hQ.1).map hemb.continuous) hP.1, (h0 Q).2 hQ.2⟩) l hl
    refine (hT.image hU.fromSpec).subset ?_
    rintro y ⟨⟨hy, hyl⟩, hyU⟩
    have : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hyU
    obtain ⟨Q, rfl⟩ := this
    refine ⟨Q, ?_, rfl⟩
    have h1 : Q ∈ closure (hU.fromSpec ⁻¹' (W ∩ fib X 0)) := by
      rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]; exact hy
    rw [← Set.biUnion_of_singleton (hU.fromSpec ⁻¹' (W ∩ fib X 0)), hS.closure_biUnion] at h1
    obtain ⟨P, hP, h1⟩ := Set.mem_iUnion₂.1 h1
    refine Set.mem_iUnion₂.2 ⟨P, hP, (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 h1), ?_⟩
    exact (natCast_eq_zero_iff hU Q l).1 ((ringChar.spec _ _).2 (dvd_of_eq hyl))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2)
    fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  refine (s.finite_toSet.biUnion fun U _ => key U.1 U.2).subset fun y hy => ?_
  obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  exact Set.mem_iUnion₂.2 ⟨U, hU, hy, hyU⟩

end GlobalTheory.GenFibClosure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGenericFibreClosureInterResidueCharFibreStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ W : Set X, IsClosed W → (W ∩ fib X 0).Finite → ∀ ℓ : ℕ, (closure (W ∩ fib X 0) ∩ fib X ℓ).Finite := by
  first | exact @GlobalTheory.GenFibClosure.finite_closure_inter_fib | exact GlobalTheory.GenFibClosure.finite_closure_inter_fib | (intros; apply GlobalTheory.GenFibClosure.finite_closure_inter_fib <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLoweringFibreDimension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem noetherianSpace_of_isArithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : NoetherianSpace X := by
  obtain ⟨N, j, hj, hjp⟩ := h.isProjOver
  haveI := h.isDomain
  haveI := h.finite
  haveI : IsNoetherian ℤ k := isNoetherian_of_isNoetherianRing_of_finite ℤ k
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  haveI : IsProper p := hjp ▸ inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  infer_instance

theorem exists_sec_fibre_dim_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z →
    (∀ ℓ : ℕ, topologicalKrullDim ↥(Z ∩ fib X ℓ) ≤ d) →
    ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, ∀ ℓ : ℕ, topologicalKrullDim ↥((Z \ NV P e 0 f) ∩ fib X ℓ) < d := by
  intro k _ X _ p D hX P hA d Z hZ hdim
  haveI : NoetherianSpace X := noetherianSpace_of_isArithVar hX
  have memfib : ∀ {x : X} {ℓ : ℕ}, x ∈ fib X ℓ ↔ ringChar (X.residueField x) = ℓ := Iff.rfl
  obtain ⟨hcov, hfibc, -, -, hWfib⟩ := GlobalTheory.T.projArith_residueCharFibre_structure k X p D hX
  have hNV : ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) :=
    fun a b g hg => (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P a b g hg).1

  obtain ⟨e₀, g, hg, hfin0⟩ := GlobalTheory.T.exists_sections_cut_genericFibre_finite k X p D hX P hA d Z hZ (hdim 0)
  have hW₀c : IsClosed (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) :=
    hZ.sdiff (isOpen_iUnion fun j => hNV _ _ _ (hg j).2)

  have hpick0 : ∀ Y : irreducibleComponents ↥(Z ∩ fib X 0), ∃ y : ↥(Z ∩ fib X 0), y ∈ Y.1 ∧
      IsClosed ({y} : Set ↥(Z ∩ fib X 0)) := fun Y =>
    (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
  choose q₀ hq₀ hq₀c using hpick0
  haveI : Finite (irreducibleComponents ↥(Z ∩ fib X 0)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set W : Set X := (Z \ ⋃ j, NV P (e₀ j) 0 (g j)) ∪ ⋃ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} with hWdef
  have hWc : IsClosed W := hW₀c.union (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hcl0 : ∀ Y, closure {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} ∩ fib X 0 ⊆ {((q₀ Y : ↥(Z ∩ fib X 0)) : X)} := by
    rintro Y x ⟨hx, hx0⟩
    obtain ⟨K, hK, hKe⟩ := isClosed_induced_iff.1 (hq₀c Y)
    have hqK : ((q₀ Y : ↥(Z ∩ fib X 0)) : X) ∈ K := by
      have : q₀ Y ∈ Subtype.val ⁻¹' K := by rw [hKe]; rfl
      exact this
    have hxK : x ∈ K := closure_minimal (Set.singleton_subset_iff.2 hqK) hK hx
    have hxZ : x ∈ Z := closure_minimal (Set.singleton_subset_iff.2 (q₀ Y).2.1) hZ hx
    have : (⟨x, hxZ, hx0⟩ : ↥(Z ∩ fib X 0)) ∈ Subtype.val ⁻¹' K := hxK
    rw [hKe] at this
    exact congrArg Subtype.val this
  have hWfin : (W ∩ fib X 0).Finite := by
    refine (hfin0.union (Set.finite_range fun Y => ((q₀ Y : ↥(Z ∩ fib X 0)) : X))).subset ?_
    rintro x ⟨hx | hx, hx0⟩
    · exact Or.inl ⟨hx, hx0⟩
    · obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hx
      exact Or.inr ⟨Y, (hcl0 Y ⟨hY, hx0⟩).symm⟩

  obtain ⟨S, hSp, hWS⟩ := hWfib W hWc

  have hpick : ∀ i : (Σ ℓ : S, irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))), ∃ y : ↥(Z ∩ fib X (i.1 : ℕ)),
      y ∈ i.2.1 ∧ IsClosed ({(y : X)} : Set X) := by
    rintro ⟨ℓ, Y⟩
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ (hSp ℓ ℓ.2).ne_zero)
    obtain ⟨y, hy, hyc⟩ :=
      (isClosed_of_mem_irreducibleComponents Y.1 Y.2).exists_closed_singleton Y.2.1.nonempty
    refine ⟨y, hy, ?_⟩
    have := hc.isClosedEmbedding_subtypeVal.isClosedMap _ hyc
    rwa [Set.image_singleton] at this
  choose q hq hqc using hpick
  haveI : ∀ ℓ : S, Finite (irreducibleComponents ↥(Z ∩ fib X (ℓ : ℕ))) := fun _ =>
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hFc : IsClosed (Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X)) := by
    rw [← Set.iUnion_singleton_eq_range]
    exact isClosed_iUnion_of_finite hqc
  set T : Set X := closure (W ∩ fib X 0) ∪ Set.range fun i => ((q i : ↥(Z ∩ fib X (i.1 : ℕ))) : X) with hTdef
  have hTc : IsClosed T := isClosed_closure.union hFc
  have hTfin : ∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite := fun ℓ =>
    ((GlobalTheory.T.finite_genericFibreClosure_inter_residueCharFibre k X p D hX W hWc hWfin ℓ).union (Set.finite_range _)).subset fun x ⟨hx, hxl⟩ =>
      hx.elim (fun h => Or.inl ⟨h, hxl⟩) Or.inr

  obtain ⟨e, he, f, hf, hTNV⟩ := GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed k X p D hX P hA T hTc hTfin
  refine ⟨e, he, f, hf, fun ℓ => ?_⟩
  have hfo : IsOpen (NV P e 0 f) := hNV _ _ _ hf

  have key : ∀ Y ∈ irreducibleComponents ↥(Z ∩ fib X ℓ), (d : WithBot ℕ∞) ≤ topologicalKrullDim Y →
      ∃ s ∈ Y, (s : X) ∈ T := by
    intro Y hY hYd
    rcases eq_or_ne ℓ 0 with rfl | hℓ0
    · refine ⟨q₀ ⟨Y, hY⟩, hq₀ ⟨Y, hY⟩, Or.inl (subset_closure ⟨?_, (q₀ ⟨Y, hY⟩).2.2⟩)⟩
      exact Or.inr (Set.mem_iUnion.2 ⟨⟨Y, hY⟩, subset_closure rfl⟩)
    by_cases hℓS : ℓ ∈ S
    · exact ⟨q ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, hq ⟨⟨ℓ, hℓS⟩, ⟨Y, hY⟩⟩, Or.inr ⟨_, rfl⟩⟩
    obtain ⟨s₀, -⟩ := hY.1.nonempty
    have hℓp : ℓ.Prime := by
      rcases hcov (s₀ : X) with h | ⟨ℓ', hℓ', h⟩
      · exact absurd ((memfib.1 s₀.2.2).symm.trans (memfib.1 h)) hℓ0
      · rwa [(memfib.1 s₀.2.2).symm.trans (memfib.1 h)]
    have hc : IsClosed (Z ∩ fib X ℓ) := hZ.inter (hfibc ℓ hℓ0)
    have hCi : IsIrreducible (Subtype.val '' Y) := hY.1.image _ continuous_subtype_val.continuousOn
    have hCc : IsClosed (Subtype.val '' Y) :=
      hc.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents Y hY)
    have hCf : Subtype.val '' Y ⊆ fib X ℓ := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2.2
    have hCd : (d : WithBot ℕ∞) ≤ topologicalKrullDim ↥(Subtype.val '' Y) := by
      rwa [← (Topology.IsEmbedding.subtypeVal.homeomorphImage Y).isHomeomorph.topologicalKrullDim_eq]
    obtain ⟨x, ⟨s, hsY, rfl⟩, hxg⟩ :=
      GlobalTheory.T.exists_common_zero_ample_sections_vertical k X p D hX P hA ℓ d (Subtype.val '' Y) e₀ g hℓp hCi hCc hCf hCd hg
    refine ⟨s, hsY, ?_⟩
    have hxW : (s : X) ∈ W := Or.inl ⟨s.2.1, hxg⟩
    rcases hWS hxW with h | h
    · exact Or.inl h
    · obtain ⟨ℓ', hℓ'S, h'⟩ := Set.mem_iUnion₂.1 h
      have : ℓ' = ℓ := (memfib.1 h').symm.trans (memfib.1 s.2.2)
      exact absurd (this ▸ hℓ'S) hℓS
  have hCsc : IsClosed {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} :=
    (hfo.preimage continuous_subtype_val).isClosed_compl
  have hdrop := (GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero ↥(Z ∩ fib X ℓ)).1 _ d hCsc (hdim ℓ) fun Y hY hYd hsub => by
    obtain ⟨s, hsY, hsT⟩ := key Y hY hYd
    exact hsub hsY (hTNV hsT)
  have hset : Subtype.val '' {s : ↥(Z ∩ fib X ℓ) | (s : X) ∉ NV P e 0 f} = (Z \ NV P e 0 f) ∩ fib X ℓ := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s.2.1, hs⟩, s.2.2⟩
    · rintro ⟨⟨hxZ, hxN⟩, hxl⟩
      exact ⟨⟨x, hxZ, hxl⟩, hxN, rfl⟩
  rw [← hset, ← (Topology.IsEmbedding.subtypeVal.homeomorphImage _).isHomeomorph.topologicalKrullDim_eq]
  exact hdrop

end GlobalTheory.HSAmp
end
end

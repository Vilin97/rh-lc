module

public import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.CastSumAddMul
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NormalOfGsOpenSubgroupNormal
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeRegular
import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
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
import Mathlib.Tactic.TypeStar
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FinrankH2EulerFormula
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FinrankKerSubOneAddFinrankKerAddOne
import GroundTheory.GlobalFields.SUnits
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GEqAddOfExactOfFiniteCokernel
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FiniteCohomologyRootsZMod

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

noncomputable abbrev rootsRepGal (i : ℕ) :
    Representation (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
      (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) :=
  (cohomologyConjRep (gsRootsZMod S ℓ) (PP hL) i).comp (gsQuotientGalEquiv hL).symm.toMonoidHom

theorem compactSpace_PP : CompactSpace (PP hL) :=
  compactSpace_openSubgroup (gsOpenSubgroup S hL)

noncomputable abbrev rootsZModEquiv (i : ℕ) :
    cohomology (Rep.res (PP hL).subtype (gsRoots S ℓ)) i ≃+
      cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i :=
  cohomologyAddEquivOfEquiv (A := Rep.res (PP hL).subtype (gsRoots S ℓ))
    (A' := Rep.res (PP hL).subtype (gsRootsZMod S ℓ))
    (zmodRepOfTorsionEquiv ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) i

theorem rootsRepGal_rootsZModEquiv (i : ℕ) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (y : cohomology (Rep.res (PP hL).subtype (gsRoots S ℓ)) i) :
    rootsRepGal hL i (gsRestrictGal hL g) (rootsZModEquiv hL i y) =
      rootsZModEquiv hL i ((cohomologyConj (gsRoots S ℓ) (PP hL) i g).hom y) := by
  have hq : (gsQuotientGalEquiv hL).symm (gsRestrictGal hL g) =
      (QuotientGroup.mk g : galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) := by
    rw [MulEquiv.symm_apply_eq, gsQuotientGalEquiv_mk]
  simp only [rootsRepGal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hq, cohomologyConjRep_mk]
  exact (cohomologyAddEquivOfEquiv_cohomologyConj (A := gsRoots S ℓ) (A' := gsRootsZMod S ℓ)
    (zmodRepOfTorsionEquiv ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl)
    (PP hL) i g y).symm

theorem rootsZModEquiv_symm_conj (i : ℕ) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (x : cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) :
    (rootsZModEquiv hL i).symm (rootsRepGal hL i (gsRestrictGal hL g) x) =
      (cohomologyConj (gsRoots S ℓ) (PP hL) i g).hom ((rootsZModEquiv hL i).symm x) := by
  have h1 := rootsRepGal_rootsZModEquiv hL i g ((rootsZModEquiv hL i).symm x)
  exact (AddEquiv.symm_apply_eq _).2
    ((congrArg (fun z => rootsRepGal hL i (gsRestrictGal hL g) z)
      ((rootsZModEquiv hL i).apply_symm_apply x)).symm.trans h1)

theorem finite_cohomology_rootsZMod [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨f⟩ := nonempty_addEquiv_gsRoots_of_mem S (n := ℓ) fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hcard : Nat.card (Rep.res (PP hL).subtype (gsRoots S ℓ)) = ℓ :=
    (Nat.card_congr f.toEquiv).trans (Nat.card_zmod ℓ)
  have : Finite (Rep.res (PP hL).subtype (gsRoots S ℓ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have h := finite_cohomology_openSubgroup K S (gsOpenSubgroup S hL)
    (Rep.res (PP hL).subtype (gsRoots S ℓ)) (fun v hv => by
      rw [hcard] at hv
      by_contra h
      exact hℓS v h hv) i hi
  exact Finite.of_equiv _ (rootsZModEquiv hL i).toEquiv

theorem toFun_rootsRepGal_zero (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (TorsN (AA hL 0) ℓ)]
    [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) 0)] :
    d.toFun _ (rootsRepGal hL 0) = dTors hL d 0 := by
  haveI := compactSpace_PP hL
  exact toFun_eq_torsN_zero (PP hL) (gsRestrictGal hL) (gsRestrictGal_surjective hL)
    (ker_gsRestrictGal_le hL) (gsKummer_shortExact S ℓ hℓS) d (rootsRepGal hL 0)
    (rootsZModEquiv hL 0).symm (rootsZModEquiv_symm_conj hL 0)

theorem finrank_tprod_comp_eq {Γ₁ Γ₂ V W : Type*} [Group Γ₁] [Group Γ₂] [AddCommGroup V]
    [Module (ZMod ℓ) V] [AddCommGroup W] [Module (ZMod ℓ) W] (ρ : Representation (ZMod ℓ) Γ₁ V)
    (σ : Representation (ZMod ℓ) Γ₁ W) (e : Γ₂ →* Γ₁) (he : Function.Surjective e) :
    Module.finrank (ZMod ℓ) (Representation.tprod (ρ.comp e) (σ.comp e)).invariants =
      Module.finrank (ZMod ℓ) (Representation.tprod ρ σ).invariants := by
  have h : Representation.tprod (ρ.comp e) (σ.comp e) = (Representation.tprod ρ σ).comp e := rfl
  rw [h, invariants_comp_of_surjective _ _ he]

theorem dN_toFun' {X : Type} [AddCommGroup X] [Module (ZMod ℓ) X] [Finite X]
    (ρX : Representation (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) X) :
    (dN hL hζ M hM hΓ).toFun X ρX = Module.finrank (ZMod ℓ) (ρX.tprod (nRep hL hζ M hM)).invariants :=
  AdditiveFunction.invariantsTensor_apply _ _ _ _ X ρX

theorem finrank_eq_toFun' (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (i : ℕ) [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i)] :
    (Module.finrank (ZMod ℓ) (cohomology M i) : ℤ) =
      (dN hL hζ M hM hΓ).toFun _ (rootsRepGal hL i) := by
  have hlp : ℓ.Prime := Fact.out
  have hTr : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hP : (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm
  have hkey := finrank_cohomology_eq_finrank_invariants (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M
    (roots_trivial hL hζ) hM hTr hP i
  have h3 := finrank_tprod_comp_eq (cohomologyConjRep (gsRootsZMod S ℓ) (PP hL) i)
    (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M)
      (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))
    (gsQuotientGalEquiv hL).symm.toMonoidHom (gsQuotientGalEquiv hL).symm.surjective
  exact (congrArg (fun n : ℕ => (n : ℤ)) (hkey.trans h3.symm)).trans
    (dN_toFun' hL hζ M hM hΓ (rootsRepGal hL i)).symm

theorem toFun_rootsRepGal_one (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 1) ℓ)]
    [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) 1)] :
    d.toFun _ (rootsRepGal hL 1) = dMod hL d 0 + dTors hL d 1 := by
  haveI := compactSpace_PP hL
  have h := toFun_eq_modN_add_torsN (PP hL) (gsRestrictGal hL) (gsRestrictGal_surjective hL)
    (ker_gsRestrictGal_le hL) (gsKummer_shortExact S ℓ hℓS) d 0 (rootsRepGal hL 1)
    (rootsZModEquiv hL 1).symm (rootsZModEquiv_symm_conj hL 1)
  exact h

theorem h0_eq [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    [Finite (TorsN (AA hL 0) ℓ)] :
    (Module.finrank (ZMod ℓ) (cohomology M 0) : ℤ) = dTors hL (dN hL hζ M hM hΓ) 0 := by
  have := finite_cohomology_rootsZMod hL hℓS 0 (by norm_num)
  exact (finrank_eq_toFun' hL hζ M hM hΓ hℓS hcop 0).trans (toFun_rootsRepGal_zero hL hℓS _)

theorem finrank_H1_euler_formula [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 1) ℓ)] :
    (Module.finrank (ZMod ℓ) (cohomology M 1) : ℤ) =
      dMod hL (dN hL hζ M hM hΓ) 0 + dTors hL (dN hL hζ M hM hΓ) 1 := by
  have := finite_cohomology_rootsZMod hL hℓS 1 (by norm_num)
  exact (finrank_eq_toFun' hL hζ M hM hΓ hℓS hcop 1).trans (toFun_rootsRepGal_one hL hℓS _)

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PFinite

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

omit [Normal K.1 L.1] in
theorem module_finite_S_units [Finite S] : Module.Finite ℤ (AA hL 0) := by
  have : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  exact Module.Finite.equiv (gsH0SUnitsEquiv hL).symm.toIntLinearEquiv

omit [Normal K.1 L.1] in
theorem finite_H1_S_units : Finite (AA hL 1) := finite_gsH1SUnits hL

theorem finite_modN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (ModN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_modN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)

theorem finite_torsN_AA [Finite S] (i : ℕ) (hi : i ≤ 1) : Finite (TorsN (AA hL i) ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  interval_cases i
  · have := module_finite_S_units hL
    exact finite_torsN_of_moduleFinite ℓ
  · have := finite_H1_S_units hL
    exact Subtype.finite

theorem card_gal_eq_index : Nat.card (L.1 ≃ₐ[K.1] L.1) =
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index := by
  rw [Subgroup.index]
  exact (Nat.card_congr (gsQuotientGalEquiv hL).toEquiv).symm

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PUnits

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

theorem units_finite_modN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (ModN A n)] : Finite (ModN B n) := by
  have h : LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ B (n : ℤ))).comap e.toIntLinearEquiv.toLinearMap := by
    rintro _ ⟨y, rfl⟩
    exact ⟨e y, by simp⟩
  refine Finite.of_surjective (Submodule.mapQ _ _ e.toIntLinearEquiv.toLinearMap h) fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H b => exact ⟨Submodule.Quotient.mk (e.symm b), by simp⟩

theorem units_finite_torsN_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (n : ℕ)
    [Finite (TorsN A n)] : Finite (TorsN B n) := by
  refine Finite.of_surjective (fun x : TorsN A n => (⟨e x.1, by
    have hx := (mem_ker_lsmul_iff n (x : A)).1 x.2
    exact (mem_ker_lsmul_iff n (e x.1)).2 (by rw [← map_nsmul, hx, map_zero])⟩ : TorsN B n)) fun y => ?_
  refine ⟨⟨e.symm y.1, (mem_ker_lsmul_iff n _).2 ?_⟩, ?_⟩
  · rw [← map_nsmul, (mem_ker_lsmul_iff n (y : B)).1 y.2, map_zero]
  · ext; simp

theorem S_units_euler_difference [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 0) ℓ)] :
    dMod hL d 0 - dTors hL d 0 = dPlaces (S := S) d + dInf d - d.one := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) := finite_placesOver (L := L.1) (S := S)
  haveI : Finite (ModN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_modN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  haveI : Finite (TorsN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L.1))).unit L.1)) ℓ) :=
    units_finite_torsN_of_addEquiv (gsH0SUnitsEquiv hL) ℓ
  have hU := conj_gsH0SUnits_eq hL d
  have hg : (letI := actA hL 0; d.g (AA hL 0)) = dMod hL d 0 - dTors hL d 0 := by
    letI := actA hL 0
    exact d.g_eq _
  have hS := d.g_sUnits (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
    (placesOver_stable (S := S) (K := K) (L := L))
  rw [← hg]
  exact hU.trans hS

theorem class_group_mod_eq_torsion [Finite S] (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 1) ℓ)] [Finite (TorsN (AA hL 1) ℓ)] :
    dMod hL d 1 = dTors hL d 1 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  letI := actA hL 1
  haveI : Finite (AA hL 1) := finite_gsH1SUnits hL
  have h1 := d.g_eq_zero_of_finite (AA hL 1)
  rw [d.g_eq (AA hL 1)] at h1
  unfold dMod dTors
  exact sub_eq_zero.1 h1

end PositivityTheory.Lit1.GEN.X
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.SumEqCardMulSub

section

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem sum_eq_card_mul_sub {ι : Type*} [Fintype ι] (a b : ι → ℤ) (m : ℤ) (h : ∀ i, a i = m - b i) :
    ∑ i, a i = Fintype.card ι * m - ∑ i, b i := by
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


open scoped Classical in
theorem altSum [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hPn : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    (Module.finrank (ZMod ℓ) (cohomology M 0) : ℤ) - Module.finrank (ZMod ℓ) (cohomology M 1) +
        Module.finrank (ZMod ℓ) (cohomology M 2) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ) -
        Fintype.card (InfinitePlace K.1) * Module.finrank (ZMod ℓ) M := by
  have : Normal K.1 L.1 := normal_of_gsOpenSubgroup_normal hL hPn
  have hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ := by rw [card_gal_eq_index hL]; exact hcop
  have := finite_modN_AA (ℓ := ℓ) hL 0 (by norm_num)
  have := finite_torsN_AA (ℓ := ℓ) hL 0 (by norm_num)
  have := finite_modN_AA (ℓ := ℓ) hL 1 le_rfl
  have := finite_torsN_AA (ℓ := ℓ) hL 1 le_rfl
  have e0 := h0_eq hL hζ M hM hΓ hℓS hcop
  have e1 := finrank_H1_euler_formula hL hζ M hM hΓ hℓS hcop
  have e2 := finrank_H2_euler_formula hL hζ M hM hΓ hℓS hcop hK
  have u0 := S_units_euler_difference hL (dN hL hζ M hM hΓ)
  have u1 := class_group_mod_eq_torsion hL (dN hL hζ M hM hΓ)
  have ei := dInf_eq hL hζ M hM hΓ ιr hℓS
  have hsr := sum_eq_card_mul_sub
    (fun v : {v : InfinitePlace K.1 // v.IsReal} =>
      (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ))
    (fun v : {v : InfinitePlace K.1 // v.IsReal} => (Module.finrank (ZMod ℓ) (Representation.invariants
          ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) : ℤ))
    (Module.finrank (ZMod ℓ) M : ℤ) fun v => by linarith [real_place_H0_finrank hL hζ M hM ιr hℓS hcop hK v]
  have hc : (Fintype.card (InfinitePlace K.1) : ℤ) = Fintype.card {v : InfinitePlace K.1 // v.IsReal} +
      Fintype.card {v : InfinitePlace K.1 // v.IsComplex} := by exact_mod_cast card_infinitePlace_eq K
  linear_combination e0 - e1 + e2 - hsr + (Module.finrank (ZMod ℓ) M : ℤ) * hc - u0 + u1 - ei

end PositivityTheory.Lit1.GEN.X
end
end

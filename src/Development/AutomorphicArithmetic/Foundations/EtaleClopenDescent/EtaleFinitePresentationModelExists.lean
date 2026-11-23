module

public import Development.EtaleCohomology.EtaleSheaves.SysFMPf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.BuildCut
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
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureRangeIsLocalizationIdempotent
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoFlatOfAffineAppLEFlatEpi
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAtPrime

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (q : PrimeSpectrum W),
        ∃ T : Submonoid W, (∀ s ∈ T, IsIdempotentElem s ∧ s ∉ q.asIdeal) ∧ IsLocalization T (Localization.AtPrime q.asIdeal) := by
  intro W _ hW q
  let T : Submonoid W :=
    { carrier := {s | IsIdempotentElem s ∧ s ∉ q.asIdeal}
      one_mem' := ⟨IsIdempotentElem.one, (Ideal.ne_top_iff_one _).mp q.isPrime.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨ha.1.mul hb.1, fun h => (q.isPrime.mem_or_mem h).elim ha.2 hb.2⟩ }
  refine ⟨T, fun s hs => hs, ?_⟩
  have hT : ∀ s ∈ T, s ∈ q.asIdeal.primeCompl := fun s hs => hs.2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨s, hT s hs⟩ : q.asIdeal.primeCompl)
  · intro z
    obtain ⟨⟨x, ⟨s, hs⟩⟩, hz⟩ := IsLocalization.surj q.asIdeal.primeCompl z
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 s
    have he_q : e ∉ q.asIdeal := fun h => hs (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨x * ↑hu.unit⁻¹, ⟨e, he, he_q⟩⟩, ?_⟩
    simp only at hz ⊢
    calc z * algebraMap W _ e = z * algebraMap W _ (e * u * ↑hu.unit⁻¹) := by
          rw [mul_assoc e, IsUnit.mul_val_inv, mul_one]
      _ = (z * algebraMap W _ (e * u)) * algebraMap W _ ↑hu.unit⁻¹ := by
          rw [map_mul (algebraMap W _) (e * u), mul_assoc]
      _ = algebraMap W _ x * algebraMap W _ ↑hu.unit⁻¹ := by rw [hz]
      _ = algebraMap W _ (x * ↑hu.unit⁻¹) := (map_mul _ _ _).symm
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := (IsLocalization.eq_iff_exists q.asIdeal.primeCompl _).mp hxy
    obtain ⟨e, u, he, hu, rfl⟩ := hW.2 c
    have he_q : e ∉ q.asIdeal := fun h => hc (q.asIdeal.mul_mem_right u h)
    refine ⟨⟨e, he, he_q⟩, ?_⟩
    simp only at hcxy ⊢
    have huv : u * ↑hu.unit⁻¹ = 1 := IsUnit.mul_val_inv hu
    calc e * x = e * u * x * ↑hu.unit⁻¹ := by linear_combination (-(e * x)) * huv
      _ = e * u * y * ↑hu.unit⁻¹ := by rw [hcxy]
      _ = e * y := by linear_combination (e * y) * huv
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIdempotentSubmonoidIsLocalizationAway

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

theorem UpperTheory.exists_idempotent_submonoid_isLocalization_away :
    ∀ {R B L B' : Type} [CommRing R] [CommRing B] [CommRing L] [CommRing B'] (e : R), IsIdempotentElem e →
        ∀ (T : Submonoid R), (∀ s ∈ T, IsIdempotentElem s) →
        ∀ [Algebra R B] [IsLocalization.Away e B] [Algebra R L] [IsLocalization T L] [Algebra L B']
          [IsLocalization.Away (algebraMap R L e) B'] (jB : B →+* B'),
        (∀ r, jB (algebraMap R B r) = algebraMap L B' (algebraMap R L r)) →
        ∃ S : Submonoid B, (∀ s ∈ S, IsIdempotentElem s) ∧ @IsLocalization B _ S B' _ jB.toAlgebra := by
  intro R B L B' _ _ _ _ e he T hT _ _ _ _ _ _ jB hj
  letI : Algebra R B' := ((algebraMap L B').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B B' := jB.toAlgebra
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq (fun r => (hj r).symm)
  have hloc : IsLocalization (T ⊔ Submonoid.powers e) B' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
      have h1 := (IsLocalization.map_units L ⟨y, hy⟩).map (algebraMap L B')
      have h2 := IsLocalization.map_units B'
        (⟨algebraMap R L e ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R L e))
      simp only [IsScalarTower.algebraMap_apply R L B', map_mul, map_pow] at h1 h2 ⊢
      exact h1.mul h2
    · intro z
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h1⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R L e)) z
      obtain ⟨⟨r, t⟩, h2⟩ := IsLocalization.surj T a
      refine ⟨⟨r, ⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩⟩, ?_⟩
      simp only at h1 h2 ⊢
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' r, ← h2]
      simp only [map_mul, map_pow] at h1 ⊢
      linear_combination (algebraMap L B' (algebraMap R L t)) * h1
    · intro x y hxy
      rw [IsScalarTower.algebraMap_apply R L B', IsScalarTower.algebraMap_apply R L B' y] at hxy
      obtain ⟨⟨_, n, rfl⟩, hc⟩ :=
        (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R L e)) B').mp hxy
      simp only at hc
      rw [← map_pow, ← map_mul, ← map_mul, IsLocalization.eq_iff_exists T L] at hc
      obtain ⟨t, ht⟩ := hc
      refine ⟨⟨t * e ^ n, Submonoid.mul_mem_sup t.2 ⟨n, rfl⟩⟩, ?_⟩
      simp only
      linear_combination ht
  have key := IsLocalization.isLocalization_of_submonoid_le B B' (Submonoid.powers e)
    (T ⊔ Submonoid.powers e) le_sup_right
  refine ⟨(T ⊔ Submonoid.powers e).map (algebraMap R B), ?_, key⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, z, ⟨n, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hx
  exact ((hT y hy).mul (he.pow n)).map (algebraMap R B)
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsCompactOpenEqBasicOpenIdempotentOfProdACF

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace LateralTheory.E.BuildCut

theorem UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF :
    ∀ {W : Type} [CommRing W], ProdACF W → ∀ (V : Opens (PrimeSpectrum W)), IsCompact (V : Set (PrimeSpectrum W)) →
        ∃ e : W, IsIdempotentElem e ∧ (V : Set (PrimeSpectrum W)) = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum W)) := by
  classical
  intro W _ hW V hV
  have key : ∀ s : Finset W, ∃ e : W, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum W, ((s : Set W) ⊆ (p.asIdeal : Set W) ↔ e ∈ p.asIdeal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp [p.asIdeal.zero_mem]⟩
    | insert a s ha ih =>
      obtain ⟨f, hf, hfs⟩ := ih
      obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
      have he' : e * e = e := he
      have hf' : f * f = f := hf
      refine ⟨e + f - e * f, ?_, fun p => ?_⟩
      · show (e + f - e * f) * (e + f - e * f) = e + f - e * f
        linear_combination (1 - f + f * f - f) * he' + (1 - e) * hf'
      · rw [Finset.coe_insert, Set.insert_subset_iff, hfs p, SetLike.mem_coe,
          Ideal.mul_unit_mem_iff_mem _ hu]
        constructor
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right _ h1)
        · intro h
          have h1 : e * (e + f - e * f) = e := by linear_combination (1 - f) * he'
          have h2 : f * (e + f - e * f) = f := by linear_combination (1 - e) * hf'
          exact ⟨h1 ▸ p.asIdeal.mul_mem_left _ h, h2 ▸ p.asIdeal.mul_mem_left _ h⟩
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hV, V.isOpen⟩
  obtain ⟨e, he, hte⟩ := key t
  refine ⟨e, he, ?_⟩
  rw [← ht]
  ext p
  simp [PrimeSpectrum.mem_zeroLocus, hte p]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleFinitePresentationModelExists

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut TopologicalSpace

namespace UpperTheory.Cb

private def rho (R : Type) [CommRing R] (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom

private theorem away_rho (R : Type) [CommRing R] (f : R) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : ((show Opens (PrimeSpectrum R) from V) : Set (PrimeSpectrum R)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) :
    @IsLocalization.Away R _ f Γ(Spec (CommRingCat.of R), V) _ (rho R V).toAlgebra := by
  have hb : V = (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact Opens.ext hV
  have h := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_of_eq_basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f) (homOfLE le_top : V ⟶ ⊤) hb
  let φ : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.toAlgebra
  have h2 := (IsLocalization.isLocalization_iff_of_base_ringEquiv (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) Γ(Spec (CommRingCat.of R), V) φ.symm).1 h
  have hp : Submonoid.map φ.symm (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)) = Submonoid.powers f := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (φ.symm_apply_apply f)
  rw [hp] at h2
  exact h2

private theorem loc_part {W : Type} [CommRing W] (hW : ProdACF W) (q : PrimeSpectrum W)
    (V : (Spec (CommRingCat.of W)).Opens) (hV : IsCompact (V : Set (Spec (CommRingCat.of W)))) :
    ∃ S : Submonoid Γ(Spec (CommRingCat.of W), V), (∀ s ∈ S, IsIdempotentElem s) ∧
      @IsLocalization _ _ S
        Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)),
          Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ⁻¹ᵁ V) _
        (Scheme.Hom.app (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))) V).hom.toAlgebra := by
  obtain ⟨e, he, hVe⟩ := UpperTheory.isCompact_open_eq_basicOpen_idempotent_of_prodACF hW V hV
  obtain ⟨T, hT, hTL⟩ := UpperTheory.exists_idempotent_submonoid_isLocalization_atPrime hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  letI : Algebra W Γ(Spec (CommRingCat.of W), V) := (rho W V).toAlgebra
  letI : Algebra (Localization.AtPrime q.asIdeal) Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) :=
    (rho _ (j ⁻¹ᵁ V)).toAlgebra
  haveI : IsLocalization.Away e Γ(Spec (CommRingCat.of W), V) := away_rho W e V hVe
  haveI : IsLocalization.Away (algebraMap W (Localization.AtPrime q.asIdeal) e)
      Γ(Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)), j ⁻¹ᵁ V) := by
    refine away_rho (Localization.AtPrime q.asIdeal) (algebraMap W (Localization.AtPrime q.asIdeal) e) (j ⁻¹ᵁ V) ?_
    ext x
    have := Set.ext_iff.1 hVe (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal)) x)
    exact this
  refine UpperTheory.exists_idempotent_submonoid_isLocalization_away (L := Localization.AtPrime q.asIdeal) e he T (fun s hs => (hT s hs).1) (j.app V).hom ?_
  intro r
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have key : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (Spec (CommRingCat.of W)).presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ j.app V =
      CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime q.asIdeal))).inv ≫
        (Spec (CommRingCat.of (Localization.AtPrime q.asIdeal))).presheaf.map (homOfLE le_top : j ⁻¹ᵁ V ⟶ ⊤).op := by
    rw [j.naturality, reassoc_of% h1]
    rfl
  exact congr($key r)

private theorem sec_part {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hle : f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U)) :
    Function.Injective (f.toNormalization.appLE _ _ hle).hom ∧
    ∀ b, b ∈ (f.toNormalization.appLE _ _ hle).hom.range ↔ (f.app U).hom.IsIntegralElem b := by
  letI := (f.app U).hom.toAlgebra
  have h := f.normalizationObjIso_hom_val hU
  have h2 : f.toNormalization.appLE _ _ hle = _ := h.symm
  rw [h2]
  have hb := ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).hom
  constructor
  · intro x y hxy
    exact hb.1 (Subtype.ext hxy)
  · intro b
    constructor
    · rintro ⟨x, rfl⟩
      exact ((f.normalizationObjIso hU).hom.hom x).2
    · intro hbi
      obtain ⟨x, hx⟩ := hb.2 ⟨b, hbi⟩
      exact ⟨x, congrArg Subtype.val hx⟩

private theorem hleN {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (U : Y.Opens) :
    f ⁻¹ᵁ U ≤ f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) := by
  have h : f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  exact h.ge

private theorem appLE_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

end UpperTheory.Cb

theorem UpperTheory.Cb.etale_finite_presentation_model_exists :
    LateralTheory.E.BuildCut.LimInt → LateralTheory.E.t_E2Cut.Cont → LateralTheory.E.t_E2Cut.MV → LateralTheory.E.SysFMPf.FMex := by
  intro _ _ _ P _ _ W _ w hW q
  let j := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  let m := GlobalTheory.normalizationLift (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)
  have e1 : j ≫ w.toNormalization = (j ≫ w).toNormalization ≫ m :=
    (GlobalTheory.toNormalization_normalizationLift _ _ _ _ _).symm
  have e2 : m ≫ w.fromNormalization = (j ≫ w).fromNormalization :=
    (GlobalTheory.normalizationLift_comp (j ≫ w) (j ≫ w.toNormalization) w.fromNormalization (𝟙 P) (by simp)).trans
      (Category.comp_id _)
  have hmi : IsIntegralHom m := GlobalTheory.isIntegralHom_normalizationLift _ _ _ _ _
  obtain ⟨hmono, hflat⟩ := UpperTheory.mono_flat_of_affine_appLE_flat_epi w.fromNormalization (j ≫ w).fromNormalization m e2 (fun U hU hle => by
    obtain ⟨S, hS, hL⟩ := loc_part hW q (w ⁻¹ᵁ U) (w.isCompact_preimage hU.isCompact)
    obtain ⟨ht, hr⟩ := sec_part w hU (hleN w U)
    obtain ⟨ht', hr'⟩ := sec_part (j ≫ w) hU (hleN (j ≫ w) U)
    have key : w.toNormalization.appLE _ _ (hleN w U) ≫ j.app (w ⁻¹ᵁ U) =
        m.appLE _ _ hle ≫ (j ≫ w).toNormalization.appLE _ _ (hleN (j ≫ w) U) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_eq e1 _ _ _
    refine UpperTheory.integralClosure_range_isLocalization_idempotent (w.app U).hom (j.app (w ⁻¹ᵁ U)).hom _ _ _ ht ht' hr (fun b => (hr' b).trans Iff.rfl) ?_ S hS hL
    intro c
    exact congr($key c))
  exact ⟨m, e1, e2, hmono, hflat, inferInstance⟩

end
end
end

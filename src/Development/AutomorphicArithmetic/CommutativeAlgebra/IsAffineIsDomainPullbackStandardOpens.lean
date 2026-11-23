module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralOfLocalizationCoverUnitProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveLineStdOpensBasicOpenGenerators
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.Lemma

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsLocalizationAwayOfRangeEqBasicOpen

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen :
    ∀ {U W : Scheme.{0}} [IsAffine U] (a : W ⟶ U) [IsOpenImmersion a] (t : Γ(U, ⊤)),
        Set.range a = (U.basicOpen t : Set U) →
        IsAffine W ∧ (∀ x : Γ(W, ⊤), ∃ (k : ℕ) (y : Γ(U, ⊤)), a.appTop.hom t ^ k * x = a.appTop.hom y) ∧
          ∀ y : Γ(U, ⊤), a.appTop.hom y = 0 → ∃ k : ℕ, t ^ k * y = 0 := by
  intro U W _ a _ t h
  have hr : Set.range a = Set.range (U.basicOpen t).ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let χ := IsOpenImmersion.isoOfRangeEq a (U.basicOpen t).ι hr
  have hfac : χ.hom ≫ (U.basicOpen t).ι = a := IsOpenImmersion.isoOfRangeEq_hom_fac a _ hr
  haveI : IsAffine (U.basicOpen t) := (isAffineOpen_top U).basicOpen t
  have hW : IsAffine W := IsAffine.of_isIso χ.hom
  have happ : ∀ r, a.appTop.hom r =
      χ.hom.appTop.hom (algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) r) := by
    intro r
    rw [← hfac, Scheme.Hom.comp_appTop]
    rfl
  have hl : ∀ x, χ.inv.appTop.hom (χ.hom.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.inv_hom_id]
    simp
  have hr' : ∀ x, χ.hom.appTop.hom (χ.inv.appTop.hom x) = x := by
    intro x
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, χ.hom_inv_id]
    simp
  refine ⟨hW, ?_, ?_⟩
  · intro x
    obtain ⟨⟨ℓ, m⟩, hℓ⟩ := IsLocalization.surj (Submonoid.powers t) (χ.inv.appTop.hom x)
    obtain ⟨k, hk⟩ := m.2
    have hk' : t ^ k = (m : Γ(U, ⊤)) := hk
    have hℓ' : χ.inv.appTop.hom x * algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) (t ^ k) =
        algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) ℓ := by
      rw [hk']
      exact hℓ
    refine ⟨k, ℓ, ?_⟩
    rw [happ, happ, ← hℓ']
    simp only [map_pow, map_mul, hr']
    ring
  · intro y hy
    have h0 : algebraMap Γ(U, ⊤) Γ(U.basicOpen t, ⊤) y = 0 := by
      have h2 := congrArg χ.inv.appTop.hom ((happ y).symm.trans hy)
      rwa [hl, map_zero] at h2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) _ y).mp h0
    exact ⟨k, hk⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralSectionsOfIntegralHomOverAffineChart

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart :
    ∀ (A : Type) [CommRing A] {P Z U L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P),
        IsIntegralHom u → IsPullback f l (terminal.from P) (terminal.from _) →
        ∀ (O : P.Opens), IsAffineOpen O → ∀ (τ : Γ(P, O)), Subring.closure {τ} = ⊤ →
        ∀ (ι : U ⟶ Z) [IsOpenImmersion ι], Set.range ι = ((u ≫ f) ⁻¹ᵁ O : Set Z) →
        ∀ (h : (⊤ : U.Opens) ≤ (ι ≫ u ≫ f) ⁻¹ᵁ O) (x : Γ(U, ⊤)),
          IsIntegral (Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ∪
            {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ})) x := by
  intro A _ P Z U L u l f hu hpb O hO τ hτ ι _ hι h x
  haveI := hu
  haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hV : IsAffineOpen (f ⁻¹ᵁ O) := hO.preimage f
  have hW : u ⁻¹ᵁ (f ⁻¹ᵁ O) = ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    change ((u ≫ f) ⁻¹ᵁ O : Set Z) = _
    rw [← hι]
    simp
  have hb : Function.Surjective (ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h).hom := by
    have key : ∀ (W : Z.Opens) (_ : W = ι ''ᵁ ⊤) (e : ⊤ ≤ ι ⁻¹ᵁ W),
        Function.Surjective (ι.appLE W ⊤ e).hom := by
      rintro W rfl e
      have e2 : ι.appLE (ι ''ᵁ ⊤) ⊤ e = (ι.appIso ⊤).hom := (Scheme.Hom.appIso_hom' ι ⊤).symm
      rw [e2]
      exact (ι.appIso ⊤).commRingCatIsoToRingEquiv.surjective
    exact key _ hW h
  have ha : (u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl).hom.IsIntegral := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact IsIntegralHom.isIntegral_app u _ hV
  set φ := u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl ≫ ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h with hφ
  have hφi : φ.hom.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ ha (RingHom.isIntegral_of_surjective _ hb)
  set S := Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (ι ≫ u ≫ l).appTop).hom ∪ {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ}) with hS
  have hpo := GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback hpb hO
  have e1 : f.app O ≫ φ = (ι ≫ u ≫ f).appLE O ⊤ h := by
    rw [hφ, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_comp_appLE ι (u ≫ f) O _ ⊤ _ _
  have c1 : ∀ y, φ.hom ((f.app O).hom y) ∈ S := by
    intro y
    have hy : y ∈ Subring.closure {τ} := hτ ▸ Subring.mem_top y
    have hle : Subring.closure {τ} ≤ (S.comap φ.hom).comap (f.app O).hom := by
      rw [Subring.closure_le, Set.singleton_subset_iff]
      show φ.hom ((f.app O).hom τ) ∈ S
      rw [← CommRingCat.comp_apply, e1]
      exact Subring.subset_closure (Or.inr rfl)
    exact hle hy
  have e2 : l.appLE ⊤ (f ⁻¹ᵁ O) (by simp) ≫ φ = (ι ≫ u ≫ l).appTop := by
    rw [hφ]
    refine ((Scheme.Hom.appLE_comp_appLE_assoc u l ⊤ (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE ι (u ≫ l) ⊤ _ ⊤ _ _)).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | (congr 1; simp)
      | simp [Scheme.Hom.appLE]
  have c2 : ∀ y, φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) ∈ S := by
    intro y
    have hy : φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) := by
      rw [← CommRingCat.comp_apply, e2]
      simp
    rw [hy]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  set T := S.comap φ.hom with hT
  let g1 := CommRingCat.ofHom ((f.app O).hom.codRestrict T c1)
  let g2 := CommRingCat.ofHom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom.codRestrict T c2)
  have hw : Scheme.Hom.appLE (terminal.from P) ⊤ O (by simp) ≫ g1 =
      Scheme.Hom.appTop (terminal.from (Spec (CommRingCat.of A))) ≫ g2 := by
    ext z
    exact congrArg (fun k => k.hom z) hpo.w
  have hid : hpo.desc g1 g2 hw ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    apply hpo.hom_ext
    · rw [hpo.inl_desc_assoc, Category.comp_id]
      ext z
      rfl
    · rw [hpo.inr_desc_assoc, Category.comp_id]
      ext z
      rfl
  have hall : ∀ y, φ.hom y ∈ S := by
    intro y
    have := congrArg (fun k => k.hom y) hid
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    rw [← this]
    exact ((hpo.desc g1 g2 hw).hom y).2
  obtain ⟨p, hm, hp⟩ := hφi x
  refine ⟨p.map (φ.hom.codRestrict S hall), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsAffineIsDomainPullbackStandardOpens

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private lemma aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : S →+* R)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hp' : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]
    ext n
    simp
  rw [hp', Polynomial.eval_map]
  change Polynomial.eval₂ (e : R →+* S) ((e : R →+* S) a) _ = 0
  rw [Polynomial.eval₂_at_apply, ha, map_zero]

private lemma aic_chart {Z U : Scheme.{0}} (hZ : AICSch Z) (ι : U ⟶ Z) [IsOpenImmersion ι] [IsAffine U] [Nonempty U] :
    AIC Γ(U, ⊤) := by
  have hA : IsAffineOpen (ι ''ᵁ ⊤) := (isAffineOpen_top U).image_of_isOpenImmersion ι
  have hN : ((ι ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨ι x, x, trivial, rfl⟩
  exact aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hA hN)

private lemma range_fst_eq {P Z U V : Scheme.{0}} (g : Z ⟶ P) (O O' : P.Opens) (τ : Γ(P, O))
    (hb : P.basicOpen τ = O ⊓ O') (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z)
    (r2 : Set.range ι₂ = (g ⁻¹ᵁ O' : Set Z)) (h : (⊤ : U.Opens) ≤ (ι₁ ≫ g) ⁻¹ᵁ O) {W : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V)
    (sq : IsPullback a b ι₁ ι₂) :
    Set.range a = (U.basicOpen (((ι₁ ≫ g).appLE O ⊤ h).hom τ) : Set U) := by
  have h1 : Set.range a = Set.range (pullback.fst ι₁ ι₂) := by
    rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  rw [h1, Scheme.Pullback.range_fst, r2, Scheme.basicOpen_appLE, hb]
  ext x
  have hx : x ∈ (ι₁ ≫ g) ⁻¹ᵁ O := h trivial
  constructor
  · intro hx'
    exact ⟨trivial, hx, hx'⟩
  · rintro ⟨-, -, hx'⟩
    exact hx'

private lemma top_appLE {X Y P : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ P) (w : X ⟶ P) (e : f ≫ g = w) (O : P.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ O) (k : (⊤ : X.Opens) ≤ w ⁻¹ᵁ O) : g.appLE O ⊤ h ≫ f.appTop = w.appLE O ⊤ k := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE f g O ⊤ ⊤ h le_top]
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  exact (Category.comp_id _).symm

private lemma ts_eq {P W U V : Scheme.{0}} (O O' : P.Opens) (τ : Γ(P, O)) (σ : Γ(P, O'))
    (hts : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op τ * P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op σ = 1)
    (g₁ : U ⟶ P) (g₂ : V ⟶ P) (h₁ : (⊤ : U.Opens) ≤ g₁ ⁻¹ᵁ O) (h₂ : (⊤ : V.Opens) ≤ g₂ ⁻¹ᵁ O')
    (a : W ⟶ U) (b : W ⟶ V) (e : a ≫ g₁ = b ≫ g₂) :
    a.appTop.hom ((g₁.appLE O ⊤ h₁).hom τ) * b.appTop.hom ((g₂.appLE O' ⊤ h₂).hom σ) = 1 := by
  have k₁ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O := fun x _ => h₁ (show a x ∈ (⊤ : U.Opens) from trivial)
  have k₂ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ O' := by
    rw [e]
    exact fun x _ => h₂ (show b x ∈ (⊤ : V.Opens) from trivial)
  have k₃ : (⊤ : W.Opens) ≤ (a ≫ g₁) ⁻¹ᵁ (O ⊓ O') := fun x hx => ⟨k₁ hx, k₂ hx⟩
  have e₁ := top_appLE a g₁ (a ≫ g₁) rfl O h₁ k₁
  have e₂ := top_appLE b g₂ (a ≫ g₁) e.symm O' h₂ k₂
  have l₁ : P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O ⊤ k₁ := Scheme.Hom.map_appLE _ _ _
  have l₂ : P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op ≫ (a ≫ g₁).appLE (O ⊓ O') ⊤ k₃ =
      (a ≫ g₁).appLE O' ⊤ k₂ := Scheme.Hom.map_appLE _ _ _
  change (g₁.appLE O ⊤ h₁ ≫ a.appTop).hom τ * (g₂.appLE O' ⊤ h₂ ≫ b.appTop).hom σ = 1
  rw [e₁, e₂, ← l₁, ← l₂]
  change ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_left : O ⊓ O' ≤ O)).op |>.hom τ) *
    ((a ≫ g₁).appLE (O ⊓ O') ⊤ k₃).hom (P.presheaf.map (homOfLE (inf_le_right : O ⊓ O' ≤ O')).op |>.hom σ) = 1
  rw [← map_mul, hts, map_one]

private lemma inj_of {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Nontrivial S] (φ : R →+* S) (t : R)
    (ht : IsUnit (φ t)) (ker : ∀ y, φ y = 0 → ∃ k : ℕ, t ^ k * y = 0) : Function.Injective φ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨k, hk⟩ := ker y hy
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ ht0)

theorem UpperTheory.isAffine_isDomain_pullback_standard_opens :
    ∀ (A : Type) [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) [IsOpenImmersion ι₁] [IsOpenImmersion ι₂] [IsAffine U] [IsAffine V],
      StdPair p ι₁ ι₂ → IsAffine (pullback ι₁ ι₂) ∧ (Nonempty ↥(pullback ι₁ ι₂) →
        letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p).appTop).hom).toAlgebra
        IsDomain Γ(pullback ι₁ ι₂, ⊤) ∧ Function.Injective (pullback.fst ι₁ ι₂).appTop.hom ∧ Function.Injective (pullback.snd ι₁ ι₂).appTop.hom ∧
        ∃ T : TC A Γ(pullback ι₁ ι₂, ⊤), T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.fst ι₁ ι₂).appTop.hom ∧
          (T.C : Set Γ(pullback ι₁ ι₂, ⊤)) = Set.range (pullback.snd ι₁ ι₂).appTop.hom) := by
  intro A _ Z U V p hZ ι₁ ι₂ _ _ _ _ hstd
  obtain ⟨L, u, l, f, hu, -, hf, rfl, r1, r2⟩ := hstd
  obtain ⟨τ, σ, a0, a1, gτ, gσ, bτ, bσ, hts⟩ := UpperTheory.projectiveLine_std_opens_basicOpen_generators
  have h1 : (⊤ : U.Opens) ≤ (ι₁ ≫ u ≫ f) ⁻¹ᵁ stdOpen 0 := by
    intro x _
    have m : ι₁ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) := r1 ▸ ⟨x, rfl⟩
    exact m
  have h2 : (⊤ : V.Opens) ≤ (ι₂ ≫ u ≫ f) ⁻¹ᵁ stdOpen 1 := by
    intro x _
    have m : ι₂ x ∈ ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z) := r2 ▸ ⟨x, rfl⟩
    exact m
  have sq : IsPullback (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂) ι₁ ι₂ := IsPullback.of_hasPullback ι₁ ι₂
  have ra := range_fst_eq (u ≫ f) _ _ τ bτ ι₁ ι₂ r2 h1 _ _ sq
  have rb := range_fst_eq (u ≫ f) (stdOpen 1) (stdOpen 0) σ (bσ.trans (inf_comm _ _)) ι₂ ι₁ r1 h2 _ _ sq.flip
  obtain ⟨aff, locA, kerA⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.fst ι₁ ι₂) _ ra
  obtain ⟨-, locB, kerB⟩ := UpperTheory.isAffine_isLocalizationAway_of_range_eq_basicOpen (pullback.snd ι₁ ι₂) _ rb
  refine ⟨aff, fun hne => ?_⟩
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom).toAlgebra
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty U := ⟨pullback.fst ι₁ ι₂ hne.some⟩
  haveI : Nonempty V := ⟨pullback.snd ι₁ ι₂ hne.some⟩
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion ι₁
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion ι₂
  haveI : IsIntegral (pullback ι₁ ι₂) := isIntegral_of_isOpenImmersion (pullback.fst ι₁ ι₂ ≫ ι₁)
  have ts := ts_eq (stdOpen 0) (stdOpen 1) τ σ hts _ _ h1 h2 (pullback.fst ι₁ ι₂) (pullback.snd ι₁ ι₂)
    (by rw [pullback.condition_assoc])
  have injA := inj_of _ _ (IsUnit.of_mul_eq_one _ ts) kerA
  have injB := inj_of _ _ (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans ts)) kerB
  refine ⟨inferInstance, injA, injB, ?_⟩
  exact UpperTheory.isIntegral_of_localization_cover_unit_product _ _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₁ ≫ u ≫ l).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι₂ ≫ u ≫ l).appTop).hom
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [Scheme.Hom.comp_appTop (pullback.fst ι₁ ι₂)]
      rfl)
    (by
      show _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ u ≫ l).appTop).hom
      rw [pullback.condition_assoc, Scheme.Hom.comp_appTop (pullback.snd ι₁ ι₂)]
      rfl)
    injA injB _ _ ts locA locB (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a0 τ gτ ι₁ r1 h1) (UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart A u l f hu hf _ a1 σ gσ ι₂ r2 h2)
    (aic_chart hZ ι₁) (aic_chart hZ ι₂)

end
end
end

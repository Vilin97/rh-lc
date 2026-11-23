module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverAStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatClosedSubschemeFiniteOverLocalRingStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocalStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  first | exact @GlobalTheory.TwistFlat.isClosedImmersion_kerι | exact GlobalTheory.TwistFlat.isClosedImmersion_kerι | (intros; apply GlobalTheory.TwistFlat.isClosedImmersion_kerι <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivial

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e


variable (A) in
theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivialStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (N : LB (A ⊗ T).left), Fam A N → Triv (abelian₂ (GlobalTheory.TwistFlat.bc A φ) (GlobalTheory.TwistFlat.twist A φ N)) := by
  first | exact @GlobalTheory.TwistFlat.triv_lam_twist | exact GlobalTheory.TwistFlat.triv_lam_twist | (intros; apply GlobalTheory.TwistFlat.triv_lam_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameter

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat
open GlobalTheory.StabFlatLocal GlobalTheory.StabFlat GlobalTheory.UU

theorem flat_of_isFinite_twist : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB →
    (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ O : LB B.left, O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) →
    ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left →
    (∀ (T : Over (Sp V)) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ O hO hu H j hj hH hf
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L O hL hO hΘ hu H j hH
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem flat_local : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
    ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left →
    (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) →
    ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (φ : Sp V ⟶ T.left),
    IsFinite (pullback.snd (h ≫ snd A T).left φ) → Flat (pullback.snd (h ≫ snd A T).left φ) := by
  intro R _ A _ hA L hL ha T N hN H h hh hH V _ _ _ φ hfin
  have hB : IsAbelianScheme (bc A φ) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have : IsCommMonObj (bc A φ) := hB.comm
  have hP : IsProjBy (bc A φ).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha V (φ ≫ T.hom)
      _ (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom)) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := LB.isLB_pull hL _
  have hO : (twist A φ N).IsLB := pull_isLB hN.isLB _
  refine flat_of_isFinite_twist GlobalTheory.T.abelianScheme_laws_unconditional.1.globalFns V (bc A φ) hB hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ _ hB hP _ hL') (twist A φ N) hO
    (GlobalTheory.T.lineBundleFamilyAtPoint_lambda_trivial A φ N hN) (ker A φ h) (kerι A φ h) (GlobalTheory.T.isClosedImmersion_fibreOverPointToBaseChange A φ h hh) (fun Y x => ?_) hfin
  rw [GlobalTheory.T.factors_fibreOverPoint_iff_factors_product A φ h Y x, ← hH, GlobalTheory.T.mumfordBundle_iso_family_iff_locally_trivial_translationDiff A T hA L hL N hN]
  exact forall_congr' fun p => exists_congr fun U => and_congr_right' (GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A A φ L hL N hN.isLB Y x U)

end GlobalTheory.TwistFlat

namespace GlobalTheory.TwistFlat

theorem isNoetherianRing_top (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsAffine X]
    (f : X ⟶ Sp R) (hf : LocallyOfFiniteType f) : IsNoetherianRing Γ(X, ⊤) := by
  have h1 : (f.appTop).hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 hf
  have : IsNoetherianRing Γ(Sp R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI := (f.appTop).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp R, ⊤) Γ(X, ⊤) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp R, ⊤) Γ(X, ⊤)

theorem flat_twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  intro R _ _ A _ hA L hL ha T _ hT N hN H h hh hH hfin
  have : IsNoetherianRing Γ(T.left, ⊤) := isNoetherianRing_top R T.left T.hom hT
  let e := T.left.isoSpec
  let f := (h ≫ snd A T).left
  haveI : IsFinite f := hfin
  let H' : Over (Sp Γ(T.left, ⊤)) := Over.mk (f ≫ e.hom)
  have hfin' : IsFinite H'.hom := by
    show IsFinite (f ≫ e.hom)
    infer_instance
  have hflat : Flat (f ≫ e.hom) := by
    refine GlobalTheory.flat_of_isFinite_of_flat_localization_maximal Γ(T.left, ⊤) H' hfin' fun m _ => ?_
    let φ : Sp (Localization.AtPrime m) ⟶ T.left := spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m)) ≫ e.inv
    have hf : IsFinite (pullback.snd f φ) := MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback f φ) hfin
    haveI := flat_local R A hA L hL ha T N hN H h hh hH (Localization.AtPrime m) φ hf
    have sq : IsPullback (pullback.fst f φ) (pullback.snd f φ) (f ≫ e.hom)
        (spMap (algebraMap Γ(T.left, ⊤) (Localization.AtPrime m))) :=
      (IsPullback.of_hasPullback f φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
        (by simp) (by simp [φ])
    show Flat (pullback.snd (f ≫ e.hom) _)
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have hfe : f = (f ≫ e.hom) ≫ e.inv := by simp
  show Flat f
  rw [hfe]
  infer_instance

end GlobalTheory.TwistFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFiniteTwistedKernelOverAffineParameterStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∀ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t) → IsFinite (h ≫ snd A T).left → Flat (h ≫ snd A T).left := by
  first | exact @GlobalTheory.TwistFlat.flat_twisted_kernel | exact GlobalTheory.TwistFlat.flat_twisted_kernel | (intros; apply GlobalTheory.TwistFlat.flat_twisted_kernel <;> assumption)
end
end

module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicLiftRegularOfPeriodsZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomFromConstThickeningOfDerivationStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Mathlib.RingTheory.Flat.EquationalCriterion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicLiftRegularOfPeriodsZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.holomorphic_lift_regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  first | exact @GlobalTheory.KS.regular_of_periods_zero | exact GlobalTheory.KS.regular_of_periods_zero | (intros; apply GlobalTheory.KS.regular_of_periods_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalDerivationOfKodairaSpencerZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory

theorem exists_locDer_top_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hpb D s hD hs
  have key : ∀ (W : X.Opens) (f : Γ(X, W)), ∃! a : Γ(P₀.A.left, m ⁻¹ᵁ W),
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
    intro W f
    refine existsUnique_section_of_locally_regular P₀ u Hm χ hu (m ⁻¹ᵁ W) (fun z => s z W f) fun z hz => ?_
    have hz' : ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ) ∈ W := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz' W.isOpen
    have hle' : W₀ ≤ W := hle
    obtain ⟨a, ha⟩ := GlobalTheory.T.holomorphic_lift_regular_of_periods_zero hL P₀ u Hm χ hu R x₀ X p m hp hpb D s hD hs W₀ hW₀ W₀ le_rfl (resG X hle' f)
    refine ⟨m ⁻¹ᵁ W₀, a, fun _ hy => hle' hy, (top_le_preimage_iff_mem ((u.ex z).left ≫ m) W₀).2 hzW₀, fun z' hz' => ?_⟩
    exact (ha z' hz').trans ((hs.der z').res W W₀ hle' hz' f)
  choose d hd hu' using key
  have ext : ∀ (W : X.Opens) (f : Γ(X, W)) (a : Γ(P₀.A.left, m ⁻¹ᵁ W)),
      (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f) → d W f = a :=
    fun W f a h => (hu' W f a h).symm
  refine ⟨d, ⟨fun W _ f f' => ext W _ _ fun z hz => ?_, fun W _ f f' => ext W _ _ fun z hz => ?_,
    fun W W' i _ f => ext W' _ _ fun z hz => ?_, fun W _ r => ext W _ _ fun z hz => ?_⟩⟩
  · rw [valAt'_add, hd W f z hz, hd W f' z hz, (hs.der z).add W hz]
  · rw [valAt'_add, valAt'_mul, valAt'_mul, valAt'_comp, valAt'_comp, hd W f z hz, hd W f' z hz,
      (hs.der z).mul W hz]
  · rw [(hs.der z).res W W' i hz, ← hd W f z fun _ hy => i (hz hy)]
    exact valAt'_res _ _ _ hz
  · have e : constFn p W r = resG X le_top (constFn p ⊤ r) := by
      unfold constFn
      exact (congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (V' := W) le_top (homOfLE le_top).op)).symm
    rw [e, (hs.der z).res ⊤ W le_top hz, hs.base]
    exact valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalDerivationOfKodairaSpencerZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  first | exact @GlobalTheory.exists_locDer_top_of_ksRel_zero | exact GlobalTheory.exists_locDer_top_of_ksRel_zero | (intros; apply GlobalTheory.exists_locDer_top_of_ksRel_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoThickeningMapOfModEps

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ThickeningIso

theorem bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp

theorem ker_appTop {A C : CommRingCat.{0}} {β : A ⟶ C} (hβ : Function.Surjective β) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Y] :
    RingHom.ker i.appTop.hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (isAffineOpen_top _))
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop
      ((Scheme.ΓSpecIso C).inv ≫ f'.appTop) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · rw [← Scheme.ΓSpecIso_naturality]
      congr 1
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem surjective_fst (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

theorem isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by
  have hs := surjective_fst K
  have h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have h2 : IsClosedImmersion (j ≫ e) := MorphismProperty.of_isPullback h'.flip h1
  have hY : IsAffine Y := isAffine_of_isAffineHom (j ≫ e)
  have hY' : IsAffine Y' := by
    refine AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
      (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']
    exact this
  suffices hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e
  rw [ConcreteCategory.isIso_iff_bijective]
  have k := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h
  have k' := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'
  have hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)
  have hsur : Function.Surjective (j ≫ e).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2
  rw [Scheme.Hom.comp_appTop] at k k' hfl hsur
  exact bijective_of_mod_eps
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom
    hfl hsur k' k

theorem isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance

end GlobalTheory.ThickeningIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoThickeningMapOfModEpsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.isIso_thickening_map_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  first | exact @GlobalTheory.ThickeningIso.isIso_of_mod_eps | exact GlobalTheory.ThickeningIso.isIso_of_mod_eps | (intros; apply GlobalTheory.ThickeningIso.isIso_of_mod_eps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstOfKsRelZero

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem isDer_snd_of_ringHom {R : Type} [CommRing R] (xD : R →+* DualNumber ℂ) :
    IsDer ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) (fun r => (xD r).snd) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [map_add (f := _), TrivSqZeroExt.snd_add]
  · simp only [map_mul, TrivSqZeroExt.snd_mul, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

theorem spMap_fst_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap Sp
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem exists_isConst_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  intro hL P₀ u Hm χ hU R _ xD A _ A' _ φ j s hA hA' hφ hj hKS

  have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD =
      spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (j ≫ φ) P₀.A.hom A.hom
      (spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD)) := by
    rw [← hcomp]
    exact hj.1.paste_horiz hφ.1

  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero hL P₀ u Hm χ hU R _ A.left A.hom (j ≫ φ) hA.smooth hsq
    (fun r => (xD r).snd) s (isDer_snd_of_ringHom xD) hKS

  obtain ⟨Y', ρ, π, hpb⟩ : ∃ (Y' : Scheme.{0}) (ρ : Y' ⟶ P₀.A.left) (π : Y' ⟶ Sp (DualNumber ℂ)),
      IsPullback ρ π P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hw : 𝟙 P₀.A.left ≫ P₀.A.hom =
      (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, spMap_fst_comp_algebraMap, Category.comp_id, Category.id_comp]
  obtain ⟨i, hiρ, hiπ⟩ := hpb.exists_lift (𝟙 _) (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) hw

  have hm : (j ≫ φ) ≫ A.hom =
      P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hiΦ, hΦ⟩ :=
    GlobalTheory.T.exists_hom_from_const_thickening_of_derivation P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ R xD A.left A.hom (j ≫ φ) d hm hd

  obtain ⟨e, heφ, heπ⟩ := hφ.1.exists_lift Φ π hΦ
  have hie : i ≫ e = j := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, heφ, hiΦ]
    · rw [Category.assoc, heπ, hiπ, hj.1.w]

  have hpb' := (GlobalTheory.T.const_thickening_complex_functions_structure P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ).2.1
  have := P₀.isAb.smooth
  have hfl : Flat π := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have he : IsIso e := GlobalTheory.T.isIso_thickening_map_of_mod_eps P₀.A.left Y' A'.left P₀.A.hom π A'.hom i j e hpb' hj.1 hfl heπ hie

  have hsq2 : IsPullback (inv e) A'.hom π (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heπ]⟩
  have hρ₀ : IsPullback (inv e ≫ ρ) A'.hom P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) := by
    have h := hsq2.paste_horiz hpb
    rwa [Category.id_comp] at h
  have hjρ : j ≫ inv e ≫ ρ = 𝟙 _ := by
    rw [← hie, Category.assoc, IsIso.hom_inv_id_assoc, hiρ]
  exact exists_isConst_of_isPullback hL P₀.A A' (inv e ≫ ρ) j P₀.isAb hA' hj hρ₀ hjρ

end GlobalTheory.KS
end
end
end

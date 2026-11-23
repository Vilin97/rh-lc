module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairLiftsGlueToMorphismOfLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsNaturalOfObstructionOneZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSectionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClass

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_isOb1 : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l hL hL' hl w
  classical
  have hdiff : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      (L'.ρ a).comp (l T) b - (l T').comp (L.ρ (n.G.map a)) b ∈ I.map (algebraMap R (L'.B T')) := by
    intro T T' a b
    rw [← L'.ker, map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply, L'.nat]
    rw [hl, hl, L.nat]
    exact (n.naturality a _).symm
  have hκ : ∀ (T T' : C') (a : T ⟶ T'), ∃ κ : Ω[F.obj (n.G.obj T)⁄R₀] →+ L'.B T',
      IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) κ := fun T T' a ↦
    ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L'.B T') I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) _).1 _ (hdiff T T' a)).exists
  choose κ hκ using hκ
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) σ := fun T ↦
    GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ hσ using hσ
  have hz : ∀ (T T' : C') (a : T ⟶ T'), ∃ y : R₁ ⊗[R₀] F'.obj T', α.KerQ y ∧ σ T' y = κ T T' a (w.1 _) :=
    fun T T' a ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T')
      (L'.surj T') (L'.ker T') (σ T') (hσ T')).2.2.2 _ ((hκ T T' a).mem _)
  choose z hzq hzs using hz

  have hcomp : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (x : Ω[F.obj (n.G.obj T)⁄R₀]),
      κ T T'' (a ≫ b) x = L'.ρ b (κ T T' a x) + κ T' T'' b (p1 F (n.G.map a) x) := by
    intro T T' T'' a b x
    have t1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T') (L'.B T'') _ _ _ (hκ T T' a)).1 (L'.ρ b)
    have t2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj T')) (F.obj (n.G.obj T')) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _) (L.surj _) (L.ker _)
      (L'.B T'') (L'.B T'') _ _ _ (hκ T' T'' b)).2 (L.ρ (n.G.map a)) (mp F (n.G.map a)) (fun y ↦ L.nat _ y)
    have e0 : ((L'.ρ b).comp (l T')).comp (L.ρ (n.G.map a)) = (L'.ρ b).comp ((l T').comp (L.ρ (n.G.map a))) :=
      AlgHom.ext fun _ ↦ rfl
    rw [e0] at t2
    have t3 := ((GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ _ _ _ t1).2.1 t2)
    have e1 : (L'.ρ b).comp ((L'.ρ a).comp (l T)) = (L'.ρ (a ≫ b)).comp (l T) :=
      AlgHom.ext fun y ↦ (hL' a b _).symm
    have e2 : ((l T'').comp (L.ρ (n.G.map b))).comp (L.ρ (n.G.map a)) = (l T'').comp (L.ρ (n.G.map (a ≫ b))) :=
      AlgHom.ext fun y ↦ by
        show l T'' (L.ρ (n.G.map b) (L.ρ (n.G.map a) y)) = l T'' (L.ρ (n.G.map (a ≫ b)) y)
        rw [Functor.map_comp, hL]
    rw [e1, e2] at t3
    have e3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk (L.B (n.G.obj T)) (F.obj (n.G.obj T)) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (L'.B T'') _ _ ((l T'').comp (L.ρ (n.G.map (a ≫ b)))) _ _ (hκ T T'' (a ≫ b))).2.2.1 t3
    exact congrArg (fun f ↦ f x) e3
  let zc : Z1 (ext R₁ F') := ⟨fun T T' a ↦ z T T' a, fun T T' T'' a b ↦ by
    have sn := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B T') (F'.obj T') (L'.p T') (L'.semi T') (L'.surj T')
      (L'.ker T') (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'') (L'.ker T'') (L'.ρ b) (mp F' b)
      (fun y ↦ L'.nat b y) (σ T') (σ T'') (hσ T') (hσ T'')
    change z T T'' (a ≫ b) = extHom R₁ (mp F' b) (z T T' a) + z T' T'' b
    rw [← sub_eq_zero]
    haveI := L'.smooth T''
    refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L'.B T'') (F'.obj T'') (L'.p T'') (L'.semi T'') (L'.surj T'')
      (L'.ker T'') (σ T'') (hσ T'') _ ?_ ?_
    · have h1 := hzq T T'' (a ≫ b)
      have h2 := sn.2 _ (hzq T T' a)
      have h3 := hzq T' T'' b
      unfold Aug.KerQ at h1 h2 h3 ⊢
      rw [map_sub, map_add (f := _), h1, h2, h3]; simp
    · rw [map_sub, map_add (f := _), ← sn.1, hzs, hzs, hzs, hcomp, w.2 (n.G.map a)]
      simp⟩
  exact ⟨H1.mk _ zc, κ, σ, zc, hκ, hσ, rfl, fun T T' a ↦ ⟨hzq T T' a, hzs T T' a⟩⟩

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeOneObstructionClassStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_degreeOneObstructionClass : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsFun → L'.IsFun → L.IsLift L' n l → ∀ w : Glob1 F, ∃ c, L.IsOb1 L' n l α w c := by
  first | exact @GlobalTheory.Obs.exists_isOb1 | exact GlobalTheory.Obs.exists_isOb1 | (intros; apply GlobalTheory.Obs.exists_isOb1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmoothStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_hom_of_reduction_squareZero_smooth : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B] (φ : B₀ →ₐ[R₀] B₀'), ∃ ρ : B →ₐ[R] B', ∀ b, p' (ρ b) = φ (p b) := by
  first | exact @GlobalTheory.Obs.homLift | exact GlobalTheory.Obs.homLift | (intros; apply GlobalTheory.Obs.homLift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebraStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_squareZeroAugmentedAlgebra : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  first | exact @GlobalTheory.Obs.exists_aug | exact GlobalTheory.Obs.exists_aug | (intros; apply GlobalTheory.Obs.exists_aug <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLift

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.MulLift

variable {S S' : Scheme.{0}}

theorem isPullback_tensor {A' B' : Over S'} {A B : Over S} {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsPullback f A'.hom A.hom b) (n : IsPullback g B'.hom B.hom b) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsPullback h (A' ⊗ B').hom (A ⊗ B).hom b := by
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A' B').left (snd A' B').left A'.hom B'.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← n.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert n
  rwa [Over.w, Over.w] at r

theorem smooth_tensor {X Y : Over S} (hX : Smooth X.hom) (hY : Smooth Y.hom) : Smooth (X ⊗ Y).hom := by
  haveI := hX
  haveI := hY
  rw [Over.tensorObj_hom, Limits.pullback.condition]
  infer_instance

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    i ≫ (lift U V).left = (lift u v).left ≫ l := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_match {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀} {A : Over (Sp R₀)} [GrpObj A]
    {X : Over (Sp R)} {i : A.left ⟶ X.left} (h : IsPullback i A.hom X.hom (spMap π)) {e : Sp R ⟶ X.left}
    (he : e ≫ X.hom = 𝟙 _) (hie : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A).left ≫ i = spMap π ≫ e) :
    i ≫ (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)).left = (1 : A ⟶ A).left ≫ i := by
  have e₁ : (1 : 𝟙_ (Over (Sp R₀)) ⟶ A) = η[A] := by simp [Hom.one_def]
  change _ = (toUnit A ≫ η[A]).left ≫ i
  rw [Over.comp_left, Over.comp_left, toUnit_left, toUnit_left]
  change i ≫ X.hom ≫ e = (A.hom ≫ η[A].left) ≫ i
  rw [← Category.assoc i, h.w, Category.assoc, Category.assoc, ← e₁]
  exact congrArg (A.hom ≫ ·) hie.symm

end GlobalTheory.Obs.MulLift

namespace GlobalTheory.Obs


open MulLift in
theorem mul_lifts : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left),
    IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left),
    l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  intro hF hAx R R₀ _ _ I hI π hπ hk A₀ _ g hab hg X i h hX e he hie l hl₁ hl₂
  have hl : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := isPullback_tensor h h hl₁ hl₂
  have hsm : Smooth (X ⊗ X).hom := smooth_tensor hX hX
  obtain ⟨S, ⟨P⟩⟩ := GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk A₀.left A₀.hom X.left X.hom i h hX
  obtain ⟨S', ⟨P'⟩⟩ :=
    GlobalTheory.T.exists_squareZeroSmoothLiftSystem_presents R R₀ I hI π hπ hk (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (X ⊗ X).left (X ⊗ X).hom l hl hsm
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.T.exists_squareZeroAugmentedAlgebra R R₀ I hI π hπ hk
  have hh : (μ[A₀]).left ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀) := overW μ[A₀]
  have hlift : ∀ T : (Pair (μ[A₀]).left)ᵒᵖ,
      ∃ ρ : (ofSys S).B ((pairPull hh).G.obj T) →ₐ[R] (pairPre S' (μ[A₀]).left).B T,
        ∀ b, (pairPre S' (μ[A₀]).left).p T (ρ b) = (pairPull hh).α T ((ofSys S).p _ b) := fun T ↦ by
    haveI := (ofSys S).smooth ((pairPull hh).G.obj T)
    exact GlobalTheory.T.exists_lift_hom_of_reduction_squareZero_smooth R R₀ I hI π hπ hk _ _ ((ofSys S).p _) ((ofSys S).semi _) ((ofSys S).surj _)
      ((ofSys S).ker _) _ _ ((pairPre S' (μ[A₀]).left).p T) ((pairPre S' (μ[A₀]).left).semi T)
      ((pairPre S' (μ[A₀]).left).surj T) ((pairPre S' (μ[A₀]).left).ker T) (coefHom (pairPull hh) T)
  choose l₀ hl₀ using hlift
  have hL : (ofSys S).IsLift (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ := hl₀
  obtain ⟨Pp, Fa, -⟩ := hF R₀ A₀ g hab hg
  have hu : (lift (𝟙 A₀) 1).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one, Over.id_left]
  have hu' : (lift 1 (𝟙 A₀)).left ≫ (μ[A₀]).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul, Over.id_left]
  have hob : ∀ w, (ofSys S).IsOb1 (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeOneObstructionClass R R₀ I hI π hπ hk R₁ α _ _ _ _ (ofSys S) (pairPre S' (μ[A₀]).left) (pairPull hh)
      l₀ (ofSys_isFun S) ((ofSys_isFun S').restrict _) hL w
    obtain ⟨⟨-, hsurj⟩, -⟩ := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ _ _ (A₀ ⊗ A₀).hom (μ[A₀]).left).1
    obtain ⟨c', rfl⟩ := hsurj c
    have ax₁ : IsExtendedPullbackDegOne R₁ (overW (lift (𝟙 A₀) 1)) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift (𝟙 A₀) 1).left (overW _)
        (lift (𝟙 X) (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X))).left hu
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (by simp) (one_match h he hie)) l₀ hL w c' hc
    have ax₂ : IsExtendedPullbackDegOne R₁ (overW (lift 1 (𝟙 A₀))) c' 0 :=
      GlobalTheory.T.retractionLiftObstruction_zero_of_liftedSection R R₀ I hI π hπ hk R₁ α _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl S S' P P'
        (μ[A₀]).left hh (lift 1 (𝟙 A₀)).left (overW _)
        (lift (toUnit X ≫ (Over.homMk e (by simpa using he) : 𝟙_ (Over (Sp R)) ⟶ X)) (𝟙 X)).left hu'
        (Over.w _) (lift_match hl₁ hl₂ _ _ _ _ (one_match h he hie) (by simp)) l₀ hL w c' hc
    have h0 : c' = 0 := hAx R₀ R₁ α.q α.sq A₀ g hab hg c' ax₁ ax₂
    subst h0
    simpa using hc
  obtain ⟨l', hL', hN'⟩ := GlobalTheory.T.lifts_natural_of_obstructionOne_zero R R₀ I hI π hπ hk R₁ α A₀.left A₀.hom Pp Fa _ _ (ofSys S)
    (pairPre S' (μ[A₀]).left) (pairPull hh) l₀ hL hob
  obtain ⟨f, hfs, hfk⟩ := GlobalTheory.T.affinePairLifts_glue_to_morphism_of_lifts R R₀ I hI π hπ hk _ _ _ _ A₀.hom (A₀ ⊗ A₀).hom X.hom (X ⊗ X).hom i l h hl
    S S' P P' (μ[A₀]).left hh l' hL' hN'
  exact ⟨Over.homMk f hfs, hfk⟩

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLiftStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift : FormSt → AxesVanishingExtendedDegOne → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom → ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i → ∃ m : X ⊗ X ⟶ X, l ≫ m.left = (μ[A₀]).left ≫ i := by
  first | exact @GlobalTheory.Obs.mul_lifts | exact GlobalTheory.Obs.mul_lifts | (intros; apply GlobalTheory.Obs.mul_lifts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem unobDim_of_formSt : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  intro hF hP hA R _ I hI R₀ _ π hπ hk A₀ _ g hab hsm
  obtain ⟨X, i, hpb, hsmX⟩ := GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero hF hP R R₀ I hI π hπ hk A₀ g hab hsm
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
  have h1 : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ A₀.hom = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀)
  obtain ⟨e, he, he'⟩ := GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb hsmX _ h1
  have P := IsPullback.of_hasPullback X.hom X.hom
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    simp only [Category.assoc, hpb.w]
    rw [← Category.assoc, ← Category.assoc, Over.w (fst A₀ A₀), Over.w (snd A₀ A₀)]
  let l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left := P.lift _ _ w
  have l1 : l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := P.lift_fst _ _ w
  have l2 : l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := P.lift_snd _ _ w
  obtain ⟨m, hm⟩ := GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift hF hA R R₀ I hI π hπ hk A₀ g hab hsm X i hpb hsmX e he he' l l1 l2
  obtain ⟨G, hG, hab'⟩ := GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hab X i hpb hsmX e he he'
    l l1 l2 m hm
  exact ⟨X, G, i, hG, hab'⟩

end GlobalTheory.Obs
end
end

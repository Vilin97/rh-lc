module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleAwayOfBijectiveMapBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorPrimeComapCompatStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.AffFib

theorem etale_basicOpen_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  have e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ =
      (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [e]
  have key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := HasRingHomProperty.Spec_iff (P := @Etale)
  rw [← key]
  constructor
  · intro H
    have e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
        (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫
          Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
      (Iso.inv_hom_id_assoc _ _).symm
    rw [e2]; infer_instance
  · intro H; infer_instance

end GlobalTheory.Mum.AffFib

theorem GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  intro A C B φ ψ Ω _ ω W w hw hE
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set F := pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _)
    (by simp [Spec.map_comp]) (by simp) with hFdef
  haveI := hE
  let θ := Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)
  let θc : CommRingCat.of (TensorProduct A Ω C) ⟶ CommRingCat.of (TensorProduct A Ω B) :=
    CommRingCat.ofHom θ.toRingHom
  have pB : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω B)))
      (Spec.map (φ ≫ ψ)) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω B)).flip
  have pC : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A Ω C).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω C)))
      (Spec.map φ) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω C)).flip
  let eB := pB.isoPullback
  let eC := pC.isoPullback
  have hF : eB.hom ≫ F = Spec.map θc ≫ eC.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, hFdef, pullback.lift_fst,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hFdef, pullback.lift_snd,
        ← Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp, Category.comp_id]
      congr 1
      ext c
      simp [θc, θ]
  have hθ : Spec.map θc = eB.hom ≫ F ≫ eC.inv := by
    rw [← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let U : (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens := eB.hom ⁻¹ᵁ W
  let y := eB.inv w
  have hy : y ∈ U := by
    show eB.hom (eB.inv w) ∈ W
    simpa using hw
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy U.2
  have hD : (show (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens from PrimeSpectrum.basicOpen f) ≤ U := hfU
  refine ⟨y.asIdeal, y.isPrime, f, ?_, (PrimeSpectrum.mem_basicOpen f y).1 hyf, ?_⟩
  · have : pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom) y := by
      rw [← pB.isoPullback_hom_fst]
      show _ = (eB.hom ≫ pullback.fst _ _) (eB.inv w)
      simp
    rw [this]
    rfl
  · refine (GlobalTheory.Mum.AffFib.etale_basicOpen_iff _ _ θc f).1 ?_
    rw [hθ, ← Scheme.homOfLE_ι _ hD]
    have e1 : (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ U.ι ≫ eB.hom ≫ F ≫ eC.inv =
        (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ (eB.hom ∣_ W) ≫ (W.ι ≫ F) ≫ eC.inv := by
      rw [← Category.assoc (U.ι), ← morphismRestrict_ι]
      simp only [Category.assoc]
    rw [Category.assoc, e1]
    infer_instance
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.etale_localisation_of_etale_affine_fibre' : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  first | exact @GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | exact GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre | (intros; apply GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEtaleRestrictOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem fibre_etale_restrict_open : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  intro T X Z T' X' Z' S p q h hh p' q' h' hh' iT iX iZ _ _ _ sZ sh x x' sx W w hw hz hE
  have hp : p' ≫ iT = iX ≫ p := by
    simp only [← hh, ← hh', Category.assoc, ← sZ]
    simp only [← Category.assoc, sh]
  have hs : x' ≫ iT = 𝟙 S ≫ x := by simp [sx]
  let j := pullback.map p' x' p x iX (𝟙 S) iT hp hs
  let jZ := pullback.map q' x' q x iZ (𝟙 S) iT sZ.symm hs
  obtain ⟨a', ha'⟩ := hz
  have hwr : w ∈ Set.range j := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨a', ha'⟩, ⟨pullback.snd p x w, by simp⟩⟩
  obtain ⟨w', rfl⟩ := hwr
  set F := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp) with hF
  set F' := pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp) with hF'
  have hnat : j ≫ F = F' ≫ jZ := by
    apply pullback.hom_ext
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, sh]
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.comp_id]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨j ⁻¹ᵁ W, w', hw, ?_, ?_⟩
  · have e1 : j ≫ pullback.fst p x = pullback.fst p' x' ≫ iX := pullback.lift_fst _ _ _
    have e2 := congrArg (fun f : pullback p' x' ⟶ X => f w') e1
    simp only [Scheme.Hom.comp_apply] at e2
    exact e2.symm
  · have e : ((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ = (j ∣_ W) ≫ (W.ι ≫ F) := by
      rw [Category.assoc, ← hnat, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have : Etale (((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ) := by
      rw [e]; infer_instance
    exact Etale.of_comp _ jZ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEtaleRestrictOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.fibre_etale_restrict_open_alt : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  first | exact @GlobalTheory.fibre_etale_restrict_open | exact GlobalTheory.fibre_etale_restrict_open | (intros; apply GlobalTheory.fibre_etale_restrict_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_basicOpen_comp_SpecMap_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  exact GlobalTheory.Mum.AffFib.etale_basicOpen_iff S R θ f

theorem etale_image_comp_of_etale (X Z X' Z' : Scheme.{0}) (h : X ⟶ Z) (h' : X' ⟶ Z') (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
    [IsOpenImmersion iX] [IsOpenImmersion iZ] (sh : iX ≫ h = h' ≫ iZ) (U : X'.Opens) :
    Etale (U.ι ≫ h') → Etale ((iX ''ᵁ U).ι ≫ h) := by
  intro hE
  have e : (iX ''ᵁ U).ι ≫ h = (iX.isoImage U).inv ≫ (U.ι ≫ h') ≫ iZ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc, sh, Category.assoc]
  rw [e]
  infer_instance

end GlobalTheory.Mum

theorem GlobalTheory.Mum.etale_near_of_etale_fibre : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T) (W : (pullback p x).Opens) (w : ↥(pullback p x)), w ∈ W → Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ V : X.Opens, pullback.fst p x w ∈ V ∧ Etale (V.ι ≫ h) := by
  intro T X Z p q h hh hp hq Ω _ x W w hw hE
  subst hh
  obtain ⟨UA, hUA, hzA, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
    (show (h ≫ q) (pullback.fst (h ≫ q) x w) ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨UC, hUC, hzC, hCA⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show h (pullback.fst (h ≫ q) x w) ∈ q ⁻¹ᵁ UA by simpa using hzA)
  obtain ⟨UB, hUB, hzB, hBC⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show pullback.fst (h ≫ q) x w ∈ h ⁻¹ᵁ UC from hzC)
  have hUA' : IsAffineOpen UA := hUA
  have hUB' : IsAffineOpen UB := hUB
  have hUC' : IsAffineOpen UC := hUC
  haveI := hUA'.isOpenImmersion_fromSpec
  haveI := hUB'.isOpenImmersion_fromSpec
  haveI := hUC'.isOpenImmersion_fromSpec
  have hxr : Set.range x ⊆ Set.range hUA'.fromSpec := by
    rw [hUA'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain rfl : y = pullback.snd (h ≫ q) x w := Subsingleton.elim _ _
    have := congrArg (fun g => g w) (pullback.condition (f := h ≫ q) (g := x))
    simp only [Scheme.Hom.comp_apply] at this
    show x (pullback.snd (h ≫ q) x w) ∈ UA
    rw [← this]; simpa using hzA
  set φ := q.appLE UA UC hCA
  set ψ := h.appLE UC UB hBC
  let x' := IsOpenImmersion.lift hUA'.fromSpec x hxr
  let ω : Γ(T, UA) ⟶ CommRingCat.of Ω := Spec.preimage x'
  have sx : Spec.map ω ≫ hUA'.fromSpec = x := by
    simp only [ω, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨W', w', hw', hfst, hE'⟩ := GlobalTheory.T.fibre_etale_restrict_open_alt T X Z _ _ _ (Sp Ω) (h ≫ q) q h rfl
    (Spec.map (φ ≫ ψ)) (Spec.map φ) (Spec.map ψ) (by rw [Spec.map_comp])
    hUA'.fromSpec hUB'.fromSpec hUC'.fromSpec (hUA'.SpecMap_appLE_fromSpec q hUC' hCA).symm
    (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm x (Spec.map ω) sx W w hw
    (by rw [hUB'.range_fromSpec]; exact hzB) hE
  have hex := GlobalTheory.T.etale_localisation_of_etale_affine_fibre' _ _ _ φ ψ Ω ω W' w' hw' hE'
  dsimp only at hex
  obtain ⟨Q', hQ', f, hcomap, hf, hEt⟩ := hex
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower Γ(T, UA) Γ(Z, UC) Γ(X, UB) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hQ'
  haveI hQprime : (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have hbij := GlobalTheory.T.localization_tensor_prime_comap_compat Γ(T, UA) Γ(Z, UC) Γ(X, UB) Ω (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal Q' f hcomap hf hEt
  haveI : Algebra.Smooth Γ(T, UA) Γ(Z, UC) := HasRingHomProperty.appLE @Smooth q hq ⟨UA, hUA'⟩ ⟨UC, hUC'⟩ hCA
  haveI : Algebra.Smooth Γ(T, UA) Γ(X, UB) := by
    have := HasRingHomProperty.appLE @Smooth (h ≫ q) hp ⟨UA, hUA'⟩ ⟨UB, hUB'⟩ (hBC.trans (h.preimage_mono hCA))
    rw [← Scheme.Hom.appLE_comp_appLE h q UA UC UB hCA hBC] at this
    exact this
  obtain ⟨g, hg, hgEt⟩ := GlobalTheory.T.exists_etale_away_of_bijective_kaehler_mapBaseChange Γ(T, UA) Γ(Z, UC) Γ(X, UB) (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w').asIdeal hbij
  have hR : ((algebraMap Γ(X, UB) (Localization.Away g)).comp ψ.hom).Etale := by
    have := RingHom.etale_algebraMap.mpr hgEt
    rwa [IsScalarTower.algebraMap_eq Γ(Z, UC) Γ(X, UB) (Localization.Away g)] at this
  have hV := (etale_basicOpen_comp_SpecMap_iff _ _ ψ g).mpr hR
  refine ⟨hUB'.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g), ?_,
    etale_image_comp_of_etale X Z _ _ h (Spec.map ψ) hUB'.fromSpec hUC'.fromSpec
      (hUC'.SpecMap_appLE_fromSpec h hUB' hBC).symm _ hV⟩
  rw [← hfst]
  exact Set.mem_image_of_mem _ hg
end
end

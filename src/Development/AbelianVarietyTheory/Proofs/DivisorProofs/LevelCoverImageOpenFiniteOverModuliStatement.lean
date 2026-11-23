module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCentredPointGenericBothModelsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_openAt_of_levAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  intro g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]
  have hf' : M.pt ≫ f = X.pt := by simpa [RatModel.IsHom, hid] using hf
  have hd' : Y.pt ≫ d = X.pt := by simpa [RatModel.IsHom, hid] using hd
  set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef
  have hUle : U ≤ f ⁻¹ᵁ Xab := fun m hm => hrange hm
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    have e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]
    infer_instance
  have hrng : Set.range (U.ι ≫ f) = Set.range d := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact m.2
    · rintro ⟨y, rfl⟩
      have hy : d y ∈ Xab := hrange ⟨y, rfl⟩
      obtain ⟨m', hm'⟩ := (f ∣_ Xab).surjective ⟨d y, hy⟩
      have h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']
        rfl
      have h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U := ⟨y, h1.symm⟩
      exact ⟨⟨_, h2⟩, h1⟩
  let e := IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng
  have he : e.hom ≫ d = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨-, hfin, hsurj, hs, hpt⟩ := hL
  refine ⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩
  · obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨M.pt w, Y.pt w, ?_⟩
    have h1 : d (Y.pt w) = X.pt w := by rw [← hd']; rfl
    have h2 : f (M.pt w) = X.pt w := by rw [← hf']; rfl
    exact h1.trans h2.symm
  · rw [Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]
    simp only [← Category.assoc, he]
  · intro x hx
    have h : x ≫ e.hom = Y.pt := by
      rw [← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']
    rw [← Category.assoc, h, hpt]

end GlobalTheory.SiegTh

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_open_finite_onto_of_levelCover : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  first | exact @GlobalTheory.SiegTh.exists_openAt_of_levAt | exact GlobalTheory.SiegTh.exists_openAt_of_levAt | (intros; apply GlobalTheory.SiegTh.exists_openAt_of_levAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeSubsetAbelianLocusOfLevelTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegTh

def isPowGrpOfUniv {T : Scheme.{0}} {P C : Over T} [GrpObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C))
    (hpr : ∀ a, IsMonHom (pr a)) (hu : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ P, ∀ a, x ≫ pr a = y a) :
    IsPowGrp P C 8 where
  pr := pr
  hom := hpr
  lim := Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s a => (hu s.pt s.proj).choose_spec.1 a)
    (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)

theorem range_subset_abLocus_of_levelTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
    SysAt F W β S ρ u → ∀ (Y M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (Zh : ZHOut ρ M U₀ EE), LevAt F β u Y q → S.Over₀ M U₀ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z)
      (κ : Ω →+* FractionRing V), spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt →
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt → Set.range ξ ⊆ abLocus Zh.G := by
  intro g n F W o Ω _ _ _ _ β S ρ u hSys Y M q U₀ EE Zh hLev hO V _ _ _ ξ τ κ hξ hτ
  obtain ⟨c, hc, pr, hpr, hu, -⟩ := hSys.2.2.2.1
  obtain ⟨ψ, -, hψ, -⟩ := hc
  obtain ⟨α, hα, -⟩ := PowFibre.exists_pow_pullback (powIsPowGrp F.univ.A 8) (isPowGrpOfUniv pr hpr hu) hψ
  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x' : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx' : x' ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x' ≫ Zh.u₀ = spMap S.R.val.toRingHom := Zh.u₀_gen x' hx'
  let a : Sp (FractionRing V) ⟶ U₀.toScheme := spMap κ ≫ x'
  have ha1 : a ≫ U₀.ι = spMap (algebraMap V (FractionRing V)) ≫ ξ := by
    rw [hξ, Category.assoc, hx']
  have ha2 : a ≫ (Zh.u₀ ≫ u) = spMap (algebraMap V (FractionRing V)) ≫ (τ ≫ q) := by
    calc a ≫ (Zh.u₀ ≫ u) = spMap κ ≫ ((x' ≫ Zh.u₀) ≫ u) := by simp only [a, Category.assoc]
      _ = spMap κ ≫ (Y.pt ≫ q) := by rw [hxu, hLev.2.2.2.2]
      _ = _ := by rw [← Category.assoc, ← hτ, Category.assoc]
  have hA := isGrpPullback_pullback ((Over.pullback Zh.u₀).obj ρ.P.A) a
  have h₂ := (hA.comp Zh.cart).congr ha1 rfl
  have h₃ := (hA.comp ((isGrpPullback_pullback ρ.P.A Zh.u₀).comp hα)).congr ha2 rfl
  obtain ⟨φ₁, h₁⟩ := GoodVal.exists_isGrpPullback_of_comp (powObj F.univ.A 8) (τ ≫ q) _ h₃
  have hab : IsAbelianScheme ((Over.pullback (τ ≫ q)).obj (powObj F.univ.A 8)) :=
    isAbelianScheme_pullback_obj (τ ≫ q) _ (AbelianSchemeGerms.isAbelianScheme_powObj F.univ.A F.univ.ab 7)
  have hz : LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
    have := M.lft
    haveI := ArithBase.ft (o := o) (Ω := Ω)
    have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
    infer_instance
  exact range_subset_abLocus_of_goodReduction
    (existsUnique_hom_extension_semiAbelian_dvr (AbelianSubgroupFinite.finite_of_no_torsion abMulN_holds))
    M.Z _ Zh.G V (FractionRing V) ξ _ _ _ _ hz Zh.semi hab h₁ h₂

end GlobalTheory.SiegTh

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeSubsetAbelianLocusOfLevelTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_levelTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
    SysAt F W β S ρ u → ∀ (Y M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (Zh : ZHOut ρ M U₀ EE), LevAt F β u Y q → S.Over₀ M U₀ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z)
      (κ : Ω →+* FractionRing V), spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt →
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt → Set.range ξ ⊆ abLocus Zh.G := by
  first | exact @GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | exact GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | (intros; apply GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjModelSurj

theorem surjective_of_isProjOver (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z)
    (hf : X.IsHom M (AlgHom.id o Ω) f) (hM : IsProjOver M.s) : Function.Surjective f := by
  obtain ⟨N, i, hi, hs⟩ := hM
  haveI : IsProper (PSpace.str o N) := isProper_str o N
  haveI : IsProper M.s := hs ▸ inferInstance
  haveI : IsSeparated X.s := X.sep
  haveI : IsProper (f ≫ X.s) := by rw [hf.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsProper f := IsProper.of_comp f X.s
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have hgen : genericPoint X.Z ∈ Set.range f := by
    have w : Sp Ω := IsLocalRing.closedPoint Ω
    refine ⟨M.pt w, ?_⟩
    have h : (M.pt ≫ f) w = (spMap (AlgHom.id o Ω).toRingHom ≫ X.pt) w := by rw [hf]
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact X.pt_apply _
  intro x
  obtain ⟨y, hy⟩ := (genericPoint_specializes x).mem_closed hcl hgen
  exact ⟨y, hy⟩

end GlobalTheory.ProjModelSurj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.surjective_functionFieldModelHom_of_projective : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (X M : RatModel o Ω) (f : M.Z ⟶ X.Z),
    X.IsHom M (AlgHom.id o Ω) f → IsProjOver M.s → Function.Surjective f := by
  first | exact @GlobalTheory.ProjModelSurj.surjective_of_isProjOver | exact GlobalTheory.ProjModelSurj.surjective_of_isProjOver | (intros; apply GlobalTheory.ProjModelSurj.surjective_of_isProjOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverImageOpenFiniteOverModuli

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OpenLev

theorem exists_open_finite : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  intro g n _ _ _ F W _ o Ω _ _ _ _ β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin hab hd hdo
  obtain ⟨-, -, -, h0, -, hfM, -, hiso⟩ := hmin
  have hsurj := GlobalTheory.T.surjective_functionFieldModelHom_of_projective o Ω X M fM hfM h0.proj
  have hrange : Set.range d ⊆ Xab := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (d y)
    obtain ⟨V, _, _, _, ξ, τ, κ, hzξ, h1, h2⟩ := GlobalTheory.T.exists_dvr_centred_point_generic_both_models o Ω Y X M fM d hfM hd hdo z ⟨y, hz.symm⟩
    have hzab : z ∈ (abLocus Zh.G : Set M.Z) :=
      GlobalTheory.T.range_subset_abelianLocus_of_levelTrait g n F W o Ω β S ρ u hsys Y M q U₀ EE Zh hlev h0 V ξ τ κ h1 h2 hzξ
    rw [hab] at hzab
    show d y ∈ (Xab : Set X.Z)
    rw [← hz]
    exact hzab
  obtain ⟨U, c, hc, hU⟩ := GlobalTheory.T.exists_open_finite_onto_of_levelCover g n F o Ω β S u Y X M q fM Xab d hlev hfM hiso hd hdo hrange
  exact ⟨U, c, hc, hab ▸ hU⟩

end GlobalTheory.OpenLev
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverImageOpenFiniteOverModuliStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.level_cover_image_open_finite_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  first | exact @GlobalTheory.OpenLev.exists_open_finite | exact GlobalTheory.OpenLev.exists_open_finite | (intros; apply GlobalTheory.OpenLev.exists_open_finite <;> assumption)
end
end

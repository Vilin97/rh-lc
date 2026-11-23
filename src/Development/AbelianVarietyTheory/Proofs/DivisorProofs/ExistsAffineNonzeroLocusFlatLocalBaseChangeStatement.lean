module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocalStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPointStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrpStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGenerator

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PullSecSq

theorem exists_sec_lbPow_two_nonzeroLocus : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  intro Y X f M₀ hM s₀ T₁ T₂ ⟨t, ht⟩
  have hN : (M₀.pull f).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := Sum.elim (Sum.elim (fun _ : PUnit => T₁) (fun _ : PUnit => T₂)) (fun _ : PUnit => 𝟙 Y))
    (ε' := Sum.elim (Sum.elim (fun _ : PUnit => (1 : ℤ)) (fun _ : PUnit => (1 : ℤ)))
      (fun k => - (fun _ : PUnit => ((2 : ℕ) : ℤ)) k)) (by
      intro U _ h
      simp only [Fin.prod_univ_three, Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp) t ht
  have H := AdjointOfPairing.lbIso_of_gen (φ := fun _ : PUnit => 𝟙 Y) (ε := fun _ => ((2 : ℕ) : ℤ)) t' ht'
  obtain ⟨s, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2) (LB.isLB_linComb hN _ _) H
    (DVR.mulSec (M₀.pull f) (fun _ : PUnit => T₁) (fun _ => 1) (fun _ : PUnit => T₂) (fun _ => 1)
      (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₁) (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₂))
  refine ⟨s, hs.trans ?_⟩
  simp only [GlobalTheory.nonzeroLocus_mulSec, GlobalTheory.nonzeroLocus_secPull]
  rfl

end GlobalTheory.PullSecSq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGeneratorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  first | exact @GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | exact GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus | (intros; apply GlobalTheory.PullSecSq.exists_sec_lbPow_two_nonzeroLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_generic_of_injective (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (ρ : R →+* R') (hρ : Function.Injective ρ) (G : Over (Sp R)) [GrpObj G]
    (h : IsAbelianScheme ((Over.pullback (jK R)).obj G)) :
    IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  let ρK : FractionRing R →+* FractionRing R' := IsFractionRing.map (A := R) (B := R') (j := ρ) hρ
  have hc : jK R' ≫ spMap ρ = spMap ρK ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [ρK, IsFractionRing.map, IsLocalization.map_eq]
  have h2 : IsAbelianScheme ((Over.pullback (spMap ρK)).obj ((Over.pullback (jK R)).obj G)) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ h
  have h3 : IsAbelianScheme ((Over.pullback (spMap ρK ≫ jK R)).obj G) :=
    GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (spMap ρK) (jK R) G) inferInstance h2
  rw [← hc] at h3
  exact GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso (pullCompIso (jK R') (spMap ρ) G).symm
    (inferInstanceAs (IsMonHom (pullCompIso (jK R') (spMap ρ) G).inv)) h3

end GlobalTheory.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R'), Function.Injective ρ → ∀ (G : Over (Sp R)) [GrpObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → IsAbelianScheme ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) := by
  first | exact @GlobalTheory.Desc.isAbelianScheme_generic_of_injective | exact GlobalTheory.Desc.isAbelianScheme_generic_of_injective | (intros; apply GlobalTheory.Desc.isAbelianScheme_generic_of_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p → ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧ (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧ Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  first | exact @GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | exact GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular | (intros; apply GlobalTheory.SmoothStalkNormal.stalk_of_smooth_over_regular <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePt

theorem exists_affine_nonzeroLocus_of_square : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  intro H R _ _ _ G _ hG hab M₀ hM s₀ hV hy₀ y
  obtain ⟨z, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local R G hG (nonzeroLocus s₀) hy₀ y
  obtain ⟨hd, hn, hic, hfl, hinj⟩ := GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local R G.left G.hom hG.smooth ((snd G G).left z)
  let R' : Type := G.left.presheaf.stalk ((snd G G).left z)
  let ρ : R →+* R' := (Spec.preimage (G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom)).hom
  have hc : G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom = spMap ρ := (Spec.map_preimage _).symm
  obtain ⟨a, Φ, hpb, hΦ1, hΦ2, hΦ3⟩ := GlobalTheory.T.exists_section_translate_baseChange_of_point R R' ρ G (G.left.fromSpecStalk ((snd G G).left z)) hc
  obtain ⟨x', hx'⟩ : ∃ x', Φ x' = z := by
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (snd G G).left)
      (g := G.left.fromSpecStalk ((snd G G).left z)) z (closedPoint R') Scheme.fromSpecStalk_closedPoint.symm
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
  have e1 : pullback.fst G.hom (spMap ρ) x' = (fst G G).left z := by
    rw [← hΦ1, Scheme.Hom.comp_apply, hx']
  have e2 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * snd G G).left z := by rw [hΦ2, Scheme.Hom.comp_apply, hx']
  have e3 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * (snd G G)⁻¹).left z := by rw [hΦ3, Scheme.Hom.comp_apply, hx']
  have hsemi' : IsSemiAbelian ((Over.pullback (spMap ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := hd; haveI := hn; haveI := hic
  have hab' := GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map R R' ρ hinj G hab
  obtain ⟨t, ht⟩ := H R' ((Over.pullback (spMap ρ)).obj G) hsemi' hab'
    (M₀.pull (pullback.fst G.hom (spMap ρ))) (LB.isLB_pull hM _) a
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator _ _ (pullback.fst G.hom (spMap ρ)) M₀ hM s₀ _ _ ⟨t, ht⟩
  haveI : IsAffineHom (pullback.fst G.hom (spMap ρ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)).flip inferInstance
  have hW : IsAffineOpen (pullback.fst G.hom (spMap ρ) ⁻¹ᵁ nonzeroLocus s₀) := hV.preimage _
  have hL := GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp R' ((Over.pullback (spMap ρ)).obj G) hsemi'.separated a _ hW
  refine ⟨R', inferInstance, ρ, hfl, x', e1.trans hz1, 2, by norm_num, s, ?_, ?_⟩
  · rw [hs]
    exact ⟨(Scheme.Hom.mem_preimage _).2 (e2 ▸ hz2), (Scheme.Hom.mem_preimage _).2 (e3 ▸ hz3)⟩
  · rw [hs, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact hL

end GlobalTheory.AmplePt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_affine_nonzeroLocus_flat_local_baseChange : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  first | exact @GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | exact GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square | (intros; apply GlobalTheory.AmplePt.exists_affine_nonzeroLocus_of_square <;> assumption)
end
end

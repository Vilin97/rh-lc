module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMulStatement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibre
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.IntegralSec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistIso

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvrStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | exact GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | (intros; apply GlobalTheory.GenericIsoConst.exists_iso_const_of_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSectionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integral_twisted_comparison_at_fixed_section : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  first | exact @GlobalTheory.SectionLattice.integralAtSection_of_conj | exact GlobalTheory.SectionLattice.integralAtSection_of_conj | (intros; apply GlobalTheory.SectionLattice.integralAtSection_of_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelian

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SemilinearModel

theorem unit_section_semilinear : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  intro W K' _ _ _ _ _ G _ hG σ τ φ ρ hστ hφ hρ e₀ he x hx hxρ
  haveI := hG.proper
  have hj : spMap σ ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    unfold spMap
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    simp [hστ]
  haveI : IsDominant (spMap (algebraMap W K')) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap W K')).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W K')]; exact bot_le)
    exact this
  refine ext_of_isDominant_of_isSeparated G.hom ?_ (spMap (algebraMap W K')) ?_
  · rw [Category.assoc, hφ, ← Category.assoc, he, Category.assoc, he]; simp
  · rw [← Category.assoc, ← hx, Category.assoc, hρ, ← Category.assoc, hxρ, Category.assoc, hx, ← Category.assoc, hj, Category.assoc]
end GlobalTheory.SemilinearModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelianStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinearModel_fixes_unit_section_abelian : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  first | exact @GlobalTheory.SemilinearModel.unit_section_semilinear | exact GlobalTheory.SemilinearModel.unit_section_semilinear | (intros; apply GlobalTheory.SemilinearModel.unit_section_semilinear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibreStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = spMap (σ : K' →+* K') ≫ x := by
  first | exact @GlobalTheory.semilinear_symm_fixes_unit | exact GlobalTheory.semilinear_symm_fixes_unit | (intros; apply GlobalTheory.semilinear_symm_fixes_unit <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.TwistedSectionsExtend

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C1
open GlobalTheory GlobalTheory.SectionLattice

theorem twisted_sections_extend : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'] (D : Set (K' ≃ₐ[K] K')), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∀ (H : LB A.left) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → M.IsLB → w.IsGen → ∀ σ ∈ D, ∀ (n : ℕ) (s : Fin n → H.Sec) (u : M.Sec) (c : Fin n → K'), GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) → ∃ u' : M.Sec, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull u' (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (σ (c k)) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
  intro K W K' _ _ _ _ _ _ _ _ D hD hD' A _ hA G _ hG e he hφ H M w hH hM hw σ hσ n s u c hu
  obtain ⟨τ, φ, hτ, hφG, hφY⟩ := hφ σ hσ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom
      (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫
      e.inv.left := ⟨_, rfl⟩
  rw [← hρ] at hφY
  have hA' : ρ ≫ (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
      e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) := by
    subst hρ
    have h := congrArg CommaMorphism.left e.inv_hom_id
    simp only [Over.comp_left, Over.id_left] at h
    simp only [Category.assoc]
    rw [reassoc_of% h]
    simp only [pullback.map, Category.id_comp, pullback.lift_fst, Category.comp_id]
  have hq : ρ ≫ pullback.snd G.hom (spMap (algebraMap W K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) ≫ spMap (σ : K' →+* K') := by
    subst hρ
    have h₁ := Over.w e.inv
    have h₂ := Over.w e.hom
    simp only [Over.pullback_obj_hom] at h₁ h₂
    simp only [Category.assoc, h₁]
    simp only [pullback.map, pullback.lift_snd]
    rw [reassoc_of% h₂]
  obtain ⟨w₁, hw₁, hsec, hval⟩ := UpperTheory.Lit.Nos.twistIso M H (pullback.fst G.hom (spMap (algebraMap W K')))
    (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) ρ φ (σ : K' →+* K') hφY hA' hq hM hH w hw
  have he₀ : η[G].left ≫ G.hom = 𝟙 _ := by simpa using Over.w η[G]
  let x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')) :=
    pullback.lift (spMap (algebraMap W K') ≫ η[G].left) (𝟙 _)
      (by rw [Category.assoc, he₀]; simp)
  have hx₁ : x ≫ pullback.fst G.hom (spMap (algebraMap W K')) =
      spMap (algebraMap W K') ≫ η[G].left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ := pullback.lift_snd _ _ _
  have hxρ : x ≫ ρ = spMap (σ : K' →+* K') ≫ x := by
    subst hρ
    exact GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre K W K' A G e he σ x hx₁ hx₂
  have he₀φ := GlobalTheory.T.semilinearModel_fixes_unit_section_abelian W K' G hG (σ : K' →+* K') τ φ ρ hτ hφG hφY η[G].left he₀ x hx₁ hxρ
  have hv := GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul W K' σ.toRingEquiv (hD σ hσ) (hD' σ hσ)
  have hHp : (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))).IsLB :=
    LB.isLB_pull hH _
  have hIAS := GlobalTheory.T.integral_twisted_comparison_at_fixed_section W K' G σ.toRingEquiv τ hv φ η[G].left he₀ he₀φ ρ x hx₁ hx₂ hxρ M _ hM hHp
    w w₁ (hval x hxρ)
  obtain ⟨v, c', hv', hrel⟩ := GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr W K' G hG (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁
  exact UpperTheory.Lit.Nos.integralSec W K' G (M.pull φ) M _ (LB.isLB_pull hM φ) hM hHp w w₁ hw hw₁ hIAS v c' hv' hrel
    (GlobalTheory.Cartier.secPull u φ) _ (hsec n s u c hu)

end UpperTheory.Lit.Nos.C1
end
end
end

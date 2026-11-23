module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubringStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegBundleSpread

theorem lbIso_spread : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ j₂ φ₂ hj hj₂ hej hφ₂ heφ
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ.w
  have hcomp : j₂ ≫ ψ₂ = φ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hj₂ hψ₂ hφ₂
  have hpb : IsPullback j₂ (G2 e.A).hom (G2 d₀.A).hom (spMap R₀.subtype) :=
    GlobalTheory.SiegDesc.isPullback_of_isSquare hj hj₂
  haveI : IsProper d₀.A.hom := d₀.ab.proper
  haveI : IsProper (G2 d₀.A).hom := by
    change IsProper (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom)
    infer_instance
  have hN : (u.P.pull ψ₂).IsLB := pull_isLB u.isLB ψ₂
  have H : LBIso (d₀.P.pull j₂) ((u.P.pull ψ₂).pull j₂) := by
    have a : LBIso (d₀.P.pull j₂) (u.P.pull φ₂) :=
      LBIso.trans (pull_isLB d₀.isLB _) e.isLB (pull_isLB u.isLB _) (LBIso.symm hej) heφ
    have b : LBIso (u.P.pull φ₂) ((u.P.pull ψ₂).pull j₂) := by
      rw [← hcomp]
      exact LBIso.symm (GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ j₂)
    exact LBIso.trans (pull_isLB d₀.isLB _) (pull_isLB u.isLB _) (pull_isLB hN _) a b
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ (G2 e.A).left (G2 d₀.A).left
    (G2 e.A).hom (G2 d₀.A).hom j₂ d₀.P (u.P.pull ψ₂) hpb d₀.isLB hN H
  refine ⟨F, fun R₁ hle hFR s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁ hφ₁₂ hd₁ hχ₂ => ?_⟩
  have hcomp₁ : φ₁₂ ≫ ψ₂ = χ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hφ₁₂ hψ₂ hχ₂
  have H₁ := hF R₁ hle hFR (G2 d₁.A).left (G2 d₁.A).hom φ₁₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ₁ hφ₁₂)
  have c : LBIso ((u.P.pull ψ₂).pull φ₁₂) (u.P.pull χ₂) := by
    rw [← hcomp₁]
    exact GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ φ₁₂
  exact LBIso.trans d₁.isLB (pull_isLB hN _) (pull_isLB u.isLB _)
    (LBIso.trans d₁.isLB (pull_isLB d₀.isLB _) (pull_isLB hN _) hd₁ H₁) c

end GlobalTheory.SiegBundleSpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpreadStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.lbIso_spread_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  first | exact @GlobalTheory.SiegBundleSpread.lbIso_spread | exact GlobalTheory.SiegBundleSpread.lbIso_spread | (intros; apply GlobalTheory.SiegBundleSpread.lbIso_spread <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem siegel_levels_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ hj hjψ
  classical
  haveI : Smooth u.A.hom := u.ab.smooth
  have hsec₀ : ∀ a, (d₀.lev a).left ≫ d₀.A.hom = 𝟙 (Sp R₀) := fun a => Over.w (d₀.lev a)
  have hsecu : ∀ a, (u.lev a).left ≫ u.A.hom = 𝟙 Y := fun a => Over.w (u.lev a)
  have key : ∀ i : Fin g ⊕ Fin g, ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      spMap (Subring.inclusion hle) ≫ (d₀.lev (Pi.single i 1)).left ≫ ψ =
        spMap (Subring.inclusion hle) ≫ h₀ ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    let x : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift ((d₀.lev (Pi.single i 1)).left ≫ ψ) (𝟙 _) (by
      rw [Category.assoc, hψ.w, ← Category.assoc, hsec₀, Category.id_comp])
    let y : Sp R₀ ⟶ pullback u.A.hom h₀ := pullback.lift (h₀ ≫ (u.lev (Pi.single i 1)).left) (𝟙 _) (by
      rw [Category.assoc, hsecu, Category.comp_id, Category.id_comp])
    have hx : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hy : y ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hxy : spMap R₀.subtype ≫ x = spMap R₀.subtype ≫ y := by
      apply pullback.hom_ext
      · simp only [x, y, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← hj, Category.assoc, hjψ, Category.assoc]
      · simp only [x, y, Category.assoc, pullback.lift_snd]
    obtain ⟨F, hF⟩ := morphisms_eq_spread_to_subring S R₀ (Sp S) (Sp R₀) (pullback u.A.hom h₀) (𝟙 _) (𝟙 _)
      (pullback.snd _ _) (spMap R₀.subtype) x y (IsPullback.id_vert _) hx hy hxy
    refine ⟨F, fun R₁ hle hF₁ => ?_⟩
    have := congrArg (· ≫ pullback.fst u.A.hom h₀)
      (hF R₁ hle hF₁ (Sp R₁) (𝟙 _) (spMap (Subring.inclusion hle)) (IsPullback.id_vert _))
    simpa only [x, y, Category.assoc, pullback.lift_fst] using this
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ hle hsub s₁ d₁ φ₁ hgp hlev₁ a => ?_⟩
  have hbasis : ∀ i : Fin g ⊕ Fin g, (d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ) =
      (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev (Pi.single i 1)).left := by
    intro i
    have hFi : (F i : Set S) ⊆ R₁ := fun x hx => hsub (by
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨i, hx⟩)
    rw [← Category.assoc, hlev₁, Category.assoc, hF i R₁ hle hFi, Category.assoc]
  let f : Sp R₁ ⟶ Y := spMap (Subring.inclusion hle) ≫ h₀
  let M : Over Y := Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ f)
  have hunit : (toUnit M).left = f := by
    have := Over.w (toUnit M)
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  have w : ∀ a, ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) ≫ u.A.hom = M.hom := by
    intro a
    rw [Category.assoc, hgp.1.w, ← Category.assoc, Over.w (d₁.lev a)]
    rfl
  let Ψ₁ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (toUnit M ≫ u.lev a)) (by
      intro a b
      rw [u.lev_add, comp_mul]
      rfl)
  let Ψ₂ : (Fin g ⊕ Fin g → ℤ) →+ Additive (M ⟶ u.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (Over.homMk ((d₁.lev a).left ≫ (φ₁ ≫ ψ)) (w a) : M ⟶ u.A)) (by
      intro a b
      show Additive.ofMul _ = Additive.ofMul (_ * _)
      congr 1
      apply Over.OverMorphism.ext
      rw [hgp.2 (𝟙_ _) (d₁.lev a) (d₁.lev b) _ _ rfl rfl, ← d₁.lev_add]
      rfl)
  have hΨ : Ψ₁ = Ψ₂ := by
    refine AddMonoidHom.functions_ext' _ _ _ (fun i => AddMonoidHom.ext_int ?_)
    show Additive.ofMul (toUnit M ≫ u.lev (Pi.single i 1)) =
      Additive.ofMul (Over.homMk ((d₁.lev (Pi.single i 1)).left ≫ (φ₁ ≫ ψ)) (w (Pi.single i 1)) : M ⟶ u.A)
    refine congrArg Additive.ofMul (Over.OverMorphism.ext ?_)
    rw [Over.comp_left, hunit]
    exact (hbasis i).symm
  have := congrArg (fun φ => (Additive.toMul (φ a)).left) hΨ
  simp only [Ψ₁, Ψ₂, AddMonoidHom.mk'_apply, toMul_ofMul, Over.comp_left, Over.homMk_left] at this
  rw [← this, hunit]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_level_sections_spread_to_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → (∀ a, (e.lev a).left ≫ j = spMap R₀.subtype ≫ (d₀.lev a).left) → (∀ a, (e.lev a).left ≫ (j ≫ ψ) = (spMap R₀.subtype ≫ h₀) ≫ (u.lev a).left) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left), IsGrpPullback d₁.A u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) → (∀ a, (d₁.lev a).left ≫ φ₁ = spMap (Subring.inclusion hle) ≫ (d₀.lev a).left) → ∀ a, (d₁.lev a).left ≫ (φ₁ ≫ ψ) = (spMap (Subring.inclusion hle) ≫ h₀) ≫ (u.lev a).left := by
  first | exact @GlobalTheory.siegel_levels_spread_to_subring | exact GlobalTheory.siegel_levels_spread_to_subring | (intros; apply GlobalTheory.siegel_levels_spread_to_subring; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegSpreadCore

theorem spMap_subtype_eq {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) :
    spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem spMap_inclusion_eq {S : Type} [CommRing S] {R₀ R₁ R₂ : Subring S} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) (h : R₀ ≤ R₂) :
    spMap (Subring.inclusion h) = spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem siegPB_spread_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ sE e hd hu
  classical
  obtain ⟨φd, φd₂, hφd, hsd, hwd, hld⟩ := hd
  obtain ⟨φu, φu₂, hφu, hsu, hwu, hlu⟩ := hu
  haveI := d₀.ab.smooth; haveI := d₀.ab.proper; haveI := u.ab.smooth; haveI := u.ab.proper
  have hZ : IsPullback (pullback.lift φu (e.A.hom ≫ spMap R₀.subtype) (by rw [hφu.1.w, Category.assoc]))
      e.A.hom (pullback.snd u.A.hom h₀) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u.A.hom h₀)
    rw [pullback.lift_fst]; exact hφu.1
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.T.baseChange_iso_spreads_to_subring S R₀ e.A.left d₀.A.left (pullback u.A.hom h₀) e.A.hom d₀.A.hom
    (pullback.snd u.A.hom h₀) φd _ hφd.1 hZ
  let R' : Subring S := Subring.closure ((R₀ : Set S) ∪ (F₁ : Set S))
  have hR0 : R₀ ≤ R' := fun x hx => Subring.subset_closure (Or.inl hx)
  have hF1 : (F₁ : Set S) ⊆ R' := fun x hx => Subring.subset_closure (Or.inr hx)
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R₀) (Sp R') s₀
    (spMap (Subring.inclusion hR0) ≫ s₀) (spMap (Subring.inclusion hR0)) d₀ rfl
  have hd'c := hd'
  obtain ⟨φ', φ'₂, hφ', hs', hw', hl'⟩ := hd'
  have eR' := spMap_subtype_eq hR0
  let j : e.A.left ⟶ d'.A.left := hφ'.1.lift φd (e.A.hom ≫ spMap R'.subtype)
    (by rw [hφd.1.w, eR', Category.assoc])
  have hj1 : j ≫ φ' = φd := hφ'.1.lift_fst _ _ _
  have hj2 : j ≫ d'.A.hom = e.A.hom ≫ spMap R'.subtype := hφ'.1.lift_snd _ _ _
  obtain ⟨ψZ, hψZ1, hψZ2⟩ := hF₁ R' hR0 hF1 d'.A.left d'.A.hom φ' j hφ'.1 hj1 hj2
  let ψ := ψZ ≫ pullback.fst u.A.hom h₀
  have hψ : IsPullback ψ d'.A.hom u.A.hom (spMap (Subring.inclusion hR0) ≫ h₀) :=
    hψZ2.paste_horiz (IsPullback.of_hasPullback _ _)
  have hjψ : j ≫ ψ = φu := by
    show j ≫ ψZ ≫ pullback.fst u.A.hom h₀ = φu
    rw [reassoc_of% hψZ1, pullback.lift_fst]
  have eh : spMap R'.subtype ≫ spMap (Subring.inclusion hR0) ≫ h₀ = spMap R₀.subtype ≫ h₀ := by
    rw [← Category.assoc, ← eR']
  have gj : IsGrpPullback e.A d'.A (spMap R'.subtype) j :=
    IsGrpPullback.cancel hφ' (by rw [hj1, ← eR']; exact hφd) hj2
  obtain ⟨j₂, hsj⟩ := GlobalTheory.SiegDesc.exists_isSquare hj2
  have hj₂ : j₂ ≫ φ'₂ = φd₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst d₀.A d₀.A).left = _ ≫ (fst d₀.A d₀.A).left
      rw [Category.assoc, hs'.1, ← Category.assoc, hsj.1, Category.assoc, hj1, hsd.1]
    · show (_ ≫ _) ≫ (snd d₀.A d₀.A).left = _ ≫ (snd d₀.A d₀.A).left
      rw [Category.assoc, hs'.2, ← Category.assoc, hsj.2, Category.assoc, hj1, hsd.2]
  have hwj : LBIso e.P (d'.P.pull j₂) := by
    rw [← hj₂] at hwd
    exact (hwd.trans e.isLB (pull_isLB d₀.isLB _) (pull_isLB (pull_isLB d₀.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull d₀.isLB φ'₂ j₂).symm).trans e.isLB
      (pull_isLB (pull_isLB d₀.isLB _) _) (pull_isLB d'.isLB _) (GlobalTheory.SiegelPullComp.iso_pull j₂ hw').symm
  have hlj : ∀ a, (e.lev a).left ≫ j = spMap R'.subtype ≫ (d'.lev a).left := by
    intro a
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hj1, hld a, Category.assoc, hl' a, ← Category.assoc, ← eR']
    · have a₁ : (e.lev a).left ≫ e.A.hom = 𝟙 _ := Over.w (e.lev a)
      have a₂ : (d'.lev a).left ≫ d'.A.hom = 𝟙 _ := Over.w (d'.lev a)
      rw [Category.assoc, hj2, reassoc_of% a₁, Category.assoc, a₂]
      simp
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ gj (by rw [eh, hjψ]; exact hφu)
  obtain ⟨F₃, hF₃⟩ := GlobalTheory.T.lbIso_spread_alt g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ j₂ φu₂ gj.1 hsj hwj
    (by rw [hjψ]; exact hsu) hwu
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.T.siegel_level_sections_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ hlj
    (fun a => by rw [eh, hjψ]; exact hlu a)
  refine ⟨F₁ ∪ F₂ ∪ F₃ ∪ F₄, fun R₁ hle hF s₁ d₁ hd₁ => ?_⟩
  have hsub : ∀ G : Finset S, G ⊆ F₁ ∪ F₂ ∪ F₃ ∪ F₄ → (G : Set S) ⊆ R₁ :=
    fun G h => (Finset.coe_subset.2 h).trans hF
  have hR'1 : R' ≤ R₁ := Subring.closure_le.2 (Set.union_subset hle
    (hsub F₁ (by intro x; simp only [Finset.mem_union]; tauto)))
  have eR1 := spMap_inclusion_eq hR0 hR'1 hle
  have hd₁' : SiegPB d₁ d' (spMap (Subring.inclusion hR'1)) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd'c (by rw [← eR1]; exact hd₁)
  obtain ⟨φ₁, φ₁₂, hφ₁, hs₁, hw₁, hl₁⟩ := hd₁'
  have gm := hF₂ R₁ hR'1 (hsub F₂ (by intro x; simp only [Finset.mem_union]; tauto)) d₁.A φ₁ hφ₁
  have e2 : spMap (Subring.inclusion hR'1) ≫ spMap (Subring.inclusion hR0) ≫ h₀ =
      spMap (Subring.inclusion hle) ≫ h₀ := by rw [eR1, Category.assoc]
  rw [e2] at gm
  obtain ⟨χ₂, hχ⟩ := GlobalTheory.SiegDesc.exists_isSquare gm.1.w
  refine ⟨φ₁ ≫ ψ, χ₂, gm, hχ, hF₃ R₁ hR'1 (hsub F₃ (by intro x; simp only [Finset.mem_union]; tauto))
    s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁.1 hs₁ hw₁ hχ, fun a => ?_⟩
  have := hF₄ R₁ hR'1 (hsub F₄ (by intro x; simp only [Finset.mem_union]; tauto)) s₁ d₁ φ₁
    (by rw [e2]; exact gm) hl₁ a
  rw [e2] at this
  exact this

end GlobalTheory.SiegSpreadCore
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubringStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  first | exact @GlobalTheory.SiegSpreadCore.siegPB_spread_subring | exact GlobalTheory.SiegSpreadCore.siegPB_spread_subring | (intros; apply GlobalTheory.SiegSpreadCore.siegPB_spread_subring <;> assumption)
end
end

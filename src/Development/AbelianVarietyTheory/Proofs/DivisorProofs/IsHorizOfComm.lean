module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslationStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomOfDerivation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslations

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.LiftComm

theorem appLE_congr {Z X : Scheme.{0}} {k k' : Z ⟶ X} (h : k = k') (U : X.Opens) (V : Z.Opens)
    (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V e' := by
  subst h; rfl

theorem pbT_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens)
    (h : O ≤ f ⁻¹ᵁ O₀) : pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT; rw [dite_eq_left h]

theorem ext_of_opens {Z X : Scheme.{0}} {a b : Z ⟶ X} (hb : a.base = b.base) (O : X.Opens → Z.Opens)
    (hO : ∀ U, O U = b ⁻¹ᵁ U)
    (h : ∀ U (e1 : O U ≤ a ⁻¹ᵁ U) (e2 : O U ≤ b ⁻¹ᵁ U), a.appLE U (O U) e1 = b.appLE U (O U) e2) :
    a = b := by
  refine GlobalTheory.KS.DerMorK.hom_ext_appLE hb fun U e => ?_
  have key : ∀ V (_ : V = O U) (e1 : V ≤ a ⁻¹ᵁ U) (e2 : V ≤ b ⁻¹ᵁ U), a.appLE U V e1 = b.appLE U V e2 := by
    intro V hV e1 e2; subst hV; exact h U e1 e2
  rw [key _ (hO U).symm e le_rfl, Scheme.Hom.appLE_eq_app]

theorem translate_comm : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  intro k _ Y Y' X m π ρ' d Φ hb hΦ T T₀ TY h₀ h₁ h₂ hd
  have hcomp : TY ≫ ρ' ≫ m = ρ' ≫ m ≫ T := by
    rw [← Category.assoc, h₁, Category.assoc, h₀]
  have hbase : (TY ≫ Φ).base = (Φ ≫ T).base := by
    ext y
    have e := congrArg (fun g => g.base y) hcomp
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at e ⊢
    rw [hb, hb, e]
  have hle : ∀ (Z : Scheme.{0}) (V : X.Opens) (g : Z ⟶ Y'), g ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ V ≤ g ⁻¹ᵁ Φ ⁻¹ᵁ V := by
    intro Z V g y hy
    show Φ.base (g.base y) ∈ V
    rw [hb]; exact hy
  refine ext_of_opens hbase (fun W => ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) (fun W => ?_) (fun W e1 e2 => ?_)
  · exact le_antisymm (hle Y' (T ⁻¹ᵁ W) (𝟙 _)) (by
      intro y hy
      show T.base (m.base (ρ'.base y)) ∈ W
      rw [← hb]; exact hy)
  · ext f
    have hO' : ρ' ⁻¹ᵁ m ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ W := hle Y' W (𝟙 _)
    have e' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ TY ⁻¹ᵁ ρ' ⁻¹ᵁ m ⁻¹ᵁ W :=
      le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)
    have e2' : ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W ≤ Φ ⁻¹ᵁ T ⁻¹ᵁ W := hle Y' (T ⁻¹ᵁ W) (𝟙 _)
    have hT0 : m ⁻¹ᵁ T ⁻¹ᵁ W ≤ T₀ ⁻¹ᵁ m ⁻¹ᵁ W := le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) h₀.symm)
    have hL : ((TY ≫ Φ).appLE W _ e1).hom f = (TY.appLE _ _ e').hom ((Φ.appLE W _ hO').hom f) := by
      rw [← Scheme.Hom.appLE_comp_appLE TY Φ W _ _ hO' e']; rfl
    have hR : ((Φ ≫ T).appLE W _ e2).hom f = (Φ.appLE (T ⁻¹ᵁ W) _ e2').hom ((T.app W).hom f) := by
      rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE Φ T W (T ⁻¹ᵁ W) _ le_rfl e2']; rfl
    rw [hL, hR, ← pbT_of_le Φ f _ hO', ← pbT_of_le Φ _ _ e2', hΦ, hΦ, map_add (f := _), map_mul,
      GlobalTheory.KS.DerMorK.appLE_constFn, h₂, hd]
    have a1 : pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = ((ρ' ≫ m).appLE W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom f :=
      pbT_of_le _ _ _ _
    have a2 : pbT ρ' (d W f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) = (ρ'.appLE (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) le_rfl).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a3 : pbT (ρ' ≫ m) ((T.app W).hom f) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        ((ρ' ≫ m).appLE (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom ((T.app W).hom f) :=
      pbT_of_le _ _ _ _
    have a4 : pbT T₀ (d W f) (m ⁻¹ᵁ T ⁻¹ᵁ W) = (T₀.appLE (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) hT0).hom (d W f) :=
      pbT_of_le _ _ _ _
    have a5 : ∀ x : Γ(Y, m ⁻¹ᵁ T ⁻¹ᵁ W), pbT ρ' x (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) =
        (ρ'.appLE (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl).hom x :=
      fun x => pbT_of_le _ _ _ _
    rw [a1, a2, a3, a4, a5]
    congr 1
    · have c1 := Scheme.Hom.appLE_comp_appLE TY (ρ' ≫ m) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE (ρ' ≫ m) T W (T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl le_rfl
      have c3 := appLE_congr (hcomp.trans (Category.assoc _ _ _).symm) W (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_of_eq (congrArg (fun g => g ⁻¹ᵁ W) hcomp.symm)) le_rfl
      rw [Scheme.Hom.app_eq_appLE]
      exact (congr(($c1).hom f)).trans ((congr(($c3).hom f)).trans (congr(($c2).hom f)).symm)
    · congr 1
      have c1 := Scheme.Hom.appLE_comp_appLE TY ρ' (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) le_rfl e'
      have c2 := Scheme.Hom.appLE_comp_appLE ρ' T₀ (m ⁻¹ᵁ W) (m ⁻¹ᵁ T ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W) hT0 le_rfl
      have c3 := appLE_congr h₁ (m ⁻¹ᵁ W) (ρ' ⁻¹ᵁ m ⁻¹ᵁ T ⁻¹ᵁ W)
        (le_trans e' le_rfl) (le_trans le_rfl (ρ'.preimage_mono hT0))
      exact (congr(($c1).hom (d W f))).trans ((congr(($c3).hom (d W f))).trans (congr(($c2).hom (d W f))).symm)

end GlobalTheory.KS.LiftComm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderLiftDerivationCommTranslationsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstOrderLift_derivation_comm_translations : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  first | exact @GlobalTheory.KS.LiftComm.translate_comm | exact GlobalTheory.KS.LiftComm.translate_comm | (intros; apply GlobalTheory.KS.LiftComm.translate_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEq

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TranslPull

theorem transl_comp_of_isGrpPullback : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  intro S S' G' _ G _ f φ h x s hx
  have hu' : ∀ (Y : Over S'), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hu : ∀ (Y : Over S), (toUnit Y).left = Y.hom := fun Y => by
    simpa using Over.w (toUnit Y)
  have hs : s.left ≫ G.hom = 𝟙 S := by simpa using Over.w s
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (G'.hom ≫ f ≫ s.left) (by
    simp [hs])
  let y₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using h.1.w)
  have key := h.2 G' (toUnit G' ≫ x) (𝟙 G') x₀ y₀ (by
      simp [x₀, hu', hx]) (by simp [y₀])
  have e1 : lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G'] = (toUnit G' ≫ x) * 𝟙 G' := rfl
  have e2 : x₀ * y₀ = (Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]) := by
    rw [← Category.assoc, comp_lift, Category.comp_id]
    have hx0 : x₀ = ((Over.homMk φ (by simpa using h.1.w) : Over.mk (G'.hom ≫ f) ⟶ G) ≫ toUnit G) ≫ s := by
      apply Over.OverMorphism.ext
      simp [x₀, hu]
    rw [hx0]
    rfl
  rw [e1, ← key, e2]
  rfl
end GlobalTheory.TranslPull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTranslationCompEqStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.groupPullback_translation_comp_eq : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (x : 𝟙_ (Over S') ⟶ G') (s : 𝟙_ (Over S) ⟶ G), x.left ≫ φ = f ≫ s.left → (lift (toUnit G' ≫ x) (𝟙 G') ≫ μ[G']).left ≫ φ = φ ≫ (lift (toUnit G ≫ s) (𝟙 G) ≫ μ[G]).left := by
  first | exact @GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | exact GlobalTheory.TranslPull.transl_comp_of_isGrpPullback | (intros; apply GlobalTheory.TranslPull.transl_comp_of_isGrpPullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizOfComm

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TranslHoriz

theorem isHoriz_of_comm : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ A.left), IsGrpPullback B' A (spMap ρ) π₁ → IsGrpPullback B' A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (dl : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)), GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → ∀ (s : 𝟙_ (Over (Sp R)) ⟶ A) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left → T₀ ≫ A₀.hom = A₀.hom → (∀ (W : A.left.Opens) (f : Γ(A.left, W)), dl ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W) (((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left.app W).hom f) = pbT T₀ (dl W f) (m₀ ⁻¹ᵁ ((lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left ⁻¹ᵁ W))) → ∀ x : Sp (DualNumber k) ⟶ B'.left, x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ρ ≫ s.left → x ≫ π₂ = spMap (constHom ρ) ≫ s.left := by
  intro k _ R _ A _ hA ρ B' _ π₁ π₂ h₁ h₂ hcl A₀ _ m₀ hm₀ dl hdl s T₀ hT₀ hT₀h hcomm x hx hx1
  set fst := (TrivSqZeroExt.fstHom k k k).toRingHom with hfst
  set alg := algebraMap k (DualNumber k) with halg
  have e_fa : spMap fst ≫ spMap alg = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
  have e_c : spMap (constHom ρ) = spMap alg ≫ spMap (fst.comp ρ) := by
    simp only [spMap, constHom, ← Spec.map_comp]; rfl
  have e_r : spMap (fst.comp ρ) = spMap fst ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have P₁ := h₁.1
  have P₂ := h₂.1
  have P₀ := hm₀.1
  have wr : π₂ ≫ A.hom = (B'.hom ≫ spMap alg) ≫ spMap (fst.comp ρ) := by
    rw [P₂.w, e_c, Category.assoc]
  let r : B'.left ⟶ A₀.left := P₀.lift π₂ (B'.hom ≫ spMap alg) wr
  have hr1 : r ≫ m₀ = π₂ := P₀.lift_fst _ _ _
  have hr2 : r ≫ A₀.hom = B'.hom ≫ spMap alg := P₀.lift_snd _ _ _
  have Pr : IsPullback r B'.hom A₀.hom (spMap alg) := by
    refine IsPullback.of_right ?_ hr2 P₀
    rw [hr1, ← e_c]; exact P₂
  have wj : m₀ ≫ A.hom = (A₀.hom ≫ spMap fst) ≫ spMap (constHom ρ) := by
    rw [P₀.w, Category.assoc, e_c, ← Category.assoc (spMap fst), e_fa, Category.id_comp]
  let j : A₀.left ⟶ B'.left := P₂.lift m₀ (A₀.hom ≫ spMap fst) wj
  have hj1 : j ≫ π₂ = m₀ := P₂.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap fst := P₂.lift_snd _ _ _
  have hjr : j ≫ r = 𝟙 _ := P₀.hom_ext (by rw [Category.assoc, hr1, hj1, Category.id_comp])
    (by rw [Category.assoc, hr2, ← Category.assoc, hj2, Category.assoc, e_fa, Category.comp_id, Category.id_comp])
  have hjπ₁ : j ≫ π₁ = m₀ := by rw [hcl A₀.left j A₀.hom hj2, hj1]
  obtain ⟨-, Pj, -⟩ := GlobalTheory.ConstThickening.structure_dualNumber k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
  have hjs : Surjective j :=
    MorphismProperty.of_isPullback (P := @Surjective) Pj.flip GlobalTheory.ConstThickening.surjective_spMap_fst
  have hm : m₀ ≫ A.hom = A₀.hom ≫ spMap fst ≫ spMap ρ := by rw [P₀.w, e_r]
  obtain ⟨Φ, hΦj, hΦp, hΦ⟩ := GlobalTheory.KS.DerMorK.exists_hom_of_derivation k A₀.left B'.left A₀.hom B'.hom r j Pr hjr hj2
    R ρ A.left A.hom m₀ dl hm hdl
  have hb : ∀ y, Φ y = m₀ (r y) := by
    intro y
    obtain ⟨y₀, rfl⟩ := hjs.surj y
    show (j ≫ Φ) y₀ = (j ≫ r ≫ m₀) y₀
    rw [hΦj, ← Category.assoc, hjr, Category.id_comp]
  have wT : (r ≫ T₀) ≫ A₀.hom = B'.hom ≫ spMap alg := by rw [Category.assoc, hT₀h, hr2]
  let TB : B'.left ⟶ B'.left := Pr.lift (r ≫ T₀) B'.hom wT
  have hTB1 : TB ≫ r = r ≫ T₀ := Pr.lift_fst _ _ _
  have hTB2 : TB ≫ B'.hom = B'.hom := Pr.lift_snd _ _ _
  have hcΦ : TB ≫ Φ = Φ ≫ (lift (toUnit A ≫ s) (𝟙 A) ≫ μ[A]).left :=
    GlobalTheory.T.firstOrderLift_derivation_comm_translations k A₀.left B'.left A.left m₀ B'.hom r dl Φ hb hΦ _ T₀ TB hT₀ hTB1 hTB2 hcomm
  let α : B'.left ⟶ B'.left := P₁.lift Φ B'.hom hΦp
  have hα1 : α ≫ π₁ = Φ := P₁.lift_fst _ _ _
  have hα2 : α ≫ B'.hom = B'.hom := P₁.lift_snd _ _ _
  have hjα : j ≫ α = j := P₁.hom_ext (by rw [Category.assoc, hα1, hΦj, hjπ₁]) (by rw [Category.assoc, hα2])
  let αo : B' ⟶ B' := Over.homMk α hα2
  have hB' : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₁
  set w : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := η[B'] ≫ αo with hw
  have hαo : αo = lift (toUnit B' ≫ w) (𝟙 B') ≫ μ[B'] := GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation k B' hB' αo (fun Z z y hz => by
    change z ≫ α = z
    rw [← Pj.lift_fst z y hz, Category.assoc, hjα])
  let xo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk x hx
  have wσ : (spMap (constHom ρ) ≫ s.left) ≫ A.hom = 𝟙 _ ≫ spMap (constHom ρ) := by
    rw [Category.assoc, Over.w s, Category.id_comp]; rfl
  let σ : Sp (DualNumber k) ⟶ B'.left := P₂.lift (spMap (constHom ρ) ≫ s.left) (𝟙 _) wσ
  have hσ1 : σ ≫ π₂ = spMap (constHom ρ) ≫ s.left := P₂.lift_fst _ _ _
  have hσ2 : σ ≫ B'.hom = 𝟙 _ := P₂.lift_snd _ _ _
  let σo : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B' := Over.homMk σ hσ2
  have tx := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap ρ) π₁ h₁ xo s hx1
  have tσ := GlobalTheory.T.groupPullback_translation_comp_eq B' A (spMap (constHom ρ)) π₂ h₂ σo s hσ1
  have hTBσ : TB = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left := by
    refine P₂.hom_ext ?_ ?_
    · rw [tσ, ← hr1, ← Category.assoc, hTB1, Category.assoc, hT₀, ← Category.assoc]
    · rw [hTB2, Over.w]
  have hcα : αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo := by
    apply Over.OverMorphism.ext
    refine P₁.hom_ext ?_ ?_
    · show α ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']).left ≫ π₁ =
        (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']).left ≫ α ≫ π₁
      rw [tx, ← Category.assoc, hα1, ← hcΦ, hTBσ]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  haveI : IsCommMonObj B' := hB'.comm
  have hτ : ∀ (u y : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B'), y ≫ (lift (toUnit B' ≫ u) (𝟙 B') ≫ μ[B']) = u * y := by
    intro u y
    rw [← Category.assoc, comp_lift, ← Category.assoc, toUnit_unique (y ≫ toUnit B') (𝟙 _), Category.id_comp,
      Category.comp_id, ← Hom.mul_def]
  have h1 : (η[B'] : 𝟙_ _ ⟶ B') = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e1 : η[B'] ≫ αo ≫ (lift (toUnit B' ≫ xo) (𝟙 B') ≫ μ[B']) = xo * w := by
    rw [← Category.assoc, ← hw, hτ]
  have e2 : η[B'] ≫ (lift (toUnit B' ≫ σo) (𝟙 B') ≫ μ[B']) ≫ αo = w * σo := by
    rw [← Category.assoc, hτ, h1, _root_.mul_one]
    nth_rewrite 1 [hαo]
    rw [hτ]
  have key : xo * w = w * σo := by
    rw [← e1, ← e2]
    exact congrArg (η[B'] ≫ ·) hcα
  have hxσ : xo = σo := by
    rw [_root_.mul_comm w σo] at key
    exact _root_.mul_right_cancel key
  have : x = σ := congrArg Over.Hom.left hxσ
  rw [this, hσ1]

end GlobalTheory.TranslHoriz
end
end
end

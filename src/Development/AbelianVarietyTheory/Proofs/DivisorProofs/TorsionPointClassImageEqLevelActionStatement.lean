module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaEqOfMkEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtUnique

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_unique {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ)
    (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (p : (torsion G n).left) (c c' : M) (h : GlobalTheory.TorsSpec.ValAt G n ℓ w p c)
    (h' : GlobalTheory.TorsSpec.ValAt G n ℓ w p c') : c = c' := by
  haveI : Etale (torsion G n).hom := GrpTangent.etale_torsion G hn
  obtain ⟨t, ht, e⟩ := Flat.generalizingMap (torsion G n).hom
    (genericPoint_specializes ((torsion G n).hom p))
  obtain ⟨q, rfl⟩ : t ∈ Set.range ((torsion G n).left.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact ht
  let D := Spec ((torsion G n).left.presheaf.stalk p)
  let y : Sp (AlgebraicClosure (D.residueField q)) ⟶ D :=
    Spec.map (CommRingCat.ofHom (algebraMap (D.residueField q) (AlgebraicClosure (D.residueField q)))) ≫
      D.fromSpecResidueField q
  let g := y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).mpr ⟨ℓ v, Set.mem_univ _, v, rfl⟩
  have hg : Set.range g ⊆ Set.range ℓ := by
    rintro _ ⟨a, rfl⟩
    have hya : y a = q := by
      have : y a ∈ Set.range (D.fromSpecResidueField q) := ⟨_, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have : g a = (torsion G n).hom ((torsion G n).left.fromSpecStalk p (y a)) := rfl
    rw [this, hya, e]
    exact hgen
  let z := IsOpenImmersion.lift ℓ g hg
  have hz : z ≫ ℓ = g := IsOpenImmersion.lift_fac ℓ g hg
  have h1 := h _ y z hz.symm
  have h2 := h' _ y z hz.symm
  exact hun _ z c c' (h1.symm.trans h2)

end GlobalTheory.TorsSpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_torsion_map_of_isGrpPullback {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {f : X' ⟶ X'}
    {φ : G.left ⟶ G.left} (h : IsGrpPullback G G f φ) (hc : (mulN G n).left ≫ φ = φ ≫ (mulN G n).left) :
    ∃ τ : (torsion G n).left ⟶ (torsion G n).left,
      τ ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ φ ∧ τ ≫ (torsion G n).hom = (torsion G n).hom ≫ f := by
  have hP := GrpTangent.isPullback_torsion G n
  have hw : ((torsion.ι G n).left ≫ φ) ≫ (mulN G n).left =
      ((torsion G n).hom ≫ f) ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have e := eta_comp_of_isGrpPullback h
    rw [Category.assoc, ← hc, ← Category.assoc, hP.w]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((torsion G n).hom ≫ ·) e).trans (Category.assoc _ _ _).symm)
  exact ⟨hP.lift _ _ hw, hP.lift_fst _ _ hw, hP.lift_snd _ _ hw⟩

theorem class_move : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).asIso.hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act Γ _ ρ' ρ hρ ι m hm hmv K _ _ t γ P Q PT QT hPT hQT hPQ
    x cP cQ hcP hcQ
  haveI := mono_torsion_ι G n
  have hpb := hm.1 γ
  obtain ⟨τ, hτι, hτh⟩ := exists_torsion_map_of_isGrpPullback G n hpb
    (by rw [← act_natCast act n]; exact hm.2.1 γ _)
  have hPQT : PT ≫ τ = QT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτι, reassoc_of% hPT, hQT, hPQ]
  have hq : τ (PT x) = QT x := by rw [← hPQT, Scheme.Hom.comp_apply]
  have hιh : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  have hval : ValAt G n ℓ w (PT x) ((ι γ).symm cQ) := by
    intro Ω _ _ y z hyz
    rw [← hq] at hcQ
    have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ (x := PT x)
    have h1 := hcQ Ω (y ≫ Spec.map (τ.stalkMap (PT x))) (z ≫ (ρ γ).asIso.hom) (by
      simp only [Category.assoc, reassoc_of% key, hτh, hρ, reassoc_of% hyz])
    simp only [Category.assoc, reassoc_of% key, hτι] at h1
    refine hpb.1.hom_ext ?_ ?_
    · simp only [Category.assoc, hmv, LinearEquiv.apply_symm_apply]
      exact h1
    · simp only [Category.assoc, hw, hιh]
      exact hyz
  rw [valAt_unique G n hn ℓ w hw hun (PT x) cP _ hcP hval, LinearEquiv.apply_symm_apply]

end GlobalTheory.TorsSpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelActionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi


theorem _root_.GlobalTheory.T.torsionPoint_class_image_eq_level_action : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).asIso.hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  first | exact @GlobalTheory.TorsSpec.class_move | exact GlobalTheory.TorsSpec.class_move | (intros; apply GlobalTheory.TorsSpec.class_move <;> assumption)
end
end

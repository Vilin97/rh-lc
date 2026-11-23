module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSectionsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSet
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclic

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem not_acyclic_cechLB_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hc : ⨆ i, D i = ⊤) : ¬ (cechLB f N D).Acyclic := by
  intro hac
  obtain ⟨t, ht⟩ := hT
  let σ : LB.Sec N := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have h0 := hac 0
  rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h0
  let x : (secCube f N D).obj ∅ := SecOnR.of f N _ (GlobalTheory.LB.ofSec σ _)
  have hx : Cube.aug (secCube f N D) x = 0 := h0 ((Cube.d_aug _ _).trans (map_zero _).symm)
  obtain ⟨p⟩ := ‹Nonempty X›
  obtain ⟨i, hi⟩ : ∃ i, p ∈ D i := by
    have hp : p ∈ ⨆ i, D i := by rw [hc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨c, hcp⟩ : ∃ c, p ∈ N.U c := by
    have hp : p ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  have e := congrFun hx ⟨{i}, Finset.card_singleton i⟩
  have e₂ := congrArg (fun y : SecOnR f N (⨅ j ∈ ({i} : Finset κ), D j) => SecOnR.coord y c) e
  have hpW : p ∈ (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c := by
    refine ⟨?_, hcp⟩
    simpa using hi
  have hu : IsUnit (rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c)
      (t.s c).val) := (t.s c).isUnit.map (rs X inf_le_right)
  have e₃ : rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val = 0 := by
    let y : SecOnR f N (⨅ j ∈ (∅ : Finset κ), D j) := x
    have e₄ : rs X (inf_le_inf_right _ (iInf_le_iInf_of_subset D (Finset.empty_subset {i})))
        (SecOnR.coord y c) = 0 := e₂
    have e₅ : SecOnR.coord y c = rs X inf_le_right (t.s c).val := GlobalTheory.LB.coord_ofSec _ _ _
    rw [e₅, rs_rs] at e₄
    exact e₄
  rw [e₃] at hu
  have hu' := hu.map (X.presheaf.germ _ p hpW).hom
  rw [map_zero] at hu'
  exact not_isUnit_zero hu'

end GlobalTheory.CompanionTheory.PointSurjectivity
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclicStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤), ¬ (cechLB f N D).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | exact GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSetStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (F : Set (Sp k ⟶ T)) (hF : F.Finite)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → y ∉ F → FibAc a (G.pull σ))
    (htot : FibAc (p ≫ a) G) (y₀ : Sp k ⟶ T) (σ₀ : X ⟶ Z) (hy : y₀ ≫ b = 𝟙 _) (h₁ : σ₀ ≫ p = 𝟙 X)
    (h₂ : σ₀ ≫ q = a ≫ y₀), ∃ (m : ℕ) (D : Fin m → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ ∧ (cechLB a (G.pull σ₀) D).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.exists_acyclic_cechLB_fibre | exact GlobalTheory.CompanionTheory.PointSurjectivity.exists_acyclic_cechLB_fibre | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.exists_acyclic_cechLB_fibre <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivialStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.picard_group_of_field_trivial : ∀ (k : Type) [Field k] (c : Pic (Sp k)), c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PicField.pic_eq_zero | exact GlobalTheory.CompanionTheory.PicField.pic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PicField.pic_eq_zero <;> assumption)
end
end

-- Source module: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.PointSurj

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CompanionTheory.PointSurjectivity
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

section Lemmas

variable {k : Type} [Field k] {A T : Over (Sp k)} {M : LB (A ⊗ T).left}

theorem pull_evc_const (hM : M.IsLB) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T) {Y : Over (Sp k)} (a : Y ⟶ A) :
    GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) = evc hM a (toUnit Y ≫ t₀) := by
  rw [pull_evc, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem pull_mul_evc_const [GrpObj A] (hM : M.IsLB) (hadd : IsAdditive M) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T)
    {Y : Over (Sp k)} (a a' : Y ⟶ A) :
    GlobalTheory.CechPic.pull (a * a').left (evc hM (𝟙 A) (toUnit A ≫ t₀)) =
      GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) +
        GlobalTheory.CechPic.pull a'.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) := by
  rw [pull_evc_const, pull_evc_const, pull_evc_const]
  exact (isAdditive_iff hM).1 hadd Y a a' _

end Lemmas



theorem pointSurj_pf : (∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic) → PointSurj := by
  intro hAA k _ _ A B _ _ hA hB P hP hadd hadd' hfin M hM haddM
  by_contra hno
  push Not at hno
  have : IsCommMonObj A := hA.comm
  have : IsCommMonObj B := hB.comm
  have hpA : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  have hpB : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have hpq : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have hsw : (swap P).IsLB := pull_isLB hP _
  obtain ⟨G, hG, eG⟩ := cls_surj
    (GlobalTheory.CechPic.pull (lift (fst A B) (toUnit (A ⊗ B))).left (cls M hM) - cls P hP)
  have cst : ∀ {X : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ X) (Y : Over (Sp k)),
      (toUnit Y ≫ x).left = Y.hom ≫ x.left := fun x Y =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit Y)))

  have sl₁ : ∀ y' : 𝟙_ (Over (Sp k)) ⟶ B, cls _ (pull_isLB hG (lift (𝟙 A) (toUnit A ≫ y')).left) =
      evc hM (𝟙 A) (toUnit A ≫ 𝟙 _) - evc hP (𝟙 A) (toUnit A ≫ y') := fun y' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit,
      Category.comp_id]
    rfl

  have sl₂ : ∀ x' : 𝟙_ (Over (Sp k)) ⟶ A, cls _ (pull_isLB hG (lift (toUnit B ≫ x') (𝟙 B)).left) =
      - evc hsw (𝟙 B) (toUnit B ≫ x') := fun x' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit]
    have e₁ : GlobalTheory.CechPic.pull (lift (toUnit B ≫ x') (toUnit B)).left (cls M hM) = 0 := by
      have e := pull_evc hM (toUnit B) x' (𝟙 _)
      rw [Category.comp_id, GlobalTheory.T.picard_group_of_field_trivial k (evc hM x' (𝟙 _)), map_zero] at e
      exact e.symm
    rw [e₁, zero_sub, evc_swap hP hsw]
    rfl
  have fibB : ∀ (y : Sp k ⟶ B.left) (σ : A.left ⟶ (A ⊗ B).left), y ≫ B.hom = 𝟙 _ →
      σ ≫ (fst A B).left = 𝟙 _ → σ ≫ (snd A B).left = A.hom ≫ y → FibAc A.hom (G.pull σ) := by
    intro y σ hy h₁ h₂
    let y' : 𝟙_ (Over (Sp k)) ⟶ B := Over.homMk y hy
    have hσ : σ = (lift (𝟙 A) (toUnit A ≫ y')).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₁, ← Over.comp_left, lift_fst]
        rfl
      · rw [h₂, ← Over.comp_left, lift_snd, cst]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k A hA _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₁ y', map_sub, map_sub, map_sub, pull_mul_evc_const hM haddM, pull_mul_evc_const hP hadd]
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₁ y', sub_eq_zero] at h0
      refine hno y' ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
      have e := congrArg (GlobalTheory.CechPic.pull (fst A (𝟙_ (Over (Sp k)))).left) h0
      rw [pull_evc, pull_evc, Category.comp_id, Category.comp_id,
        ← Category.assoc (fst A _) (toUnit A) y',
        toUnit_unique (fst A (𝟙_ (Over (Sp k))) ≫ toUnit A) (snd A _)] at e
      refine Eq.trans ?_ (e.trans (cls_ev hP _ _ _).symm)
      rw [evc, lift_fst_snd, Over.id_left, pull_id]
  have htot : FibAc ((fst A B).left ≫ A.hom) G :=
    GlobalTheory.T.fibre_acyclicity_of_sections A.hom B.hom (fst A B).left (snd A B).left hpq hpA G hG fibB
  let F' : Set (Sp k ⟶ A.left) :=
    (fun x : 𝟙_ (Over (Sp k)) ⟶ A => x.left) '' {x | Triv (ev P (toUnit B ≫ x) (𝟙 B))}
  have fibA : ∀ (y : Sp k ⟶ A.left) (σ : B.left ⟶ (A ⊗ B).left), y ≫ A.hom = 𝟙 _ →
      σ ≫ (snd A B).left = 𝟙 _ → σ ≫ (fst A B).left = B.hom ≫ y → y ∉ F' → FibAc B.hom (G.pull σ) := by
    intro y σ hy h₁ h₂ hyF
    let x' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk y hy
    have hσ : σ = (lift (toUnit B ≫ x') (𝟙 B)).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₂, ← Over.comp_left, lift_fst, cst]
        rfl
      · rw [h₁, ← Over.comp_left, lift_snd]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k B hB _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₂ x', map_neg, map_neg, map_neg, pull_mul_evc_const hsw hadd']
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₂ x', neg_eq_zero, evc_swap hP hsw] at h0
      exact hyF ⟨x', (triv_ev_iff hP _ _).2 h0, rfl⟩
  have htot' : FibAc ((snd A B).left ≫ B.hom) G := hpq.w ▸ htot
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨m, D, hD, hc, hac⟩ := GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite B.hom A.hom (snd A B).left (fst A B).left hpq.flip hpB G hG F'
    (hfin.image _) fibA htot' η[A].left (lift (toUnit B ≫ η[A]) (𝟙 B)).left hη
    (by rw [← Over.comp_left, lift_snd]; rfl) (by rw [← Over.comp_left, lift_fst, cst])
  have : Nonempty B.left := ⟨η[B].left (IsLocalRing.closedPoint k)⟩
  refine GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic B.hom _ (pull_isLB hG _) ?_ (Fin m) D hc hac
  refine (cls_eq_zero_iff (pull_isLB hG _)).1 ?_
  rw [sl₂, evc_swap hP hsw, ← Hom.one_def, IsAdditive.evc_one hP hadd, neg_zero]

end CompanionTheory.PfDual
end
end

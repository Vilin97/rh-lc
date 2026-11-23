module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedTorusSubgroupWithoutPiTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotient

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.SemiAbAct

theorem exists_torus_quotient_act : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  intro O _ k _ _ G _ act _ T
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := T.isAbelian.proper
  have hmono : Mono T.i := T.isKernel.flip.mono_snd_of_mono
  have hepi : Epi T.q := GlobalTheory.SemiRigid.epi_of_fpqc T.q
  have hA : ∀ a, IsMonHom (act.act a) := act.hom

  have hT : ∀ a, T.i ≫ act.act a ≫ T.q = toUnit _ ≫ η := by
    intro a
    rw [GlobalTheory.SemiRigid.torus_const T.X T.B (T.i ≫ act.act a ≫ T.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  let fT : ∀ a, splitTorus (Sp k) T.X ⟶ splitTorus (Sp k) T.X := fun a ↦
    T.isKernel.lift (T.i ≫ act.act a) (toUnit _) (by rw [Category.assoc, hT])
  have hfT : ∀ a, fT a ≫ T.i = T.i ≫ act.act a := fun a ↦ T.isKernel.lift_fst _ _ _

  have hB : ∀ a, ∃ g, T.q ≫ g = act.act a ≫ T.q := fun a ↦
    GlobalTheory.SemiRigid.exists_desc T.q (act.act a ≫ T.q) fun Z x y h ↦ by
      obtain ⟨τ, hτ⟩ := GlobalTheory.SemiRigid.exists_eq_mul T.isKernel h
      rw [hτ, MonObj.mul_comp_assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hT,
        comp_toUnit_assoc, ← Hom.one_def, _root_.one_mul, Category.assoc]
  choose fB hfB using hB
  have hmulT : ∀ a, IsMonHom (fT a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
        IsMonHom.one_hom]
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hfT]
  have hmulB : ∀ a, IsMonHom (fB a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · have h := IsMonHom.one_hom (f := T.q)
      rw [← h, Category.assoc, hfB, IsMonHom.one_hom_assoc, h]
    · have hqq : Epi (T.q ⊗ₘ T.q) := by
        have : Epi (T.q ▷ G) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (T.q ▷ T.B) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (lift (snd T.B G) (fst T.B G)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd G T.B) (fst G T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have : Epi (lift (snd T.B T.B) (fst T.B T.B)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd T.B T.B) (fst T.B T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have hs : T.B ◁ T.q =
            lift (snd T.B G) (fst T.B G) ≫ (T.q ▷ T.B) ≫ lift (snd T.B T.B) (fst T.B T.B) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [MonoidalCategory.tensorHom_def, hs]
        infer_instance
      rw [← cancel_epi (T.q ⊗ₘ T.q), ← IsMonHom.mul_hom_assoc, hfB, IsMonHom.mul_hom_assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hfB]
  refine ⟨⟨fB, hmulB, ?_, ?_, ?_⟩, ⟨fT, hmulT, ?_, ?_, ?_⟩, hfB, hfT⟩
  · rw [← cancel_epi T.q, hfB, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_epi T.q, hfB, act.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · intro a b
    rw [← cancel_epi T.q, hfB, MonObj.comp_mul, hfB, hfB, act.add, MonObj.mul_comp]
  · rw [← cancel_mono T.i, hfT, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_mono T.i, hfT, act.mul, Category.assoc, hfT, reassoc_of% hfT]
  · intro a b
    rw [← cancel_mono T.i, hfT, MonObj.mul_comp, hfT, hfT, act.add, MonObj.comp_mul]

end GlobalTheory.SemiAbAct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotientStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  first | exact @GlobalTheory.SemiAbAct.exists_torus_quotient_act | exact GlobalTheory.SemiAbAct.exists_torus_quotient_act | (intros; apply GlobalTheory.SemiAbAct.exists_torus_quotient_act <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsAbelianVarietyOfNoPiTorsionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group


theorem _root_.GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (π : 𝓞 E) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → π ≠ 0 → ¬ IsUnit π → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ act.act π = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  first | exact @GlobalTheory.NoPiTorsion.finite_points | exact GlobalTheory.NoPiTorsion.finite_points | (intros; apply GlobalTheory.NoPiTorsion.finite_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsion

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableAbelian

theorem restrict : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (B N : Over (Sp k)) [GrpObj B] [GrpObj N] (act : OAct O B) (ν : N ⟶ B), IsMonHom ν → IsClosedImmersion ν.left → IsReduced N.left → (∀ a : O, Set.range (ν ≫ act.act a).left ⊆ Set.range ν.left) → ∃ act' : OAct O N, ∀ a, act'.act a ≫ ν = ν ≫ act.act a := by
  intro k _ O _ B N _ _ act ν hν hνc hred h
  have : Mono ν := Over.mono_of_mono_left _
  have hl : ∀ a : O, ∃ l : N ⟶ N, l ≫ ν = ν ≫ act.act a := fun a => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (ν ≫ act.act a).left ν.left (h a)
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, Over.comp_left, Category.assoc, (act.act a).w, ν.w]
  choose l hl using hl
  have hm : ∀ a, IsMonHom (l a) := fun a => by
    have := act.hom a
    constructor
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hl]
  refine ⟨⟨l, hm, ?_, ?_, ?_⟩, hl⟩
  · rw [← cancel_mono ν, hl, act.one, Category.id_comp, Category.comp_id]
  · intro a b
    rw [← cancel_mono ν, hl, act.mul, Category.assoc, hl, reassoc_of% (hl a)]
  · intro a b
    rw [← cancel_mono ν, hl, act.add, MonObj.comp_mul, MonObj.mul_comp, hl, hl]

theorem range_comp_subset : ∀ (k : Type) [Field k] (N₀ N : Over (Sp k)) [GrpObj N₀] [GrpObj N] (ν₀ : N₀ ⟶ N) (f : N ⟶ N), IsMonHom ν₀ → IsMonHom f → IsOpenImmersion ν₀.left → IsClosedImmersion ν₀.left → ConnectedSpace N₀.left → Set.range (ν₀ ≫ f).left ⊆ Set.range ν₀.left := by
  intro k _ N₀ N _ _ ν₀ f hν₀ hf ho hc hconn
  haveI := ho
  haveI := hc
  have hcl : IsClopen (Set.range ν₀.left) :=
    ⟨ν₀.left.isClosedEmbedding.isClosed_range, ν₀.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (Set.range (ν₀ ≫ f).left) :=
    isPreconnected_range (ν₀ ≫ f).left.continuous
  let t : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have e2 : η[N₀] ≫ ν₀ ≫ f = η[N₀] ≫ ν₀ := by
    rw [IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have he : (η[N₀] ≫ ν₀ ≫ f).left t ∈ Set.range (ν₀ ≫ f).left ∩ Set.range ν₀.left := by
    refine ⟨⟨η[N₀].left t, rfl⟩, ?_⟩
    rw [e2]
    exact ⟨η[N₀].left t, rfl⟩
  exact hpre.subset_isClopen hcl ⟨_, he⟩

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ B _ act π hB hπ0 hπu C Z hZ hC hstab htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have : Mono ν := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := GlobalTheory.AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have hlift : ∀ x ∈ C, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x := fun x hx => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
      (hr ▸ (hC x).1 hx)
    exact ⟨Over.homMk l (by rw [← ν.w, ← Category.assoc, hl, x.w]), Over.OverMorphism.ext hl⟩
  have hNred : IsReduced N.left := isReduced_of_smooth N.hom
  obtain ⟨actN, hactN⟩ := restrict k (𝓞 E) B N act ν hν hνc hNred fun a => by
    rw [hr]
    refine GlobalTheory.ReducedSubgroup.range_subset_of_points (ν ≫ act.act a) hZ fun x => ?_
    rw [← Category.assoc, ← hC]
    exact hstab a _ (hmem x)
  have : Smooth N₀.hom := SmoothOfRelativeDimension.smooth g N₀.hom
  have hN₀red : IsReduced N₀.left := isReduced_of_smooth N₀.hom
  have hconn : ConnectedSpace N₀.left := GeometricallyConnected.connectedSpace_of_subsingleton N₀.hom
  obtain ⟨act₀, hact₀⟩ := restrict k (𝓞 E) N N₀ actN ν₀ hν₀ hν₀c hN₀red fun a =>
    range_comp_subset k N₀ N ν₀ (actN.act a) hν₀ (actN.hom a) hν₀o hν₀c hconn
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine GlobalTheory.T.finite_points_abelianVariety_of_no_pi_torsion E k N₀ act₀ π g hA hg hπ0 hπu fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      have e : (x ≫ ν₀ ≫ ν) ≫ act.act π = (x ≫ act₀.act π) ≫ ν₀ ≫ ν := by
        simp only [Category.assoc, ← hactN, reassoc_of% (hact₀ π)]
      rw [e, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := GlobalTheory.TorsionDense.finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hlift x hx
  exact ⟨y, Subtype.ext hy⟩

end GlobalTheory.OStableAbelian
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  first | exact @GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | exact GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion | (intros; apply GlobalTheory.OStableAbelian.finite_of_isClosed_of_no_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedStableSubgroupSemiAbelianNoTorsion

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableClosed
open GlobalTheory.RationalPoint

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (π : 𝓞 E), IsSemiAbelian G → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ G _ act π hG hπ hπu C Z hZ hC hstab htor
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  obtain ⟨T⟩ := GlobalTheory.TorsionDense.nonempty_torusExtension G hG
  letI := T.addCommGroup
  letI := T.free
  letI := T.finite
  letI := T.grpB
  haveI := T.q_hom
  haveI := T.i_hom
  haveI := T.isAbelian.proper
  haveI := T.isAbelian.smooth
  haveI := act.hom π
  obtain ⟨actB, actT, hB, hT⟩ := GlobalTheory.T.exists_ringAction_torus_and_abelian_quotient (𝓞 E) k G act hG T
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ T.B) :=
    MonoidHom.mk' (fun x => x ≫ T.q) fun x y => MonObj.mul_comp x y T.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ T.i) fun x y => MonObj.mul_comp x y T.i
  let m : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ act.act π) fun x y => MonObj.mul_comp x y _
  have hj : Function.Injective j := fun x y hxy =>
    T.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨T.isKernel.lift x (toUnit _) hx, T.isKernel.lift_fst _ _ _⟩
  have hTf : Finite (C.comap j) := by
    refine GlobalTheory.T.finite_closed_torus_subgroup_without_pi_torsion E k T.X actT π hπ hπu _ (T.i.left ⁻¹' Z)
      (hZ.preimage T.i.left.continuous) (fun x => ?_) (fun a x hx => ?_) (fun x hx h1 => ?_)
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · rw [Subgroup.mem_comap] at hx ⊢
      change (x ≫ actT.act a) ≫ T.i ∈ C
      rw [Category.assoc, hT a, ← Category.assoc]
      exact hstab a _ hx
    · apply hj
      rw [map_one]
      refine htor _ hx ?_
      change (x ≫ T.i) ≫ act.act π = 1
      rw [Category.assoc, ← hT π, ← Category.assoc, h1, MonObj.one_comp]
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ T.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G T.B T.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine GlobalTheory.T.finite_closed_ringStable_subgroup_abelian_no_torsion E k T.B actB π T.isAbelian hπ hπu _ Z' hZ' (fun y => ?_) (fun a y hy => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · obtain ⟨x, rfl⟩ := hy
      refine ⟨⟨x.1 ≫ act.act a, hstab a _ x.2⟩, ?_⟩
      change (x.1 ≫ act.act a) ≫ T.q = (x.1 ≫ T.q) ≫ actB.act a
      rw [Category.assoc, Category.assoc, hB]
    · rintro _ ⟨y, rfl⟩ hy
      have hmC : ∀ z : C, m z.1 ∈ C := fun z => hstab π _ z.2
      have hmK : ∀ z : ψ.ker, ψ ⟨m z.1.1, hmC z.1⟩ = 1 := fun z => by
        change (z.1.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        change ψ z.1 ≫ actB.act π = 1
        rw [MonoidHom.mem_ker.1 z.2]
        haveI := actB.hom π
        exact MonObj.one_comp _
      let f : ψ.ker → ψ.ker := fun z => ⟨⟨m z.1.1, hmC z.1⟩, hmK z⟩
      have hf : Function.Injective f := fun z₁ z₂ h => by
        have h1 : m z₁.1.1 = m z₂.1.1 := congrArg (fun z : ψ.ker => z.1.1) h
        have h2 : z₁.1.1 / z₂.1.1 = 1 := htor _ (C.div_mem z₁.1.2 z₂.1.2) (by
          change m (z₁.1.1 / z₂.1.1) = 1
          rw [map_div, h1, div_self'])
        exact Subtype.ext (Subtype.ext (div_eq_one.1 h2))
      have hw : ψ ⟨m y.1, hmC y⟩ = 1 := by
        change (y.1 ≫ act.act π) ≫ T.q = 1
        rw [Category.assoc, ← hB π, ← Category.assoc]
        exact hy
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hf) ⟨⟨m y.1, hmC y⟩, hw⟩
      have h1 : m z.1.1 = m y.1 := congrArg (fun z : ψ.ker => z.1.1) hz
      have h2 : y.1 / z.1.1 = 1 := htor _ (C.div_mem y.2 z.1.2) (by
        change m (y.1 / z.1.1) = 1
        rw [map_div, h1, div_self'])
      have h3 : y = z.1 := Subtype.ext (div_eq_one.1 h2)
      rw [h3]
      exact z.2
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory.OStableClosed
end
end

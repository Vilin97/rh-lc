module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtAbelianVarietyHomDescent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HomFinExt

open GlobalTheory.Spread GlobalTheory.HomExtNormal

theorem exists_finite_hom : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap ga)).obj A ⟶ (Over.pullback (spMap ga)).obj A', IsMonHom f → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (f' : (Over.pullback (spMap io)).obj A ⟶ (Over.pullback (spMap io)).obj A'), io.Finite ∧ l.comp io = j.comp ga ∧ IsMonHom f' ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A.hom (spMap ga)) (p' : Z ⟶ pullback A.hom (spMap io)) (t : Z ⟶ Sp Ω'), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.left ≫ pullback.fst _ _ = p' ≫ f'.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ ga A A' _ _ hA hA' f hf
  haveI := hf
  have := hA.proper
  have := hA'.proper
  have := hA.smooth
  have := hA'.smooth
  let Ωb := AlgebraicClosure Ω
  let j : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (j.comp ga).toAlgebra
  let Kb := algebraicClosure K Ωb
  have hcomp : spMap j ≫ spMap ga = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨f₁, hf₁, e₁⟩ := exists_pull_hom (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp f
  obtain ⟨g, hg, eg⟩ := GlobalTheory.T.exists_mon_hom_over_algebraic_closure K Ωb A A' hA hA' f₁ hf₁
  obtain ⟨s, hs⟩ := GlobalTheory.HomPairDescent.exists_descend (K := K) (Ω := Kb) A A' g
  let L : IntermediateField K Kb := IntermediateField.adjoin K (s : Set Kb)
  obtain ⟨g', hg'⟩ := hs L (IntermediateField.subset_adjoin _ _)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A L.val
  have gB := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A' L.val
  obtain ⟨-, hmon⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff L Kb L.val.toRingHom
  have hg'm : IsMonHom g' := (hmon _ _ _ _ _ _ g' g gA gB hg').1 hg
  let l : L →+* Ωb := Kb.val.toRingHom.comp L.val.toRingHom
  refine ⟨L, inferInstance, algebraMap K L, Ωb, inferInstance, j, l, g', RingHom.finite_algebraMap.mpr hfin,
    ?_, hg'm, ?_⟩
  · ext x
    change Kb.val (L.val (algebraMap K L x)) = algebraMap K Ωb x
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro Z p p' t h1 h2 h3
    have hP : (p ≫ pullback.fst _ _) ≫ A.hom = t ≫ spMap (algebraMap K Ωb) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h2, Category.assoc, hcomp]
    let P : Z ⟶ pullback A.hom (spMap (algebraMap K Ωb)) := pullback.lift (p ≫ pullback.fst _ _) t hP
    have hPp : P ≫ pullMap (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp A = p := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, pullback.lift_fst]
      · rw [Category.assoc, pullMap_snd, pullback.lift_snd_assoc, h2]
    have hQ : (P ≫ bcMap A.hom Kb.val) ≫ bcMap A.hom L.val = p' := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, bcMap_fst, pullback.lift_fst, h1]
      · rw [Category.assoc, bcMap_snd, Category.assoc, bcMap_snd_assoc, pullback.lift_snd_assoc, h3]
        rw [← Spec.map_comp]; rfl
    calc p ≫ f.left ≫ pullback.fst _ _
        = P ≫ f₁.left ≫ pullback.fst _ _ := by rw [e₁, ← hPp, Category.assoc]
      _ = P ≫ bcMap A.hom Kb.val ≫ g.left ≫ pullback.fst _ _ := by rw [eg]
      _ = p' ≫ g'.left ≫ pullback.fst _ _ := by
        rw [← hQ, Category.assoc, Category.assoc, ← Category.assoc (bcMap A.hom L.val), hg', Category.assoc,
          bcMap_fst]

end GlobalTheory.HomFinExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtAbelianVarietyHomDescentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap ga)).obj A ⟶ (Over.pullback (spMap ga)).obj A', IsMonHom f → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (f' : (Over.pullback (spMap io)).obj A ⟶ (Over.pullback (spMap io)).obj A'), io.Finite ∧ l.comp io = j.comp ga ∧ IsMonHom f' ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A.hom (spMap ga)) (p' : Z ⟶ pullback A.hom (spMap io)) (t : Z ⟶ Sp Ω'), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.left ≫ pullback.fst _ _ = p' ≫ f'.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.HomFinExt.exists_finite_hom | exact GlobalTheory.HomFinExt.exists_finite_hom | (intros; apply GlobalTheory.HomFinExt.exists_finite_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.IsoFinExt

theorem isPullback_compare {X S L S' T : Scheme.{0}} (a : X ⟶ S) (b : L ⟶ S) (i : S' ⟶ S) (j : T ⟶ L)
    (l : T ⟶ S') (hc : l ≫ i = j ≫ b) :
    ∃ q : pullback (pullback.snd a b) j ⟶ pullback a i,
      q ≫ pullback.fst a i = pullback.fst _ _ ≫ pullback.fst a b ∧
      IsPullback q (pullback.snd _ _) (pullback.snd a i) l := by
  have hw : (pullback.fst (pullback.snd a b) j ≫ pullback.fst a b) ≫ a = (pullback.snd _ _ ≫ l) ≫ i := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc, hc]
  refine ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a i)
  rw [pullback.lift_fst, hc]
  exact (IsPullback.of_hasPullback (pullback.snd a b) j).paste_horiz (IsPullback.of_hasPullback a b)

theorem isIso_of_compare {X₁ X₂ S L S' T : Scheme.{0}} (a₁ : X₁ ⟶ S) (a₂ : X₂ ⟶ S) (b : L ⟶ S) (i : S' ⟶ S)
    (j : T ⟶ L) (l : T ⟶ S') [Surjective l] [Flat l] [QuasiCompact l] (hc : l ≫ i = j ≫ b)
    (f : pullback a₁ b ⟶ pullback a₂ b) [IsIso f] (hf : f ≫ pullback.snd _ _ = pullback.snd _ _)
    (f' : pullback a₁ i ⟶ pullback a₂ i) (hf' : f' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback a₁ b) (p' : Z ⟶ pullback a₁ i) (t : Z ⟶ T),
      p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ j →
      p' ≫ pullback.snd _ _ = t ≫ l → p ≫ f ≫ pullback.fst _ _ = p' ≫ f' ≫ pullback.fst _ _) :
    IsIso f' := by
  obtain ⟨q₁, e₁, H₁⟩ := isPullback_compare a₁ b i j l hc
  obtain ⟨q₂, e₂, H₂⟩ := isPullback_compare a₂ b i j l hc
  let F : pullback (pullback.snd a₁ b) j ⟶ pullback (pullback.snd a₂ b) j :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hF₁ : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := pullback.lift_fst _ _ _
  have hF₂ : F ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hw : q₁ ≫ f' = F ≫ q₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, e₂, ← Category.assoc F, hF₁, Category.assoc]
      exact (h _ _ q₁ _ e₁.symm pullback.condition H₁.w).symm
    · rw [Category.assoc, Category.assoc, hf', H₂.w, ← Category.assoc, hF₂, H₁.w]
  have H : IsPullback q₁ F f' q₂ := by
    refine IsPullback.of_bot ?_ hw H₂
    rw [hF₂, hf']
    exact H₁
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q₂ :=
    ⟨⟨MorphismProperty.of_isPullback H₂.flip ‹Surjective l›,
      MorphismProperty.of_isPullback H₂.flip ‹Flat l›⟩,
      MorphismProperty.of_isPullback H₂.flip ‹QuasiCompact l›⟩
  have hF : IsIso F := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
    H.flip hq hF

theorem exists_finite_iso : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  intro K L _ _ _ β A₁ A₂ _ _ h₁ h₂ f hf
  obtain ⟨K', _, io, Ω, _, j, l, f', hfin, hc, hm, h⟩ := GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent K L β A₁ A₂ h₁ h₂ f.hom hf
  have hc' : spMap l ≫ spMap io = spMap j ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have : Flat (spMap l) := by
    rw [Flat.SpecMap_iff]
    letI := l.toAlgebra
    exact (inferInstance : Module.Flat K' Ω)
  have : Surjective (spMap l) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hl : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have : IsIso f'.left :=
    @isIso_of_compare _ _ _ _ _ _ A₁.hom A₂.hom (spMap β) (spMap io) (spMap j) (spMap l) _ _ _ hc'
      f.hom.left hl (Over.w f.hom) f'.left (Over.w f') h
  have : IsIso ((Over.forget _).map f') := this
  have : IsIso f' := isIso_of_reflects_iso f' (Over.forget _)
  exact ⟨K', inferInstance, io, Ω, inferInstance, j, l, asIso f', hfin, hc, hm, h⟩

end GlobalTheory.IsoFinExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ


theorem _root_.GlobalTheory.T.isomorphism_mon_hom_descends_finite_extension : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.IsoFinExt.exists_finite_iso | exact GlobalTheory.IsoFinExt.exists_finite_iso | (intros; apply GlobalTheory.IsoFinExt.exists_finite_iso <;> assumption)
end
end

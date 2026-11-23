module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FiniteType
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Ring.FinitePresentation
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeIntHomFilteredColimit

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem finiteType_int_hom_filteredColimit :
    ∀ (A : CommRingCat.{0}), Algebra.FiniteType ℤ A → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
      (∀ φ : A ⟶ c.pt, ∃ (j : J) (ψ : A ⟶ D.obj j), ψ ≫ c.ι.app j = φ) ∧
      ∀ (j : J) (ψ ψ' : A ⟶ D.obj j), ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j →
        ∃ (k : J) (f : j ⟶ k), ψ ≫ D.map f = ψ' ≫ D.map f := by
  intro A hA J _ _ D c hc
  let R : CommRingCat.{0} := CommRingCat.of ℤ
  let f : R ⟶ A := CommRingCat.ofHom (Int.castRingHom A)
  let α : (Functor.const J).obj R ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom (D.obj i))
      naturality := by
        intro i j g
        ext1
        exact RingHom.ext_int _ _ }
  have hfp : f.hom.FinitePresentation := by
    have h1 : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp hA
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FinitePresentation
    rw [e]
    exact h1
  have hft : f.hom.FiniteType := by
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FiniteType
    rw [e]
    exact hA
  have hR : ∀ {X : CommRingCat.{0}} (u v : R ⟶ X), u = v := by
    intro X u v
    ext1
    exact RingHom.ext_int _ _
  refine ⟨fun φ => ?_, fun j ψ ψ' h => ?_⟩
  · obtain ⟨i, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R D α f c hc
      hfp φ (fun i => hR _ _)
    exact ⟨i, g', hg'.symm⟩
  · obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R D α f c hc
      hft.essFiniteType ψ (hR _ _) ψ' (hR _ _) h
    refine ⟨IsFiltered.coeq hik hjk, hik ≫ IsFiltered.coeqHom hik hjk, ?_⟩
    calc ψ ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk)
        = (ψ ≫ D.map hik) ≫ D.map (IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = (ψ' ≫ D.map hjk) ≫ D.map (IsFiltered.coeqHom hik hjk) := by rw [e]
      _ = ψ' ≫ D.map (hjk ≫ IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = ψ' ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk) := by
          rw [IsFiltered.coeq_condition]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteType

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FinExt

def finTypeZ : ObjectProperty CommRingCat.{0} := fun A => Algebra.FiniteType ℤ A

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  (E : finTypeZ.ι.LeftExtension G)

lemma comp_eq_of_fac {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
    {c : Cocone D} (hc : IsColimit c) (s : Cocone (D ⋙ E.right))
    (X : finTypeZ.FullSubcategory) {j j' : J} (ψ : finTypeZ.ι.obj X ⟶ D.obj j)
    (ψ' : finTypeZ.ι.obj X ⟶ D.obj j') (h : ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j') :
    E.hom.app X ≫ E.right.map ψ ≫ s.ι.app j = E.hom.app X ≫ E.right.map ψ' ≫ s.ι.app j' := by
  obtain ⟨k, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  have hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k := by
    simpa only [Category.assoc, Cocone.w] using h
  obtain ⟨l, f, hf⟩ := (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk
  have e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l := (s.w (a ≫ f)).symm
  have e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l := (s.w (b ≫ f)).symm
  rw [e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 3
  simpa only [Functor.map_comp, Category.assoc] using hf

end

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  {E : finTypeZ.ι.LeftExtension G}

theorem preservesFilteredColimits_of_isPointwiseLeftKanExtension
    (hE : E.IsPointwiseLeftKanExtension) : PreservesFilteredColimitsOfSize.{0, 0} E.right := by
  refine ⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hfac := fun (g : CostructuredArrow finTypeZ.ι c.pt) =>
    (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom
  choose j ψ hψ using hfac
  let t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G) :=
    fun s =>
    { pt := s.pt
      ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g)
             naturality := by
               intro g g' f
               have hn := E.hom.naturality f.left
               dsimp at hn ⊢
               simp only [Category.comp_id]
               change G.map f.left ≫ _ = _
               erw [reassoc_of% hn, ← Functor.map_comp_assoc]
               exact comp_eq_of_fac E hc s g.left _ _
                 (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }
  have ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt),
      E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) =
        E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ)) := by
    intro s X φ
    have := (hE c.pt).fac (t s) (CostructuredArrow.mk φ)
    exact (Category.assoc _ _ _).symm.trans this
  exact
  { desc := fun s => (hE c.pt).desc (t s)
    fac := fun s k => by
      apply (hE (D.obj k)).hom_ext'
      intro X φ
      have h1 := ht s X (φ ≫ c.ι.app k)
      simp only [Functor.mapCocone_ι_app]
      erw [← Functor.map_comp_assoc, h1]
      exact comp_eq_of_fac E hc s X _ _ (hψ _)
    uniq := fun s m hm => by
      apply (hE c.pt).hom_ext'
      intro X φ
      rw [ht s X φ]
      have h2 := hψ (CostructuredArrow.mk φ)
      dsimp at h2
      conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]
      have h3 := hm (j (CostructuredArrow.mk φ))
      simp only [Functor.mapCocone_ι_app] at h3
      rw [h3] }

end

theorem exists_preservesFilteredColimits_isIso :
    ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜),
      ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧
        (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) := by
  intro 𝒜 _ _ M
  haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜
  haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance
  let E := Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))
  have hE : E.IsPointwiseLeftKanExtension :=
    finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _
  let φ := hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))
  refine ⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE,
    fun A hA => ?_⟩
  let X : finTypeZ.FullSubcategory := ⟨A, hA⟩
  have h1 : IsIso (E.hom.app X) := (hE (finTypeZ.ι.obj X)).isIso_hom_app
  have h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _ := by
    have := congr_app (StructuredArrow.w φ) X
    simpa using this
  have h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X)) := by
    rw [h2]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  exact IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))

end GlobalTheory.FinExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
end
end

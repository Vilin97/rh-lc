module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGroupSectionsDenseInFibresStatement
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoveNear

theorem exists_section_translate_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π G' _ _ _ N e he hPt Ω _ s g hT hs
  haveI := N.isOpen
  haveI := hR.1
  let xR := s ≫ π
  let UΩ := pullback N.U.hom xR
  let T := pullback G'.hom s
  let m : UΩ ⟶ pullback N.U.hom π := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [Category.assoc]; exact pullback.condition)
  let k : UΩ ⟶ T := pullback.lift (m ≫ N.u) (pullback.snd _ _)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd])
  have sqP : IsPullback m (pullback.snd N.U.hom xR) (pullback.snd N.U.hom π) s := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback N.U.hom π)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback N.U.hom xR
  have sqk : IsPullback m k N.u (pullback.fst G'.hom s) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G'.hom s) (v₂₂ := G'.hom) (h₃₁ := s) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback G'.hom s)
    rw [pullback.lift_snd, N.u_over]
    exact sqP
  have hk : IsOpenImmersion k := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqk N.isOpen
  let TO : Over S := Over.mk (pullback.snd G'.hom s ≫ s)
  let yT : TO ⟶ G' := Over.homMk (pullback.fst G'.hom s) pullback.condition
  let qT : TO ⟶ Over.mk s := Over.homMk (pullback.snd G'.hom s) rfl
  let zT : TO ⟶ G' := (qT ≫ g) * yT
  let UO : Over S := Over.mk (pullback.snd N.U.hom xR ≫ s)
  let kO : UO ⟶ TO := Over.homMk k (by
    change k ≫ pullback.snd _ _ ≫ s = _
    rw [pullback.lift_snd_assoc]
    rfl)
  have sec : ∀ h : Over.mk s ⟶ G', ∃ σ : Over.mk s ⟶ TO, σ ≫ yT = h ∧ σ ≫ qT = 𝟙 _ := fun h =>
    ⟨Over.homMk (pullback.lift h.left (𝟙 _) ((Over.w h).trans (Category.id_comp _).symm))
      (by
        change pullback.lift _ _ _ ≫ pullback.snd G'.hom s ≫ s = s
        rw [pullback.lift_snd_assoc]
        exact Category.id_comp _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
  have hone : ∀ p, (1 : Over.mk s ⟶ G').left p ∈ Set.range N.u := by
    obtain ⟨x₀, -, -, hx₀⟩ := hPt
    have e₁ : (1 : Over.mk s ⟶ G').left = s ≫ (1 : Over.mk (𝟙 S) ⟶ G').left := congrArg (fun f => f.left)
      (MonObj.comp_one (M := G') (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))).symm
    intro p
    rw [e₁, ← hx₀]
    exact ⟨x₀ (s p), rfl⟩
  have hoU : IsOpen (Set.range N.u) := N.u.isOpenEmbedding.isOpen_range
  obtain ⟨σ₁, h₁, -⟩ := sec 1
  obtain ⟨σ₂, h₂, h₂'⟩ := sec g⁻¹
  have e₂ : σ₂ ≫ zT = 1 := by
    rw [MonObj.comp_mul, h₂, ← Category.assoc, h₂', Category.id_comp, mul_inv_cancel]
  have : IrreducibleSpace T := hT
  obtain ⟨t, ⟨p₀, hp₀⟩, ht⟩ := nonempty_preirreducible_inter (hoU.preimage (pullback.fst G'.hom s).continuous)
    (hoU.preimage zT.left.continuous)
    ⟨σ₁.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← h₁] at this
      exact this⟩
    ⟨σ₂.left (IsLocalRing.closedPoint _), by
      have := hone (IsLocalRing.closedPoint _)
      rw [← e₂] at this
      exact this⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback sqk p₀ t hp₀
  let O : UΩ.Opens := ⟨(kO ≫ zT).left ⁻¹' Set.range N.u, hoU.preimage (kO ≫ zT).left.continuous⟩
  have hwO : w ∈ O := by
    show (kO ≫ zT).left w ∈ Set.range N.u
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    change zT.left (k w) ∈ Set.range N.u
    rw [hw]; exact ht
  have hirr : IrreducibleSpace UΩ := by
    refine (irreducibleSpace_def _).2 ⟨⟨w, trivial⟩, ?_⟩
    have := (IrreducibleSpace.isIrreducible_univ T).2.preimage k.isOpenEmbedding
    simpa using this
  obtain ⟨a, aΩ, ha, haf, has, hao⟩ := GlobalTheory.T.smoothGroup_sections_dense_in_fibres R hR.2.2.2 N.U N.smooth e he Ω xR hs hirr O ⟨w, hwO⟩
  let x : Over.mk (𝟙 S) ⟶ G' := Over.homMk
    (pullback.lift (π ≫ a) (𝟙 S) (by rw [Category.assoc, ha, Category.comp_id]; exact (Category.id_comp π).symm) ≫ N.u)
    (by rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
  refine ⟨a, x, ha, ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ?_⟩
  let rO : Over.mk s ⟶ UO := Over.homMk aΩ (by
    change aΩ ≫ pullback.snd _ _ ≫ s = s
    rw [← Category.assoc, has, Category.id_comp])
  have hq : rO ≫ kO ≫ qT = 𝟙 _ := by
    ext
    change aΩ ≫ k ≫ pullback.snd _ _ = 𝟙 _
    rw [pullback.lift_snd, has]
  have hy : rO ≫ kO ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
    ext
    change aΩ ≫ k ≫ pullback.fst _ _ = s ≫ pullback.lift (π ≫ a) (𝟙 S) _ ≫ N.u
    rw [pullback.lift_fst, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      show aΩ ≫ pullback.lift (pullback.fst N.U.hom xR) _ _ ≫ pullback.fst N.U.hom π = s ≫ π ≫ a
      rw [pullback.lift_fst, haf]
      simp only [xR, Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, has,
        Category.id_comp, Category.comp_id]
  have hz : g * ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x) = rO ≫ kO ≫ zT := by
    have hq' : (rO ≫ kO) ≫ qT = 𝟙 _ := by rw [Category.assoc]; exact hq
    have hy' : (rO ≫ kO) ≫ yT = (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x := by
      rw [Category.assoc]; exact hy
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, hq', Category.id_comp, hy']
  rintro _ ⟨p, rfl⟩
  rw [hz]
  exact hao ⟨p, rfl⟩

end GlobalTheory.MoveNear
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_section_translate_mem_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (N : Near π G') (e : Sp R ⟶ N.U.left), e ≫ N.U.hom = 𝟙 _ → N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left → ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), IrreducibleSpace (pullback G'.hom s : Scheme.{0}) → closedPoint R ∉ Set.range (s ≫ π) → ∃ (a : Sp R ⟶ N.U.left) (x : Over.mk (𝟙 S) ⟶ G'), a ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a) x.left ∧ Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.MoveNear.exists_section_translate_mem | exact GlobalTheory.MoveNear.exists_section_translate_mem | (intros; apply GlobalTheory.MoveNear.exists_section_translate_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  rw [← Category.assoc, hφ1, one_left_pullback] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.unitSection_near_closedFibre_descends_to_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  first | exact @GlobalTheory.UnitDescent.unit_descends | exact GlobalTheory.UnitDescent.unit_descends | (intros; apply GlobalTheory.UnitDescent.unit_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_sec_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)
    (g : Over.mk s ⟶ G) (x : Over.mk (𝟙 S) ⟶ G) :
    (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left = g.left ≫ (transl x).left := by
  have h2 : g ≫ (Over.homMk G.hom (by simp) : G ⟶ Over.mk (𝟙 S)) = Over.homMk s (by simp) := by
    ext; exact Over.w g
  rw [← Over.comp_left, transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, h2]

theorem irreducibleSpace_fibre_of_semiAbelian {S : Scheme.{0}} (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G')
    (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) : IrreducibleSpace (pullback G'.hom s : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback G'.hom s : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) s _ _ (IsPullback.of_hasPullback G'.hom s)
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace Ω _ (pullback.snd G'.hom s) inferInstance hc

theorem range_one_subset_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (hπ : IsProper π)
    (G' : Over S) [GrpObj G'] (N : Near π G') :
    Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u := by
  have hW : IsOpen ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u) :=
    N.isOpen.isOpen_range.preimage (1 : Over.mk (𝟙 S) ⟶ G').left.continuous
  have hcl : IsClosed (π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ) :=
    π.isClosedMap _ hW.isClosed_compl
  have hover : ∀ z : S, G'.hom ((1 : Over.mk (𝟙 S) ⟶ G').left z) = z := fun z => by
    have := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
    change ((1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom) z = z
    rw [this]; rfl
  rintro _ ⟨z, rfl⟩
  by_contra hz
  have hmem : π z ∈ π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwc⟩ := (IsLocalRing.specializes_closedPoint (π z)).mem_closed hcl hmem
  apply hw
  apply N.all
  rw [hover]; exact hwc

theorem cover_by_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π hπ hs hS G' _ _ hG N hL
  obtain ⟨e, he, hPe⟩ := GlobalTheory.T.unitSection_near_closedFibre_descends_to_base R hR S π hπ hs hS G' hG N hL (range_one_subset_near π hπ G' N)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  let Idx := {ax : (Sp R ⟶ N.U.left) × (Over.mk (𝟙 S) ⟶ G') // ax.1 ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ ax.1) ax.2.left}
  let V : Idx → Set G'.left := fun i => Set.range N.u ∪ (transl i.1.2).left ⁻¹' Set.range N.u
  have hopen : IsOpen (Set.range N.u) := N.isOpen.isOpen_range
  have hV : ∀ i, IsOpen (V i) := fun i => hopen.union (hopen.preimage (transl _).left.continuous)
  have hcov : Set.univ ⊆ ⋃ i, V i := by
    intro p _
    by_cases hp : p ∈ Set.range N.u
    · exact Set.mem_iUnion.2 ⟨⟨(e, 1), he, hPe⟩, Or.inl hp⟩
    · have hfp : (G'.left.fromSpecResidueField p) (closedPoint _) = p := G'.left.fromSpecResidueField_apply p _
      have hnc : closedPoint R ∉ Set.range (G'.left.fromSpecResidueField p ≫ G'.hom ≫ π) := by
        rintro ⟨y, hy⟩
        apply hp
        apply N.all
        rw [← hy, Subsingleton.elim y (closedPoint _)]
        change π (G'.hom p) = π (G'.hom ((G'.left.fromSpecResidueField p) _))
        rw [hfp]
      obtain ⟨a, x, ha, hPa, hr⟩ := GlobalTheory.T.exists_section_translate_mem_near_closedFibre R hR S π G' hG N e he hPe (G'.left.residueField p)
        (G'.left.fromSpecResidueField p ≫ G'.hom) (Over.homMk (G'.left.fromSpecResidueField p) rfl)
        (irreducibleSpace_fibre_of_semiAbelian G' hG _ _) (by simpa [Category.assoc] using hnc)
      rw [mul_sec_left_eq] at hr
      refine Set.mem_iUnion.2 ⟨⟨(a, x), ha, hPa⟩, Or.inr ?_⟩
      have := hr ⟨closedPoint _, rfl⟩
      change (transl x).left ((G'.left.fromSpecResidueField p) (closedPoint _)) ∈ _ at this
      rwa [hfp] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcov
  refine ⟨t.card, fun k => (t.equivFin.symm k).1.1.1, fun k => (t.equivFin.symm k).1.1.2,
    fun k => (t.equivFin.symm k).1.2, ?_⟩
  intro Ω _ s g
  have hpt : ∀ y : Sp Ω, y = closedPoint Ω := fun y => Subsingleton.elim _ _
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (g.left (closedPoint Ω))))
  rcases hi with hi | hi
  · left
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi
  · right
    refine ⟨t.equivFin ⟨i, hit⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [mul_sec_left_eq]
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionTranslatesCoverSemiAbelianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_section_translates_cover_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  first | exact @GlobalTheory.Mum.cover_by_translates | exact GlobalTheory.Mum.cover_by_translates | (intros; apply GlobalTheory.Mum.cover_by_translates <;> assumption)
end
end

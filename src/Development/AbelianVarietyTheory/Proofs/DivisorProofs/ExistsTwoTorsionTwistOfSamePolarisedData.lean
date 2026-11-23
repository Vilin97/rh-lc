module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarised

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.SamePolIso
variable {R : Type} [CommRing R] [IsDomain R]

theorem grp_iso {B Q : Over (Sp R)} [GrpObj B] [GrpObj Q] {β : B.left ⟶ Q.left}
    (h : IsGrpPullback B Q (spMap (RingHom.id R)) β) : ∃ f : B ≅ Q, f.hom.left = β ∧ IsMonHom f.hom := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have h1 := h.1
  rw [hs] at h1
  have : IsIso β := h1.isIso_fst_of_isIso
  let f : B ⟶ Q := Over.homMk β (by simpa using h1.w)
  have : IsIso ((Over.forget (Sp R)).map f) := (inferInstance : IsIso β)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  refine ⟨asIso f, rfl, isMonHom_of_mul _ fun T x y => ?_⟩
  let ρ : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have e := h.2 T x y (ρ ≫ x ≫ f) (ρ ≫ y ≫ f) (by simp [ρ, f]) (by simp [ρ, f])
  apply Over.OverMorphism.ext
  rw [← MonObj.comp_mul] at e
  simpa [ρ, f] using e.symm

theorem gw_congr {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {f f' : Y ⟶ X'} (hf : f = f') (y : Y) {j j' : L.ι} (hj : j = j') {k k' : L'.ι} (hk : k = k') :
    gw w f y j k = gw w f' y j' k' := by
  subst hf hj hk; rfl

theorem exists_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  intro R _ _ D₀ D h
  obtain ⟨Q, e₀, e, ⟨β₀, β₂₀, w₀, p₀, s₀, g₀, c₀, t₀⟩, ⟨β₁, β₂₁, w₁, p₁, s₁, g₁, c₁, t₁⟩⟩ := h
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  obtain ⟨f₀, hf₀, m₀⟩ := grp_iso p₀
  obtain ⟨f₁, hf₁, m₁⟩ := grp_iso p₁
  have cc₀ : ∀ a, D₀.c a ≫ f₀.hom = Q.c (e₀ a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₀, c₀ a, hs, Category.id_comp])
  have cc₁ : ∀ a, D.c a ≫ f₁.hom = Q.c (e a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₁, c₁ a, hs, Category.id_comp])
  have ea : ∀ x, e ((e₀.trans e.symm) x) = e₀ x := fun x => by simp
  have hcβ : ∀ χ, D₀.c χ ≫ (f₀ ≪≫ f₁.symm).hom = D.c ((e₀.trans e.symm) χ) := fun χ => by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, cc₀, Iso.comp_inv_eq, cc₁, ea]
  have hF : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) :
      G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁ = β₂₀ := by
    apply pullback.hom_ext
    · change _ ≫ β₂₁ ≫ (fst Q.B Q.B).left = β₂₀ ≫ (fst Q.B Q.B).left
      rw [s₁.1, s₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp
    · change _ ≫ β₂₁ ≫ (snd Q.B Q.B).left = β₂₀ ≫ (snd Q.B Q.B).left
      rw [s₁.2, s₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp

  subst hF
  have hLQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hLD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hLD₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  obtain ⟨wΛ, T⟩ := exists_cancel hLQ w₁ w₀ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀) hLD hLD₀
  refine ⟨f₀ ≪≫ f₁.symm, e₀.trans e.symm, ?_, hcβ, wΛ,
    (isGen_iff _).2 (T.pgen_cancel hLQ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀)), ?_⟩
  · show IsMonHom (f₀.hom ≫ f₁.inv)
    infer_instance
  intro a a' z J J' hJ hJ'
  choose d hd using fun χ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
  have hκ : 𝟙 (TK R).left ≫ jK R = jK R ≫ spMap (RingHom.id R) := by rw [hs]; simp
  have A₀ := t₀ (𝟙 _) hκ a a' z d J' hd hJ'
  have A₁ := t₁ (𝟙 _) hκ ((e₀.trans e.symm) a) ((e₀.trans e.symm) a') z d J hd hJ
  rw [ea, ea] at A₁
  have hP : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left = (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a)) (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc, hcβ, hcβ]
  have m₁ : β₂₁ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z)) ∈ (abelian₂ Q.B Q.M.L).U
      (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left)) := by
    have := Good.mem (L := Q.M.L) hd (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁)
    simp only [Category.assoc] at this ⊢
    exact this
  have m₂ : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z) ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := by
    have := Good.mem (L := D.P.L) hJ (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left)
    simp only [Category.assoc] at this
    exact this
  have m₃ : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z ∈ (abelian₂ D₀.P.A D₀.P.L).U (fun I => J' ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (psum D₀.P.A (x2 D₀.P.A) I.down).left)) :=
    Good.mem (L := D₀.P.L) hJ' (fun I : ULift (Finset (Fin 2)) => (psum D₀.P.A (x2 D₀.P.A) I.down).left) (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left
  have key := T _ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ _ m₁ m₂ m₃
  have k₁ : gw w₁ ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left) z (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left))
      (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) =
      GlobalTheory.PolDeg.lamVal w₁ (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a))
        (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left z d J :=
    gw_congr w₁ hP z (funext fun I => by rw [← hP]; simp only [Category.assoc])
      (funext fun I => by rw [← hP]; simp only [Category.assoc])
  rw [k₁] at key
  rw [A₀, A₁]
  change gw w₀ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _ = gw wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _
  rw [key, _root_.mul_assoc, _root_.mul_left_comm]
end GlobalTheory.MumCmp.SamePolIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_iso_refinements_same_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  first | exact @GlobalTheory.MumCmp.SamePolIso.exists_iso | exact GlobalTheory.MumCmp.SamePolIso.exists_iso | (intros; apply GlobalTheory.MumCmp.SamePolIso.exists_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslateStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_order_two_point_torus_extension_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.Point.exists_point | exact GlobalTheory.MumCmp.Point.exists_point | (intros; apply GlobalTheory.MumCmp.Point.exists_point <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatch

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add (f := _), map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatchStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_translate_of_mumfordBundle_match : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  first | exact @GlobalTheory.MumCmp.exists_translate_of_lam | exact GlobalTheory.MumCmp.exists_translate_of_lam | (intros; apply GlobalTheory.MumCmp.exists_translate_of_lam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := GlobalTheory.T.exists_iso_refinements_same_polarised R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := GlobalTheory.T.exists_translate_of_mumfordBundle_match R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := GlobalTheory.T.exists_order_two_point_torus_extension_translate R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
end
end

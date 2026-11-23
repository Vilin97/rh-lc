module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedDataStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover_noetherian | exact GlobalTheory.abelianScheme_descends_galoisCover_noetherian | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover_noetherian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedDataTransportIdentityLevelChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem descData_transport_id : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  intro h n N d B B' _ _ ζ ζ' X Y s s' C c π A₀ _ φ φ₂ P₀ lev₀ hS hA hsq hP₀ hw hlev
  obtain ⟨ψ, hψ, ⟨ψ₂, hsqψ, hC⟩, hlevψ⟩ := hS
  haveI : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl c.A)) hψ
  haveI := he
  have heψ' : e.hom.left ≫ ψ = 𝟙 _ := by simpa using heψ
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hψe : ψ = e.inv.left := by
    rw [← Category.id_comp ψ, ← hie, Category.assoc, heψ', Category.comp_id]
  let E₂ : G2 c.A ⟶ G2 C.A := lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)
  have hE₂ : E₂.left ≫ ψ₂ = 𝟙 _ := by
    have := GlobalTheory.SiegelDescent.lift_square hsqψ (τ := 𝟙 (G2 c.A).left) (a := fst c.A c.A ≫ e.hom)
      (b := snd c.A c.A ≫ e.hom) (a₀ := fst c.A c.A) (b₀ := snd c.A c.A)
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
    rw [this, lift_fst_snd, Over.id_left, Category.comp_id]
  refine ⟨e.hom.left ≫ φ, E₂.left ≫ φ₂, ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp π) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h1 : LBIso (C.P.pull E₂.left) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame P₀ _ (fun _ => φ₂) _ E₂.left fun _ => rfl) hw
    have h2 : LBIso (C.P.pull E₂.left) (c.P.pull (E₂.left ≫ ψ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame c.P _ (fun _ => ψ₂) _ E₂.left fun _ => rfl) hC
    have h3 : LBIso (c.P.pull (E₂.left ≫ ψ₂)) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.trans (pull_isLB c.isLB _) (pull_isLB C.isLB _) (pull_isLB hP₀ _) h2.symm h1
    exact LBIso.chartPull (chartPullUnpull c.P _ hE₂)
      (chartPullSame P₀ _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h3
  · intro a
    have h₀ := hlevψ a
    rw [pow_one, Category.id_comp, hψe] at h₀
    rw [← h₀, Category.assoc, ← Category.assoc e.inv.left, hie, Category.id_comp, hlev a]

end GlobalTheory.SiegLev
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedDataTransportIdentityLevelChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.descendedData_transport_identity_levelChange : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  first | exact @GlobalTheory.SiegLev.descData_transport_id | exact GlobalTheory.SiegLev.descData_transport_id | (intros; apply GlobalTheory.SiegLev.descData_transport_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_squareBundle_descent_galoisCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  first | exact @GlobalTheory.SquareDescent.exists_bundle_descent | exact GlobalTheory.SquareDescent.exists_bundle_descent | (intros; apply GlobalTheory.SquareDescent.exists_bundle_descent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  first | exact @GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | exact GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth | (intros; apply GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDescentFiniteEtaleSurjective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevDescent

theorem principal_of_sRel_finite_etale : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  intro h M M₀ d d₀ B B₀ _ _ ζ ζ₀ X Y _ s s₀ π c c₀ hfin het hsurj m hc
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  refine ⟨(relAmple_kTriv_of_finite_etale_cover Y X π c₀.A c.A φ c₀.diag c.diag hfin het hsurj c₀.ab
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) pb (GlobalTheory.SiegelPull.diag_iso sq iso)).1 h₁, ?_⟩
  intro T x ⟨t, ht⟩
  haveI := het
  haveI := hsurj
  let T' : Over X := Over.mk (pullback.snd T.hom π)
  let p : T'.left ⟶ T.left := pullback.fst T.hom π
  have hp : p ≫ T.hom = T'.hom ≫ π := pullback.condition
  haveI : Epi p := Flat.epi_of_flat_of_surjective _
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SiegelDescent.exists_liftHom pb T' T p hp
  have hx' : (ρ x).left ≫ φ = p ≫ x.left := (hρ x (ρ x)).1 rfl
  have w₁ : (fst c.A T').left ≫ φ ≫ c₀.A.hom = ((snd c.A T').left ≫ p) ≫ T.hom := by
    rw [pb.1.w, ← Category.assoc, Over.w (fst c.A T'), Category.assoc, hp, ← Category.assoc,
      Over.w (snd c.A T')]
  let χ : (c.A ⊗ T').left ⟶ (c₀.A ⊗ T).left := pullback.lift ((fst c.A T').left ≫ φ) ((snd c.A T').left ≫ p) w₁
  have χ₁ : χ ≫ (fst c₀.A T).left = (fst c.A T').left ≫ φ := pullback.lift_fst _ _ _
  have χ₂ : χ ≫ (snd c₀.A T).left = (snd c.A T').left ≫ p := pullback.lift_snd _ _ _
  have e : (lift (snd c.A T' ≫ ρ x) (fst c.A T')).left ≫ φ₂ = χ ≫ (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left :=
    GlobalTheory.SiegelDescent.lift_square sq (τ := χ)
      (by rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc χ, χ₂, Category.assoc])
      χ₁.symm
  have H := GlobalTheory.SiegelDescent.lbIso_square c.isLB c₀.isLB iso e
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullPull (c₀.P.pull (lift (snd c₀.A T ≫ x) (fst c₀.A T)).left) χ) t ht
  have hg := GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB (pull_isLB c₀.isLB _) _) (pull_isLB c.isLB _)
    H.symm ⟨t₁, ht₁⟩
  have h₃ : ρ x = 1 := h₂ T' (ρ x) hg
  have h₄ : p ≫ x.left = p ≫ (1 : T ⟶ c₀.A).left := by
    rw [← hx', h₃, GlobalTheory.SiegelDescent.one_comp pb T' T p hp]
  exact Over.OverMorphism.ext ((cancel_epi p).1 h₄)

end GlobalTheory.SiegLevDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalDescentFiniteEtaleSurjectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principal_descent_finite_etale_surjective : ∀ (h M M₀ d d₀ : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] (ζ : B) (ζ₀ : B₀) (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : X ⟶ Sp B) (s₀ : Y ⟶ Sp B₀) (π : X ⟶ Y) (c : SiegPre h M ζ s) (c₀ : SiegPre h M₀ ζ₀ s₀), IsFinite π → Etale π → Surjective π → SRel c c₀ d d₀ π → c.Principal → c₀.Principal := by
  first | exact @GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | exact GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale | (intros; apply GlobalTheory.SiegLevDescent.principal_of_sRel_finite_etale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelLowerLevelDescendsGalois

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PrincipalDescent

theorem principal_descends : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [IsNoetherianRing o] [CommRing o'] (b : TBase o n) (ζ' : o') (j : o →+* o') (X Y : Scheme.{0}) (s' : X ⟶ Sp o') (π : X ⟶ Y) (sY : Y ⟶ Sp o) (C : SiegPre h N ζ' s') (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (ν : Ga → (C.A.left ⟶ C.A.left)), N ≠ 0 → IsUnit (N : o') → n ∣ N → j (b.ζ : o) = ζ' ^ (N / n) → π ≫ sY = s' ≫ spMap j → IsGaloisCover Ga ρ π → IsQProjOver (π ≫ sY) → LocallyOfFiniteType sY → C.Principal → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → (∀ a, SRelBy C C (N / n) (N / n) (ρ a) (ν a)) → ∃ c : SiegPre h n (b.ζ : o) sY, c.Principal ∧ SRel C c (N / n) 1 π := by
  intro h n N o o' _ _ _ b ζ' j X Y s' π sY C Ga _ ρ ν hN hNu hdiv hζ hbase hπ hq hft hP ν1 νm hν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨c, hCc, -⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o' b.ζ ζ' j X s' C hN hNu hdiv hζ
  have hqA : IsQProjOver (C.A.hom ≫ π ≫ sY) := GlobalTheory.T.isQProjOver_of_relAmple_over_qproj_noetherian o X (π ≫ sY) C.A C.diag hq (pull_isLB C.isLB _) hP.1
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ := GlobalTheory.T.abelianScheme_descends_galoisCover_noetherian_base o X Y π sY Ga ρ C.A ν hπ hqA C.ab (fun a => (hν a).1) ν1 νm
  obtain ⟨P₀, φ₂, hP₀, sq, iso, norm⟩ := GlobalTheory.T.exists_squareBundle_descent_galoisCover X Y π Ga ρ C.A A₀ φ ν C.P hπ C.ab hA₀ gp hφ (fun a => (hν a).1) ν1 νm
    C.isLB C.rig₁ (fun a => (hν a).2.1)
  have hlev : ∀ a, ∃ x₀ : 𝟙_ (Over Y) ⟶ A₀, (C.lev a ^ (N / n)).left ≫ φ = π ≫ x₀.left := by
    intro a
    obtain ⟨f, hf, -⟩ := hπ.existsUnique_desc ((C.lev a ^ (N / n)).left ≫ φ) (fun g => by
      rw [← Category.assoc, ← (hν g).2.2 a, Category.assoc, hφ.inv g])
    have hf' : f ≫ A₀.hom = 𝟙 Y := by
      have := hπ.fin
      have := hπ.etale
      have := hπ.onto
      have : Epi π := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi π, ← Category.assoc, hf, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
      simp
    exact ⟨Over.homMk f hf', hf.symm⟩
  choose lev₀ hlev₀ using hlev
  obtain ⟨φ', φ₂', gp', sq', iso', hlev'⟩ := GlobalTheory.T.descendedData_transport_identity_levelChange h n N (N / n) o o' b.ζ ζ' X Y (s' ≫ spMap j) s' C c π A₀ φ φ₂ P₀ lev₀
    hCc gp sq hP₀ iso hlev₀
  obtain ⟨c₀, hpb⟩ := GlobalTheory.T.exists_siegelObject_of_galois_descended_data h n o b.ζ X Y π (s' ≫ spMap j) sY Ga ρ c A₀ φ' φ₂' P₀ lev₀ hbase.symm hπ hA₀ gp' sq' hP₀
    iso' norm hlev'
  have hR : SRel C c₀ (N / n) 1 π := by
    have e := ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N o o o' b.ζ b.ζ ζ' Y X X sY (s' ≫ spMap j) s' c₀ c C π (𝟙 X) 1 1 (N / n)
      ((sRel_one_one_iff c c₀ π).2 hpb)).1).1 hCc
    rwa [Category.id_comp] at e
  exact ⟨c₀, GlobalTheory.T.principal_descent_finite_etale_surjective h N n (N / n) 1 o' o ζ' b.ζ X Y s' sY π C c₀ hπ.fin hπ.etale hπ.onto hR hP, hR⟩

end GlobalTheory.PrincipalDescent
end
end
end

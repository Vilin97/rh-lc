module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStepNilExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickeningStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReductionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfIsStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftingOfNoetherianCaseStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBaseStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem liftObj_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A' _ i' h' hA' hg' F hF
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  obtain ⟨X, i, h, hX, hFil⟩ := H.exists_lift h' hA' hg' hF
  have hA₀ : IsAbelianScheme A₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h'
  have hg₀ : SmoothOfRelativeDimension g A₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h'.1 hg'
  obtain ⟨e, he, he₀⟩ := GlobalTheory.T.exists_section_lift_smooth_nilpotent_thickening R R₀ π hπ hn X A₀ i h hX (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left
    (Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀))
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    rw [Category.assoc, Category.assoc, h.w, Over.w_assoc, Over.w_assoc]
  have hl₁ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (fst X X).left
      = (fst A₀ A₀).left ≫ i := Limits.pullback.lift_fst _ _ _
  have hl₂ : (Limits.pullback.lift _ _ w : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left) ≫ (snd X X).left
      = (snd A₀ A₀).left ≫ i := Limits.pullback.lift_snd _ _ _
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g A₀ A₀ A' A' i' i' h' h' hA' hA' hg' hg' X X i i h h hX hX
    e e he he he₀ he₀ _ hl₁ hl₂ (𝟙 A₀) (fun d hd ↦ by rw [push_id]; exact hd)
  have hμ : (fst A₀ A₀ ≫ 𝟙 A₀) * snd A₀ A₀ = μ[A₀] := by
    rw [Category.comp_id, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [hμ] at hm
  obtain ⟨_, hp, hab⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_smoothLift_nilpotent R R₀ π hπ hn A₀ hA₀ X i h hX e he he₀ _ hl₁ hl₂ m hm
  have hg : SmoothOfRelativeDimension g X.hom := GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₀ π hπ hn g X A₀ i h hX hg₀
  exact ⟨X, _, i, hp, hab, hg, (schemeFil_eq_liftFil _ hp (P.1 R X g hab hg).1).symm.trans hFil⟩

end GlobalTheory.SqLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftAbelianSchemeOfSquareZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftObj (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.liftObj_sq | exact GlobalTheory.SqLift.liftObj_sq | (intros; apply GlobalTheory.SqLift.liftObj_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZero

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift.Hom

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  let x : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have e : x * x = x := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 x x rfl rfl, _root_.mul_one]; rfl)
  have e' : x = 1 := by simpa using e
  have := congrArg (fun z ↦ z.left) e'
  refine this.trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (T : Over S) :
    (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem liftHom_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have pA := (P.1 R A g hA hg).1
  have pB := (P.1 R B g' hB hg').1
  obtain ⟨l, l₁, l₂⟩ : ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
      l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j :=
    ⟨Limits.pullback.lift ((fst A₀ B₀).left ≫ i) ((snd A₀ B₀).left ≫ j) (by
      rw [Category.assoc, Category.assoc, h.1.w, k.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g' A₀ B₀ A B i j h k hA hB hg hg' A B i j h.1 k.1
    hA.smooth hB.smooth η[A].left η[B].left (Over.w η[A]) (Over.w η[B])
    ((one_left_comp h _).trans (Category.id_comp _)) ((one_left_comp k _).trans (Category.id_comp _)) l l₁ l₂ f₀
    (by rw [schemeFil_eq_liftFil _ h pA, schemeFil_eq_liftFil _ k pB]; exact hf)
  refine GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, hk ▸ hI⟩ A₀ B₀ A B i j h k hA hB f₀ (lift (𝟙 A) 1 ≫ φ) ?_
  have e : i ≫ (lift (𝟙 A) (1 : A ⟶ B)).left = (lift (𝟙 A₀) (1 : A₀ ⟶ B₀)).left ≫ l := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (i ≫ _) ≫ (fst A B).left = (_ ≫ l) ≫ (fst A B).left
      rw [Category.assoc, Category.assoc, l₁, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_fst, lift_fst,
        Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
    · change (i ≫ _) ≫ (snd A B).left = (_ ≫ l) ≫ (snd A B).left
      rw [Category.assoc, Category.assoc, l₂, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_snd, lift_snd,
        one_left_comp k, one_left, ← Category.assoc, h.1.w, Category.assoc]
  rw [Over.comp_left, ← Category.assoc, e, Category.assoc, hφ, ← Category.assoc, ← Over.comp_left, comp_mul,
    lift_fst_assoc, lift_snd, _root_.mul_one, Category.id_comp]

end GlobalTheory.SqLift.Hom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckMessingLiftHomomorphismOfSquareZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  first | exact @GlobalTheory.SqLift.Hom.liftHom_sq | exact GlobalTheory.SqLift.Hom.liftHom_sq | (intros; apply GlobalTheory.SqLift.Hom.liftHom_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem NilExp.mono {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {N M : ℕ} (h : NilExp κ N)
    (e : N ≤ M) : NilExp κ M :=
  fun l hl hs ↦ h l hl (e.trans hs)

theorem NilExp.eq_zero {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) {a : R}
    (ha : a ∈ I) : a = 0 := by

  have h1 := h [(1, a)] (by simpa using ha) (by simp)
  simpa [κ.dpow_one ha] using h1

theorem NilExp.eq_sqDP {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} (h : NilExp κ 1) :
    ∃ hI : I ^ 2 = 0, κ = divided₂ hI := by
  have hbot : I = ⊥ := eq_bot_iff.2 fun a ha ↦ (Ideal.mem_bot).2 (h.eq_zero ha)
  have hI : I ^ 2 = 0 := by
    rw [hbot, pow_two, Ideal.mul_bot]
    rfl
  refine ⟨hI, ?_⟩

  ext n x hx
  obtain rfl := h.eq_zero hx
  rcases n with _ | _ | n
  · rw [κ.dpow_zero hx, (divided₂ hI).dpow_zero hx]
  · rw [κ.dpow_one hx, (divided₂ hI).dpow_one hx]
  · rw [squareZeroDividedPowers_dpow hI (by omega), κ.dpow_eval_zero (by omega)]

theorem abelianLifting_of_sqLifting (hD : AbelianDeRham) (hU : AbelianUnobstructed) (hS : SqLifting) :
    AbelianLifting := by

  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (R₀ : Type) [CommRing R₀]
      (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → NilExp κ (n + 1) →
        LiftObj κ π ∧ LiftHom κ π := by
    intro n
    induction n with
    | zero =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨hI, rfl⟩ := NilExp.eq_sqDP h
      exact hS R I hI R₀ π hπ hker
    | succ n ih =>
      intro R _ I κ R₀ _ π hπ hker h
      obtain ⟨R₁, _, J, hJ, ρ, I₁, κ₁, π₁, st, h₁⟩ := exists_isStep_nilExp R R₀ I κ π hπ hker n h
      have hsq := hS R J hJ R₁ ρ st.surj st.kerJ
      have hih := ih R₁ I₁ κ₁ R₀ π₁ st.surj₁ st.ker₁ h₁
      exact ⟨GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization hD hU R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.1 hih.1,
        liftHom_of_isStep hD R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st hsq.2 hih.2⟩
  intro R _ I κ hκ R₀ _ π hπ hker
  obtain ⟨N, hN⟩ := (isPDNilpotent_iff κ).1 hκ
  exact key N R I κ R₀ π hπ hker (hN.mono (Nat.le_succ N))

theorem abelianLifting_of_schemeLifts :
    AbelianDeRham → AbelianSchemeLifts → AbelianUnobstructed → AbelianLifting := by
  intro hD hL hU
  refine abelianLifting_of_sqLifting hD hU (GlobalTheory.T.squareZeroLifting_of_noetherian_case hD ?_)
  intro R _ _ I hI R₀ _ π hπ hk
  exact ⟨GlobalTheory.T.grothendieckMessingLiftAbelianScheme_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk),
    GlobalTheory.T.grothendieckMessingLiftHomomorphism_of_squareZero hD R R₀ I hI π hπ hk (hL R I hI R₀ π hπ hk)⟩

end GlobalTheory.SqLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatements

section

@[expose] public section

theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare a b c d) (GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology a) e
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilDPOfFiveStatementsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.abelianSchemeHomLiftingNilDP_of_hodge_cube_duality_unobstructed : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed → GlobalTheory.Published.AbelianLifting := by
  first | exact @GlobalTheory.SqLift.abelianLifting_of_known_theorems | exact GlobalTheory.SqLift.abelianLifting_of_known_theorems | (intros; apply GlobalTheory.SqLift.abelianLifting_of_known_theorems <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfFour

section

@[expose] public section

namespace GlobalTheory.LiftFour

theorem abelianLifting_of_four :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a c d e => GlobalTheory.T.abelianSchemeHomLiftingNilDP_of_hodge_cube_duality_unobstructed a GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base c d e

end GlobalTheory.LiftFour
end
end

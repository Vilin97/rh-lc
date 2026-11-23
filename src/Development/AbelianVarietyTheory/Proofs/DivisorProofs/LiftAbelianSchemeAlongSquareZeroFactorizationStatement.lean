module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntermediateGrpPullbackAbelianSchemeStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReductionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTower

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift

theorem dual_eq_sum_of_ker {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P)
    (hx : ∀ c, ρ (x c) = 0) :
    ∃ (n : ℕ) (j : Fin n → R) (d : Fin n → Module.Dual R P), (∀ k, ρ (j k) = 0) ∧
      x = ∑ k, j k • d k := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k ↦ x (f (Pi.single k 1)), fun k ↦ (LinearMap.proj k) ∘ₗ s, fun k ↦ hx _, ?_⟩
  ext c
  have e1 : s c = ∑ k, s c k • (Pi.single k (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : x c = x (f (s c)) := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]

  rw [e2, e1, map_sum, map_sum]
  simp [mul_comm]

theorem isAdmissible_reduce : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hs g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h hi hA hg F hF
  obtain ⟨PF, -, PB, -, -⟩ := P
  letI : Algebra R R₁ := ρ.toAlgebra
  have hbc : (AbelianDeRham.bcMor h₂).IsBC := (PB R A g hA hg R₁ A₁ i₂ h₂).1
  obtain ⟨hfin, hproj, -⟩ := PF.prim hA hg

  have hPs : Function.Surjective (redMor h₂).pull := by
    intro c₁
    obtain ⟨z, rfl⟩ := hbc.2 c₁
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul r c =>
      obtain ⟨r', rfl⟩ := hs.surj r
      exact ⟨r' • c, by rw [liftSemi_tmul, LinearMap.map_smulₛₗ]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  have hex : ∀ x : HdR A, ∃ y : HdR A₁, (redMor h₂).Corr x y := fun x ↦ hbc.exists x
  have huniq : ∀ {x : HdR A} {y y' : HdR A₁}, (redMor h₂).Corr x y → (redMor h₂).Corr x y' → y = y' := by
    intro x y y' e e'
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [e c, e' c]
  have hlift : ∀ y : HdR A₁, ∃ x : HdR A, (redMor h₂).Corr x y := by
    intro y
    let l : primDR A →ₗ[R] R₁ :=
      { toFun c := y ((redMor h₂).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₁) l hs.surj
    exact ⟨x, fun c ↦ (LinearMap.congr_fun hx c).symm⟩
  let S : Submodule R (HdR A) → Submodule R₁ (HdR A₁) := fun F ↦
    { carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨x', hx', ex'⟩
        exact ⟨x + x', F.add_mem hx hx', fun c ↦ by simp [ex c, ex' c]⟩
      zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
      smul_mem' := by
        rintro r₁ y ⟨x, hx, ex⟩
        obtain ⟨r, rfl⟩ := hs.surj r₁
        exact ⟨r • x, F.smul_mem r hx, fun c ↦ by simp [ex c]⟩ }
  have comp : ∀ c, (redMor h₁).pull ((redMor h₂).pull c) = (redMor h).pull c :=
    fun c ↦ GrpMor.pull_pull (redMor h₂) (redMor h₁) (redMor h) (fun r ↦ RingHom.congr_fun hs.comp r) hi c
  obtain ⟨⟨N, hN⟩, hFil⟩ := hF
  refine ⟨S F, ⟨⟨S N, ⟨?_, ?_⟩⟩, fun y ↦ ?_⟩, fun y ↦ Iff.rfl⟩
  · refine Submodule.disjoint_def.2 fun y ⟨f, hf, ef⟩ ⟨n, hn, en⟩ ↦ ?_
    have hx : ∀ c, ρ ((f - n) c) = 0 := fun c ↦ by
      rw [LinearMap.sub_apply, map_sub, ← ef c, ← en c, sub_self]
    obtain ⟨k, j, d, hj, hsum⟩ := dual_eq_sum_of_ker ρ (f - n) hx
    have hfp : f = (Submodule.linearProjOfIsCompl F N hN (f - n) : HdR A) := by
      have e1 : Submodule.linearProjOfIsCompl F N hN f = ⟨f, hf⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hN ⟨f, hf⟩
      have e2 : Submodule.linearProjOfIsCompl F N hN n = 0 :=
        (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN).2 hn
      rw [map_sub, e1, e2, sub_zero]
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [ef c, hfp, hsum]

    simp [map_sum, Submodule.coe_sum, hj]
  · refine codisjoint_iff_le_sup.2 fun y _ ↦ ?_
    obtain ⟨x, ex⟩ := hlift y
    obtain ⟨f, hf, n, hn, rfl⟩ := Submodule.mem_sup.1 (hN.sup_eq_top ▸ Submodule.mem_top : x ∈ F ⊔ N)
    obtain ⟨yf, ef⟩ := hex f
    obtain ⟨yn, en⟩ := hex n
    refine Submodule.mem_sup.2 ⟨yf, ⟨f, hf, ef⟩, yn, ⟨n, hn, en⟩, huniq (fun c ↦ ?_) ex⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, ef c, en c, map_add (f := _)]
  · rw [hFil y]
    constructor
    · rintro ⟨x, hx, e⟩
      obtain ⟨x₁, e₁⟩ := hex x
      refine ⟨x₁, ⟨x, hx, e₁⟩, fun c₁ ↦ ?_⟩
      obtain ⟨c, rfl⟩ := hPs c₁
      rw [comp, e c, e₁ c]
      exact (RingHom.congr_fun hs.comp _).symm
    · rintro ⟨x₁, ⟨x, hx, e₁⟩, e⟩
      exact ⟨x, hx, fun c ↦ by rw [← comp, e, e₁ c]; exact RingHom.congr_fun hs.comp _⟩

end GlobalTheory.SqLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTowerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.group_scheme_divided_power_lift_tower : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  first | exact @GlobalTheory.SqLift.isAdmissible_reduce | exact GlobalTheory.SqLift.isAdmissible_reduce | (intros; apply GlobalTheory.SqLift.isAdmissible_reduce <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorization

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem corr_crysToDR_step_iff {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I : Ideal R}
    {I₁ : Ideal R₁} {κ : DividedPowers I} {κ₁ : DividedPowers I₁} {π : R →+* R₀} {ρ : R →+* R₁}
    {π₁ : R₁ →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {X₁ : Over (Sp R₁)} [GrpObj X₁] {X : Over (Sp R)}
    [GrpObj X] {i₁ : A₀.left ⟶ X₁.left} {i₂ : X₁.left ⟶ X.left} {i : A₀.left ⟶ X.left}
    (h₁ : IsGrpPullback A₀ X₁ (spMap π₁) i₁) (h₂ : IsGrpPullback X₁ X (spMap ρ) i₂)
    (h : IsGrpPullback A₀ X (spMap π) i) (e : i₁ ≫ i₂ = i)
    (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _))
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
  have k : GrpMor (dp0 R) (𝟙 _) X κ₁ (spMap π₁) A₀
      (ρ.comp (RingHom.id R)) ((𝟙 _) ≫ spMap π) ((𝟙 _) ≫ i) := by
    apply GrpMor.of_isGrpPullback
    · exact IsDPMorphism.comp _ M.dp (liftMor κ h).dp
    · simpa using M.base
    · simpa using h
  have e1 : ∀ c, (liftMor κ₁ h₁).pull ((redMor h₂).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by rw [Category.id_comp, e]) c
  have e2 : ∀ c, M.pull ((liftMor κ h).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c
  constructor
  · intro H c
    obtain ⟨c, rfl⟩ := hs c
    have := H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2] at this
    exact this
  · intro H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2]
    exact H _

theorem liftObj_step : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁]
    [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  intro P U R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ S L₂ L₁
  intro g A₀ _ A' _ i' h' hA' hg F hF
  have hπ : Function.Surjective π := S.comp ▸ S.surj₁.comp S.surj
  have hrig := P.2.2.2.1
  have hsp : spMap π = spMap π₁ ≫ spMap ρ := by rw [← S.comp, Cris.spMap_comp]
  have M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) := by
    refine ⟨S.dp, ?_, ?_, ?_⟩
    · simpa using hsp
    · simp
    · intro T x y x₀ y₀ hx hy
      have mul_left {U : Over (Sp R₀)} (a b : U ⟶ A₀) :
          (a * b).left = CategoryTheory.Limits.pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm) ≫ μ[A₀].left := by
        rw [Hom.mul_def, Over.comp_left, Over.lift_left]
      rw [mul_left, mul_left]
      congr 1
      apply CategoryTheory.Limits.pullback.hom_ext
      · simpa using hx
      · simpa using hy

  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, e₁₂, hA₁, hg₁⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A' i' (by rw [S.comp]; exact h') hA' hg
  obtain ⟨F₁, hF₁, hF₁F⟩ :=
    GlobalTheory.T.group_scheme_divided_power_lift_tower P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ A₁ A' i₁ i₂ i' h₁ h₂ h' e₁₂ hA' hg F hF

  obtain ⟨B₁, _, j₁, k₁, hB₁, hgB₁, hfB₁⟩ := L₁ g A₀ A₁ i₁ h₁ hA₁ hg₁ F₁ hF₁
  obtain ⟨C, _, j₂, k₂, hC⟩ := U R J hJ R₁ ρ S.surj S.kerJ B₁ hB₁
  have hgC : SmoothOfRelativeDimension g C.hom :=
    GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₁ ρ S.surj (by rw [S.kerJ]; exact ⟨2, hJ⟩) g C B₁ j₂ k₂.1 hC.smooth hgB₁
  have kC : IsGrpPullback A₀ C (spMap π) (j₁ ≫ j₂) := (k₁.comp k₂).congr hsp.symm rfl
  have b' : Function.Bijective (crysToDR κ h') :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hA' hg S.nil hπ S.ker h'
  have bC : Function.Bijective (crysToDR κ kC) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hC hgC S.nil hπ S.ker kC
  have bB₁ : Function.Bijective (crysToDR κ₁ k₁) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hB₁ hgB₁ S.nil₁ S.surj₁ S.ker₁ k₁
  have s' := (hrig R A' g hA' hg I κ S.nil R₀ π hπ S.ker A₀ i' h').2
  have sC := (hrig R C g hC hgC I κ S.nil R₀ π hπ S.ker A₀ _ kC).2

  set E := F.comap (crysToDR κ h') with hE
  set FC := E.map (crysToDR κ kC) with hFC
  have hFCa : IsAdmissible k₂ FC := by
    obtain ⟨N, hN⟩ := hF.1
    refine ⟨⟨(N.comap (crysToDR κ h')).map (crysToDR κ kC), ?_⟩, fun y ↦ ?_⟩
    · exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ bC)).isCompl
        ((Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ b')).symm.isCompl hN)
    obtain ⟨d₁, rfl⟩ := bB₁.2 y
    have l1 : crysToDR κ₁ k₁ d₁ ∈ Fil B₁ ↔ ∃ d ∈ E, M.Corr d d₁ := by
      change d₁ ∈ liftFil κ₁ k₁ ↔ _
      rw [hfB₁, Submodule.mem_comap, hF₁F]
      constructor
      · rintro ⟨x, hx, ex⟩
        obtain ⟨d, rfl⟩ := b'.2 x
        exact ⟨d, hx, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).1 ex⟩
      · rintro ⟨d, hd, ed⟩
        exact ⟨_, hd, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).2 ed⟩
    rw [l1]
    constructor
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).2 ed⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, ex⟩
      exact ⟨d, hd, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).1 ex⟩

  obtain ⟨A, _, j₃, k₃, hA, hgA, hfA⟩ := L₂ g B₁ C j₂ k₂ hC hgC FC hFCa
  have kA : IsGrpPullback A₀ A (spMap π) (j₁ ≫ j₃) := (k₁.comp k₃).congr hsp.symm rfl
  refine ⟨A, inferInstance, j₁ ≫ j₃, kA, hA, hgA, ?_⟩
  obtain ⟨N, -, hNC⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ C j₁ j₂ (j₁ ≫ j₂) k₁ k₂ kC rfl hC hgC
  obtain ⟨N', -, hNA⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ A j₁ j₃ (j₁ ≫ j₃) k₁ k₃ kA rfl hA hgA
  obtain rfl : N' = N := rfl
  ext d
  change crysToDR κ kA d ∈ Fil A ↔ d ∈ E
  rw [hNA d]
  change _ ∈ liftFil (divided₂ hJ) k₃ ↔ _
  rw [hfA, Submodule.mem_comap, ← hNC d]
  exact ⟨fun ⟨d', hd', e⟩ ↦ bC.1 e ▸ hd', fun hd ↦ ⟨d, hd, rfl⟩⟩

end GlobalTheory.SqLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorizationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.liftAbelianScheme_along_squareZero_factorization : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  first | exact @GlobalTheory.SqLift.liftObj_step | exact GlobalTheory.SqLift.liftObj_step | (intros; apply GlobalTheory.SqLift.liftObj_step <;> assumption)
end
end

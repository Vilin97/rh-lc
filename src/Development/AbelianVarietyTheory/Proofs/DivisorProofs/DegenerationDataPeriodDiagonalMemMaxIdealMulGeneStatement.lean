module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSectionUnit
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsJKToOpenTop

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

open Formalism.L2.Pj GlobalTheory.PsiCoordLocal

theorem gs_jK_toOpen_top {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (jK R) z ⊤ (DegPre.toOpen (R := R) ⊤ r) = thK R z (algebraMap R (FractionRing R) r) := by
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  rw [gs_eq _ z ⊤ hz]
  have e := congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have t : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [t]
  simp only [thK, RingHom.comp_apply]
  rw [e]
  rfl

theorem psiIn_iff_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), TopGood D.P z J → ∀ (χ : D.X) (I : Ideal R), D.PsiIn χ I ↔ ∃ r ∈ I, ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) = thK R z (algebraMap R (FractionRing R) r) := by
  intro R _ _ _ D z J hJ χ I
  let j : PUnit → D.P.L.ι := fun _ => J (𝟙 _ ≫ D.xK χ)
  have hxK : 𝟙 _ ≫ D.xK χ = jK R ≫ (D.c χ).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1 <;> simp
  have hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
    have := hJ.2 (D.c χ).left (Over.w (D.c χ))
    show ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (𝟙 _ ≫ D.xK χ))
    rw [hxK, this]
  have h := generic_le D χ j hj
  have key : ∀ r : R, ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val ↔
      ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) =
        thK R z (algebraMap R (FractionRing R) r) := by
    intro r
    have hz : z ∈ jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    have g1 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) =
        thK R z (algebraMap R (FractionRing R) r) := by
      rw [gs_pull (𝟙 _) (jK R) z ⊤ trivial, Category.id_comp]
      exact gs_jK_toOpen_top z r
    have g2 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) =
        ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) := by
      refine (gs_res _ z h hz _).trans ((gs_unit _ _ _ (h hz) _).trans ?_)
      rfl
    constructor
    · intro e
      rw [← g1, ← g2, e]
    · intro e
      refine fn_ext fun y _ => ?_
      obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) y z
      rw [g1, g2, e]
  constructor
  · intro hI
    obtain ⟨s, hs, es⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    exact ⟨r, hr, (key r).1 es⟩
  · rintro ⟨r, hr, e⟩
    exact (GlobalTheory.PeriodFormEdge.psiIn_iff ⟨j, hj, h, (key r).2 e⟩ I).2 hr

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauDiagEqUnitMulPsiSq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

theorem left_comp_hom_unit {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))}
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) : s.left ≫ B.hom = 𝟙 _ :=
  Over.w s

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R :=
  Over.w (toUnit (TK R))

theorem tau_diag_eq_unit_mul_psi_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (hT : D.TauBimult) (hE : D.PsiEven) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : TopGood D.P z J) (y : D.X) :
    ∃ u : Rˣ, val (D.tau y y) (𝟙 _) z J = uK R z u * val (D.psi y) (𝟙 _) z J ^ 2 := by
  have hG := hJ.1
  set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef
  have hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ := fun _ => rfl
  set rg := val D.rigK (𝟙 _) z J with hrgdef

  have h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]

  obtain ⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by
    rw [hrgdef]
    unfold DegPre.rigK
    rw [val_pull hG, Category.id_comp, toUnit_TK_left]
    have e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) :=
      (Category.comp_id _).symm
    rw [e]
    exact val_section_unit D.P z J hJ D.rig _ (fun _ => by
      rw [Category.id_comp]; exact left_comp_hom_unit (η[D.P.A]))

  set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef
  have h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J := by
    intro a a' b
    have := (val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))
    have hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b :=
      (val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])
    exact (congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this
  have hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u := by
    intro a a' b
    have e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
      unfold DegPre.pt3
      rw [← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u
    rw [e]
    exact val_section_unit D.P z J hJ D.cub.t _ (fun k => by
      rw [← Over.comp_left]; exact left_comp_hom_unit _)

  set S : D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun χ => val D.sym (D.xK χ) z J with hSdef
  have h3 : ∀ χ, P (-χ) * S χ = P χ := by
    intro χ
    have := (val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))
    rw [val_pull hG, Category.id_comp] at this
    exact this
  have hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u := by
    intro χ
    have e : D.xK χ = jK R ≫ (D.c χ).left := by
      show (toUnit (TK R) ≫ D.c χ).left = _
      rw [Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u
    rw [e]
    refine val_section_unit D.P z J hJ D.sym _ (fun k => ?_)
    fin_cases k
    · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _
      rw [← Over.comp_left]; exact left_comp_hom_unit _
    · show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _
      rw [Category.comp_id]; exact left_comp_hom_unit _

  obtain ⟨c0, hc0⟩ := hC 0 0 0
  obtain ⟨c1, hc1⟩ := hC y (-y) y
  obtain ⟨s, hs⟩ := hS y
  have e0 := h2 0 0 0
  simp only [h1, add_zero] at e0

  have hP0 : P 0 = (C 0 0 0 * rg)⁻¹ := by
    have : C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹ := mul_left_cancel e0
    rw [this]; group
  have e1 := h2 y (-y) y
  simp only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1
  have hPm : P (-y) = P y * (S y)⁻¹ := by rw [← h3 y]; group
  rw [hPm, hP0] at e1
  refine ⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩
  rw [h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]

  rw [eq_mul_inv_of_mul_eq e1.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataPeriodDiagonalMemMaxIdealMulGene

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DataPos

variable {V : Type} [CommRing V] [IsDomain V]

theorem lamPts_generic (D : DegPre V) (a b : D.X) (k : Fin 4) :
    lamPts (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b) k = jK V ≫ lamPts (D.c a) (D.c b) k := by
  have e : (toUnit (TK V)).left = jK V := GlobalTheory.Mum.UnitValuedLeadingSection.toUnit_TK_left V
  fin_cases k
  · show ((toUnit (TK V) ≫ D.c a) * (toUnit (TK V) ≫ D.c b)).left = jK V ≫ (D.c a * D.c b).left
    rw [← MonObj.comp_mul, Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c a).left = jK V ≫ (D.c a).left
    rw [Over.comp_left, e]
  · show (toUnit (TK V) ≫ D.c b).left = jK V ≫ (D.c b).left
    rw [Over.comp_left, e]
  · show (1 : TK V ⟶ D.P.A).left = jK V ≫ (1 : 𝟙_ _ ⟶ D.P.A).left
    rw [← e, ← Over.comp_left, MonObj.comp_one]

theorem lamPts_sec (D : DegPre V) (a b : D.X) (k : Fin 4) : lamPts (D.c a) (D.c b) k ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k <;> exact GlobalTheory.Mum.UnitValuedLeadingSection.left_comp_hom_unit _

theorem tau_diag_pos : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V))
    (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧
      ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε),
        ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
          Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  intro V _ _ _ D y hy
  obtain ⟨z₀⟩ : Nonempty (TK V).left := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.Mum.UnitValuedLeadingSection.exists_topGood V D.toPre.P z₀
  obtain ⟨u₁, hu₁⟩ :=
    GlobalTheory.Mum.UnitValuedLeadingSection.tau_diag_eq_unit_mul_psi_sq V D.toPre D.tau_bimult D.psi_even z₀ J₀ hJ₀ y
  obtain ⟨r₀, hr₀, e₀⟩ :=
    (GlobalTheory.Mum.UnitValuedLeadingSection.psiIn_iff_val V D.toPre z₀ J₀ hJ₀ y (maximalIdeal V)).1 (D.psi_pos y hy)
  have hr : (u₁ : V) * r₀ ^ 2 ∈ maximalIdeal V :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr₀ 2 two_pos)
  have eT : ((val (D.toPre.tau y y) (𝟙 _) z₀ J₀ : ((TK V).left.presheaf.stalk z₀)ˣ) : (TK V).left.presheaf.stalk z₀) =
      GlobalTheory.Mum.UnitValuedLeadingSection.thK V z₀ (algebraMap V _ ((u₁ : V) * r₀ ^ 2)) := by
    rw [hu₁, Units.val_mul, Units.val_pow_eq_pow_val, e₀, map_mul, map_mul, map_pow, map_pow]
    rfl
  have hr0 : algebraMap V (FractionRing V) ((u₁ : V) * r₀ ^ 2) ≠ 0 := by
    intro h
    have := (val (D.toPre.tau y y) (𝟙 _) z₀ J₀).ne_zero
    rw [eT, h, map_zero] at this
    exact this rfl
  refine ⟨_, hr, Units.mk0 _ hr0, rfl, ?_⟩

  set k : (FractionRing V)ˣ := Units.mk0 _ hr0 with hk
  set φV := lamPts (D.toPre.c y) (D.toPre.c y) with hφVdef
  set φK := lamPts (toUnit (TK V) ≫ D.toPre.c y) (toUnit (TK V) ≫ D.toPre.c y) with hφKdef
  have hφ : ∀ k, φK k = jK V ≫ φV k := lamPts_generic D.toPre y y
  let jst : Fin 4 → D.toPre.P.L.ι := fun k => J₀ (jK V ≫ φV k)
  have hint : ∀ k, φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) = ⊤ := fun k => hJ₀.2 (φV k) (lamPts_sec D.toPre y y k)
  have htop : LB.wchart D.toPre.P.L φV jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    exact this
  have htopK : LB.wchart D.toPre.P.L φK jst = ⊤ := eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => by
    have : jK V p ∈ φV k ⁻¹ᵁ D.toPre.P.L.U (jst k) := by rw [hint k]; trivial
    show p ∈ (φK k).base ⁻¹' (D.toPre.P.L.U (jst k) : Set _)
    rw [hφ k]
    exact this
  have hle : ∀ j, LB.wchart D.toPre.P.L φV j ≤ LB.wchart D.toPre.P.L φV j ⊓ LB.wchart D.toPre.P.L φV jst :=
    fun j => le_inf le_rfl (by rw [htop]; exact le_top)
  let u : LB.Gen (LB.LinComb D.toPre.P.L φV negε) := ⟨fun j => res (hle j) ((LB.LinComb D.toPre.P.L φV negε).g j jst)⟩
  obtain ⟨t, htg, ht⟩ := GlobalTheory.PolDeg.Wit.exists_tau D.toPre y y

  have hkey : t.s jst = res le_top (unitOn k) := by
    refine unit_ext fun x hx => ?_
    obtain rfl : x = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) x z₀
    refine Units.ext ?_
    rw [gm_res _ x _ hx]
    have e1 : gm (𝟙 _) x ((LB.LinComb D.toPre.P.L φK negε).U jst) (t.s jst) = val t (𝟙 _) x J₀ :=
      (val_of t (𝟙 _) x J₀ jst (fun k => by show J₀ (𝟙 _ ≫ φK k) = J₀ (jK V ≫ φV k); rw [Category.id_comp, hφ k])).symm
    rw [e1, ht _ _ x J₀ hJ₀.1, eT]
    have e2 := GlobalTheory.RefTauCoord.gm_unitOn (R := V) (RingHom.id (FractionRing V)) x k
    have e3 : spMap (RingHom.id (FractionRing V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e3] at e2
    exact e2.symm
  refine ⟨u, fun Z ρ z J hJ => ?_⟩
  have hmK : ρ z ∈ LB.wchart D.toPre.P.L φK jst := by rw [htopK]; trivial
  have hmV : (ρ ≫ jK V) z ∈ LB.wchart D.toPre.P.L φV jst := by rw [htop]; trivial
  have L1 : val (D.toPre.tau y y) ρ z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst * gm ρ z ⊤ (unitOn k) := by
    rw [← ht Z ρ z J hJ]
    refine (gen_trans htg ρ z (hJ.mem φK ρ) hmK).trans ?_
    rw [hkey]
    exact congrArg (_ * ·) (gm_res _ z _ hmK _)
  have L2 : val u (ρ ≫ jK V) z J =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    have hm := hJ.mem φV (ρ ≫ jK V)
    exact (gm_res _ z (hle _) hm _).trans (gm_linComb _ _ _ _ z _ _ hm hmV)
  have L3 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φK negε ρ z (fun k => J (ρ ≫ φK k)) jst =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF φV negε (ρ ≫ jK V) z (fun k => J ((ρ ≫ jK V) ≫ φV k)) jst := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF
    refine Finset.prod_congr rfl fun k _ => ?_
    have e : ρ ≫ φK k = (ρ ≫ jK V) ≫ φV k := by rw [hφ k, Category.assoc]
    have h : ∀ a b : Z ⟶ D.toPre.P.A.left, a = b →
        gm a z (D.toPre.P.L.U (J a) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J a) (jst k)) =
          gm b z (D.toPre.P.L.U (J b) ⊓ D.toPre.P.L.U (jst k)) (D.toPre.P.L.g (J b) (jst k)) := by
      rintro a b rfl; rfl
    exact congrArg (· ^ negε k) (h _ _ e)
  rw [L1, L2, L3, mul_comm]

end GlobalTheory.DataPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataPeriodDiagonalMemMaxIdealMulGeneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degenerationData_period_diagonal_mem_maxIdeal_mul_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (y : D.toPre.X), y ≠ 0 → ∃ r ∈ maximalIdeal V, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = algebraMap V _ r ∧ ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (lamPts (D.toPre.c y) (D.toPre.c y)) negε), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (TK V).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val (D.toPre.tau y y) ρ z J = gm ρ z ⊤ (unitOn k) * val u (ρ ≫ jK V) z J := by
  exact @GlobalTheory.DataPos.tau_diag_pos
end
end

module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTermsIsThetaTermsTorsionFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMembersClassSumsDeeperLevels
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourOfGaloisClassSumsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemIndexZeroCoefficientApproxStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemLamOfExactClassSumsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificati

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem GlobalTheory.Poinc.Sep.exists_isAct : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  intro g n F W Z i X₁
  obtain ⟨c, hc, pr, h1, h2, h3⟩ := X₁.sharp
  choose act hact using fun a : Matrix (Fin 8) (Fin 8) ℤ =>
    (h2 X₁.ρ.P.A fun u => (List.ofFn fun v => pr v ^ a u v).prod).exists
  exact ⟨act, c, hc, pr, h1, h2, h3, hact⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerMatrixActionThetaCompactificatiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_eighthPowerMatrixAction_thetaCompactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ act, IsAct X₁ act := by
  exact @GlobalTheory.Poinc.Sep.exists_isAct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaSetup_primePowerLevel_regular_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  first | exact @GlobalTheory.Poinc.Sep.exists_setup_regAt_chart | exact GlobalTheory.Poinc.Sep.exists_setup_regAt_chart | (intros; apply GlobalTheory.Poinc.Sep.exists_setup_regAt_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemClassSumsValuesOfFunctionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaSystem_classSums_values_of_functions : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo | exact GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo | (intros; apply GlobalTheory.Poinc.Sep.ExactSums.exact_of_isGeo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMembersClassSumsDeeperLevelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.uniformisedMembers_classSums_deeper_levels : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (x₀ : X₁.S.Gam) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper | exact GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper | (intros; apply GlobalTheory.Poinc.Sep.DeepSums.classSums_deeper <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.Poinc.Sep.nonempty_uMem_trait {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (hZ : IsNormalScheme Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (hact : IsAct X₁ act)
    (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V) (h₁ : IsLocalHom ev) (h₂ : RegAt X₁ z₁ ev)
    (h₃ : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i) :
    Nonempty (UMem X₁ z₁ act T.V ev T.D.toPre.X ![T.ϖ] ![T.β]) := by
  haveI := X₁.imm
  obtain ⟨hτ, h0, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T
  have hcn : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj hZ X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ z₁ act hact T.V (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β]
    (fun k => by rw [Subsingleton.elim k 0]; exact T.irr.ne_zero)
    (fun k => by rw [Subsingleton.elim k 0]; exact T.symm)
    (fun k => by rw [Subsingleton.elim k 0]; exact h0) hτ T.V (RingHom.id _) hcn Function.injective_id
    (RingHom.Finite.id _) T.D (AddEquiv.refl _) (GlobalTheory.PolDeg.Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb ev h₁ h₂ h₃
  exact ⟨𝔪⟩

theorem _root_.GlobalTheory.Poinc.Sep.exists_vPre_traits_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, V₁, _, _, _, ρ, ev, D₀, e₀, hj, hN, hcn, hinj, hfin, hloc, hreg, hcomp, href⟩ :=
    GlobalTheory.T.exists_thetaSetup_primePowerLevel_regular_chart g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsymm hnn hpos hτ ξ hξ l hl hln j₀
  have hdom := (GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁).1
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_eighthPowerMatrixAction_thetaCompactification g n F W Z i X₁
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  obtain ⟨G₀, _, _, A₀, U₀, y₀, α, α₂, hsemi, hy₀, hcart, hsq, hlb⟩ := hξ.2 V₁ ρ hcn hinj hfin D₀ e₀ href
  obtain ⟨𝔪₀, hsharp⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact V Q m t δ
    (fun k => (ht k).2) hsymm hnn hτ V₁ ρ hcn hinj hfin D₀ e₀ href G₀ A₀ U₀ y₀ α α₂ hsemi hcart hsq hlb ev hloc hreg
    (by rw [hcomp, hy₀])
  have hζ : IsUnit (zetaAway n) := by
    rw [← cycBase_ζ (show n ≠ 0 by omega)]
    exact Units.isUnit _
  have hρ : IsLocalHom ρ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite V V₁ := hfin
    haveI : FaithfulSMul V V₁ := (faithfulSMul_iff_algebraMap_injective V V₁).2 hinj
    exact (inferInstance : IsLocalHom (algebraMap V V₁))
  let Tr : Type 1 := Σ T : Trait F, {e : X₁.M.Z.presheaf.stalk z₁ →+* T.V // IsLocalHom e ∧ RegAt X₁ z₁ e ∧
    jK T.V ≫ spMap e ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i}
  let VV : Option Tr → Type := fun y => match y with | none => V₁ | some T => T.1.V
  letI iR : ∀ y, CommRing (VV y) := fun y => match y with
    | none => inferInstanceAs (CommRing V₁) | some T => inferInstanceAs (CommRing T.1.V)
  haveI iD : ∀ y, IsDomain (VV y) := fun y => match y with
    | none => inferInstanceAs (IsDomain V₁) | some T => inferInstanceAs (IsDomain T.1.V)
  haveI iL : ∀ y, IsLocalRing (VV y) := fun y => match y with
    | none => inferInstanceAs (IsLocalRing V₁) | some T => inferInstanceAs (IsLocalRing T.1.V)
  let EV : ∀ y, X₁.M.Z.presheaf.stalk z₁ →+* VV y := fun y => match y with | none => ev | some T => T.2.1
  let XX : Option Tr → Type := fun y => match y with | none => Q.X | some T => T.1.D.toPre.X
  letI iA : ∀ y, AddCommGroup (XX y) := fun y => match y with
    | none => inferInstanceAs (AddCommGroup Q.X) | some T => inferInstanceAs (AddCommGroup T.1.D.toPre.X)
  haveI iF : ∀ y, Module.Free ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Free ℤ Q.X) | some T => inferInstanceAs (Module.Free ℤ T.1.D.toPre.X)
  haveI iG : ∀ y, Module.Finite ℤ (XX y) := fun y => match y with
    | none => inferInstanceAs (Module.Finite ℤ Q.X) | some T => inferInstanceAs (Module.Finite ℤ T.1.D.toPre.X)
  let MM : Option Tr → ℕ := fun y => match y with | none => m | some _ => 1
  let tt : ∀ y, Fin (MM y) → VV y := fun y => match y with | none => fun k => ρ (t k) | some T => ![T.1.ϖ]
  let dd : ∀ y, Fin (MM y) → LinearMap.BilinForm ℤ (XX y) := fun y => match y with | none => δ | some T => ![T.1.β]
  let 𝔪 : ∀ y, UMem X₁ z₁ act (VV y) (EV y) (XX y) (tt y) (dd y) := fun y => match y with
    | none => 𝔪₀
    | some T => (nonempty_uMem_trait hnorm X₁ z₁ act hact T.1 T.2.1 T.2.2.1 T.2.2.2.1 T.2.2.2.2).some
  have hlab : Set.range (Subtype.val : X₁.S.HH X₁.M z₁ → X₁.S.Gam) = X₁.S.HH X₁.M z₁ := Subtype.range_val
  choose u hu₁ hu₂ hu₃ using fun y => GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hx₀ (VV y) (EV y) (XX y) (MM y) (tt y) (dd y)
    (𝔪 y) (X₁.S.HH X₁.M z₁) Subtype.val hlab
  let Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁) :=
    { posW := X₁.posW
      Y := Option Tr
      V := VV
      cn := fun y => (𝔪 y).cn
      ev := EV
      ev_loc := fun y => (𝔪 y).loc
      X := XX
      rank_le := fun y => match y with
        | none => hrk
        | some T => (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.2.2 (by omega) hζ
      m := MM
      t := tt
      t_mem := fun y => match y with
        | none => fun k => ⟨map_nonunit ρ _ (ht k).1, fun h => (ht k).2 (hinj (h.trans (map_zero ρ).symm))⟩
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact ⟨T.1.irr.not_isUnit, T.1.irr.ne_zero⟩
      δ := dd
      bal := fun y => match y with
        | none => fun k => mem_balForms_int.2 (hsymm k)
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact mem_balForms_int.2 T.1.symm
      nonneg := fun y => match y with
        | none => hnn
        | some T => fun k => by
            rw [Subsingleton.elim (α := Fin 1) k 0]
            exact (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.1
      pos := fun y => match y with
        | none => hpos
        | some T => fun x hx => ⟨(0 : Fin 1), (GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ _ F T.1).2.2.1 x hx⟩
      Q := X₁.S.HH X₁.M z₁
      u := u
      u_unit := hu₂ }
  have hgeo : IsGeo X₁ z₁ act x₀ Φ Subtype.val := ⟨hx₀, hlab, fun y => ⟨𝔪 y, hu₁ y⟩⟩
  refine ⟨j, X₁, z₁, hdom, Φ, none, ρ, AddEquiv.refl _, Equiv.refl _, ⟨x₀, AddSubgroup.subset_closure hx₀⟩, hj, ?_, ?_,
    fun y => hu₃ y _ rfl, ?_, ?_, ?_⟩
  · intro T e h₁ h₂ h₃
    refine ⟨some ⟨T, e, h₁, h₂, h₃⟩, RingHom.id _, AddEquiv.refl _, rfl, inferInstanceAs (IsPrincipalIdealRing T.V),
      Function.injective_id, inferInstanceAs (IsLocalHom (RingHom.id T.V)), rfl, fun k => ?_⟩
    rw [Subsingleton.elim (α := Fin 1) k 0]
    exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨hinj, hfin, hcomp, fun k => ⟨rfl, fun _ _ => rfl⟩, 𝔪₀.D.toPre, 𝔪₀.e₈, hsharp, ?_⟩
    rw [← hN]
    exact GlobalTheory.T.memberTerms_isThetaTerms_torsionFrames g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev Q.X m _ δ 𝔪₀ _ Subtype.val hlab _ (hu₁ none)
  · rintro (_ | T) h
    · rfl
    · exact absurd rfl h
  · rw [← hN]
    exact GlobalTheory.T.thetaSystem_classSums_values_of_functions g n F W Z i X₁ z₁ act x₀ Φ _ hgeo
  · rw [← hN]
    exact GlobalTheory.T.uniformisedMembers_classSums_deeper_levels g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth X₁ z₁ act hact x₀ Φ _ hgeo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemTraitsChartThetaModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (Φ : VPre (id : ℤ → ℤ) g W (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) (c₀ : Φ.Q), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ ∧ IsChartMemberP X₁ z₁ Φ ((l ^ j) ^ 2) Q ξ t δ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((l ^ j) ^ 2) ∧ Φ.ClassSums ((l ^ j) ^ 2) := by
  first | exact @GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | exact GlobalTheory.Poinc.Sep.exists_vPre_traits_chart | (intros; apply GlobalTheory.Poinc.Sep.exists_vPre_traits_chart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierTermSystemRegularTraitsGivenChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory



theorem GlobalTheory.Poinc.Sep.exists_chartMember_traitsR : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Φ : VSys (id : ℤ → ℤ) g W ((l ^ j) ^ 2) (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m), j₀ ≤ j ∧ HasTraitsR X₁ z₁ Φ.pre ∧ IsChartMember X₁ z₁ Φ Q ξ t δ y ρ e h := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln j₀
  obtain ⟨j, X₁, z₁, hdom, Φ, y, ρ, e, h, c₀, hj, hR, hC, hU, hM, hE, hCS⟩ :=
    GlobalTheory.T.exists_fourierTermSystem_traits_chart_thetaModel g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth V Q m t δ hrk ht hsym hnn hpos hmon ξ hξ l hl hln
      (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (l ^ j) ^ 2 := by
    have h2 : 2 ≤ l ^ j := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hU y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hM y₁ h₁).trans (hM y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((l ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units ℤ id g 8 W _ Φ ((l ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁, z₁, (Φ.rescale v).toVSys ((l ^ j) ^ 2) hLam' hFour', y, ρ, e, h,
    le_trans (le_max_left _ _) hj, hR, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, e₈, hS, hT⟩ := hC
  refine ⟨h1, h2, h3, h4, D, e₈, hS, ?_⟩
  have h0 : Φ.term y (fun a => e.symm ((0 : Fin 8 → Q.X) a)) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun a => e.symm ((0 : Fin 8 → Q.X) a)) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((l ^ j) ^ 2) (Fin 8 → Q.X) Φ.Q e₈
    (fun mu c => Φ.term y (fun a => e.symm (mu a)) c) (v y) c₀ hT h0
  refine cast (congrArg (fun T : (Fin 8 → Q.X) → Φ.Q → Φ.V y => IsThetaTerms D ((l ^ j) ^ 2) e₈ T) ?_) this
  funext mu c
  show Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a)) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun a => e.symm (mu a)) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono W (Φ.t y) (Φ.δ y) (fun a => e.symm (mu a))
  exact mul_right_comm _ _ _
end
end

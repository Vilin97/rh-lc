module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelationStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelationStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInMaximalIdealOfNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZeroStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSectionSupportEqUnivStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_integral_theta_section_with_expansion : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  first | exact @GlobalTheory.ThetaIntegral.exists_theta | exact GlobalTheory.ThetaIntegral.exists_theta | (intros; apply GlobalTheory.ThetaIntegral.exists_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelationStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_psi_thetaExpansionPsiRelation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  first | exact @GlobalTheory.exists_psi_psiRel | exact GlobalTheory.exists_psi_psiRel | (intros; apply GlobalTheory.exists_psi_psiRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPsiRelationOfPullbackExtensionFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  first | exact @GlobalTheory.psiRel_of_pullB | exact GlobalTheory.psiRel_of_pullB | (intros; apply GlobalTheory.psiRel_of_pullB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU

theorem fe_one_of_psiRel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U θ f hθ hψ t s hts
  obtain ⟨hp, hq⟩ := PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hp θ
  obtain ⟨s₀, hs₀, -⟩ := hq f
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expF_of_theta_degree_one h₁ h₂ V hV D A G U θ f hθ th s₀ hth hs₀).2.2 t s hts
  exact famFE_one_of_psiRel h₁.globalFns V D (Kbar V) s₀ s c (GlobalTheory.T.thetaPsiRelation_of_pullback_extension_field V D (Kbar V) f s₀ hs₀ hψ) hc

end GlobalTheory.UU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOneStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.thetaExpansion_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → PsiRel D (𝟙_ _) f → U.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.fe_one_of_psiRel | exact GlobalTheory.UU.fe_one_of_psiRel | (intros; apply GlobalTheory.UU.fe_one_of_psiRel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem exists_degData_fe_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U

  obtain ⟨θ, f, hθ⟩ := GlobalTheory.T.exists_integral_theta_section_with_expansion hL hL2 V hV D A G U
  have hf := (GlobalTheory.T.thetaSection_support_eq_univ hL hL2 V hV D A G U θ f hθ).1

  obtain ⟨ψ, h, hpsi⟩ := GlobalTheory.T.exists_psi_thetaExpansionPsiRelation hL hL2 V D f hf
  obtain ⟨U', hP, hgen, -, hth⟩ := exists_preU_setPsi V D (IsLocalRing.maximalIdeal V) A G U ψ h
  obtain ⟨θ', hθ'⟩ := hth θ f hθ

  have hev := GlobalTheory.T.even_psi_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hbi := GlobalTheory.T.bimultiplicative_tau_of_thetaExpansionPsiRelation hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hfin := GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow V hV (setPsi D ψ h) A G U' θ' f hθ' (hf 0) hpsi
  have hpos := GlobalTheory.psiIn_maximalIdeal_of_ne_zero V hV (setPsi D ψ h) hbi hev (hfin 1)
  have hfe := GlobalTheory.T.thetaExpansion_functionalEquation_degree_one hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  exact ⟨{ toPre := setPsi D ψ h, psi_even := hev, tau_bimult := hbi, psi_pos := hpos, psi_tendsto := hfin }, U', hP, hgen, hfe⟩
end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOnStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.exists_degData_fe_one | exact GlobalTheory.UU.exists_degData_fe_one | (intros; apply GlobalTheory.UU.exists_degData_fe_one <;> assumption)
end
end

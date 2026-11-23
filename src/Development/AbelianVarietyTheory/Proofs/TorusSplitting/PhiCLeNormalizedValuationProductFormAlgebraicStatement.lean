module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogbNormUniformizerNormalisationStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCSmulPull
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulPhiLeValuationProductFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.card_mul_phi_le_valuation_productForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  first | exact @GlobalTheory.EtaVal.card_mul_phiC_le_valuation | exact GlobalTheory.EtaVal.card_mul_phiC_le_valuation | (intros; apply GlobalTheory.EtaVal.card_mul_phiC_le_valuation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  first | exact @GlobalTheory.EtaVal.datAt_of_uniformisation | exact GlobalTheory.EtaVal.datAt_of_uniformisation | (intros; apply GlobalTheory.EtaVal.datAt_of_uniformisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbeddingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_injective_intO_embedding_of_norm_lt_one : ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∃ (i : T.Fr →+* T'.Fr) (ρ : ℕ), 0 < ρ ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (φ a)) ∧ (∀ x, vV T'.V (i x) = (ρ : ℤ) * vV T.V x) ∧ ∀ (p : ℕ) (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) → ∃ f : T'.V →+* intO ↥C.S, Function.Injective f ∧ (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) ∧ ∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  first | exact @GlobalTheory.EtaVal.finite_extension_ramification_embedding | exact GlobalTheory.EtaVal.finite_extension_ramification_embedding | (intros; apply GlobalTheory.EtaVal.finite_extension_ramification_embedding <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralThetaSection_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  first | exact @GlobalTheory.EtaVal.intSec_exists_and_baseChange | exact GlobalTheory.EtaVal.intSec_exists_and_baseChange | (intros; apply GlobalTheory.EtaVal.intSec_exists_and_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCSmulPullStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symB_phiC_eq_mul_of_pullback : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  first | exact @GlobalTheory.EtaVal.phiC_smul_pull | exact GlobalTheory.EtaVal.phiC_smul_pull | (intros; apply GlobalTheory.EtaVal.phiC_smul_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.valuationForm_psi_balanced_symmetric_periodForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧ (∀ a b, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = QForm.bOf P.D.toPre Q a b) ∧ (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ ∀ (C : Type) [NormedField C] (f : V →+* C) (p : ℕ), Function.Injective f → (∀ a, ‖f a‖ ≤ 1) → ∀ a b, betaAt P.D.toPre f p a b = -Real.logb p ‖f ϖ‖ * (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b := by
  first | exact @GlobalTheory.ValForm.main | exact GlobalTheory.ValForm.main | (intros; apply GlobalTheory.ValForm.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraic

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem phiC_le_normalized_valuation_local_model_base_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (O : Type) [CommRing O]
    (β₀ : O →+* c.F) (Y : Model Xo c β₀) (hB : PointsOfFlagModel.BaseAt la β₀) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (y : IntFr Xo c T io) (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (Pc : PointsOfFlagModel.PtC Y C) (hO : OverLa la T.V io e)
    (hAlg : T.FinRes) (eF : T.Fr →+* ↥C.S) (heF : eF.comp io = Pc.fK)
    (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (hy : letI := io.toAlgebra; Pc.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x)
    (cj : E → E) (hcj : ∀ a, cj a = IsCMField.complexConj E a) :
    ∃ (A : DatAt Y Pc) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧
      ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ)
        (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f →
        ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 *
          (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  letI := io.toAlgebra
  obtain ⟨G, ⟨I⟩⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).1 T io y
  obtain ⟨T', φ, G', m, hφi, hφf, -, -, U, hU, hUt⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G I.t' I.m2 y.1.x I.m1 hAlg
  obtain ⟨i, ρ, hρ, hi, hiv, hf⟩ := GlobalTheory.T.exists_injective_intO_embedding_of_norm_lt_one T T' φ hφi hφf
  obtain ⟨f, hfi, hfφ, hfm⟩ := hf _ C eF hle hlt
  obtain ⟨A, e', hA⟩ := GlobalTheory.T.degeneration_data_at_model_point_of_uniformisation E H Dw l Xo c O β₀ Y la hB
    T io e hO y.1.x y.1.s G I y.1.x_over T' φ G' m U hU hUt _ C Pc eF f heF hy hfφ hfm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨Q, β, hQ, hQ0, -, hβQ, hβ⟩ := GlobalTheory.T.valuationForm_psi_balanced_symmetric_periodForm E H T'.V G' U ϖ hϖ cj hcj
  have hf1 : ∀ a, ‖((intO ↥C.S).subtype.comp f) a‖ ≤ 1 := fun a => (f a).2
  have hfi' : Function.Injective ((intO ↥C.S).subtype.comp f) :=
    (intO ↥C.S).subtype_injective.comp hfi
  have hO' := hO.bc i hρ hiv
  obtain ⟨hun, hew⟩ := GlobalTheory.T.logb_norm_uniformizer_normalisation c.F la T' (i.comp io) (ρ * e) hO' ϖ hϖ C _ hf1
  set t : ℝ := -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖((intO ↥C.S).subtype.comp f) ϖ‖ with ht
  have hρe : (0 : ℝ) < ((ρ * e : ℕ) : ℝ) := by exact_mod_cast hO'.1
  have hew' : (0 : ℝ) < (Formalism.BasicNotions.eWL c.F la : ℝ) := by exact_mod_cast hew
  have ht0 : 0 ≤ t := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.1 hneg) (mul_pos hρe hew')
    linarith
  obtain ⟨bA, hbA, hφ⟩ := GlobalTheory.T.exists_symB_phiC_eq_mul_of_pullback E cj A.Ylat U.D.toPre.X e' β t ht0
  refine ⟨A, bA, fun a b => ?_, ?_⟩
  · rw [hbA, hA, hβ _ _ _ hfi' hf1]
  intro R hR hR1 J _ n cf xs g hsp hg
  letI : Algebra c.F T'.Fr := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr T'.Fr ψ y.1
  obtain ⟨I'⟩ := (GlobalTheory.T.integralThetaSection_exists_and_baseChange E H Dw l Xo c).2 T.V T'.V φ ψ y.1 y' G G' m I hi hy'
  have hval := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR J n cf xs g hg T.Fr y.1 y.2.1).2
    T'.Fr ψ y' hy'
  by_cases h0 : evI y g = 0
  · rw [h0, nval_zero]; exact le_top
  have h0' : i (evI y g) ≠ 0 := (map_ne_zero i).2 h0
  have hpt := GlobalTheory.T.card_mul_phi_le_valuation_productForm E H Dw l Xo c T'.V y' G' I' U ϖ hϖ Q hQ hQ0 cj hcj β hβQ R hR hR1 J n cf xs
    (i (evI y g)) hsp hval h0'
  rw [← nval_bc (V' := T'.V) i hρ hiv e, nval_of_ne h0', EReal.coe_le_coe_iff, le_div_iff₀ hρe, hφ]
  refine le_trans (le_of_eq ?_) hpt
  calc _ = (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β *
        (t * (((ρ * e : ℕ) : ℝ) * Formalism.BasicNotions.eWL c.F la)) := by ring
    _ = _ := by rw [hun, _root_.mul_one]

theorem phiC_le_nval_of_lies :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (z : PointsOfFlagModel.Pt Tw .yy), OverLa la T.V io e → y.IsAlg → LiesOverBaseChange la Tw T io y z → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (A : DatAt (Tw.Y z.1) z.2.2.1) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧ ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f → ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  intro E _ _ _ H Dw l Xo c la Tw hTw T io e y z hO hAlg hL cj hcj
  have hv : z.1.1 = la := congrArg Subtype.val hL.1
  have hB : PointsOfFlagModel.BaseAt la (Tw.β z.1) := by
    have h := (hTw.1 z.1).1
    rwa [hv] at h
  refine hL.2.elim fun eF h => ?_
  exact phiC_le_normalized_valuation_local_model_base_change E H Dw l Xo c la _ (Tw.β z.1) (Tw.Y z.1) hB T io e y z.2.1 z.2.2.1
    hO hAlg eF h.1 h.2.1 h.2.2.1 h.2.2.2.1 cj hcj

end GlobalTheory.EtaVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCLeNormalizedValuationProductFormAlgebraicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.phiC_le_normalized_valuation_product_form_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (z : PointsOfFlagModel.Pt Tw .yy), OverLa la T.V io e → y.IsAlg → LiesOverBaseChange la Tw T io y z → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∃ (A : DatAt (Tw.Y z.1) z.2.2.1) (bA : Formalism.MainNotions.ModuliIntegralCharts.SymB cj A.Ylat), (∀ a b, (bA : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a b = A.beta a b) ∧ ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), GlobalTheory.EtaAn.Spans xs → IsEtaRule Xo c R cf xs f → ((((Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * (Formalism.BasicNotions.eWL c.F la * Formalism.MainNotions.ModuliIntegralCharts.phiC cj bA) : ℝ)) : EReal) ≤ nval T.V e (evI y f) := by
  first | exact @GlobalTheory.EtaVal.phiC_le_nval_of_lies | exact GlobalTheory.EtaVal.phiC_le_nval_of_lies | (intros; apply GlobalTheory.EtaVal.phiC_le_nval_of_lies <;> assumption)
end
end

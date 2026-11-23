module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValuesStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cmCurveTorsion_definedOver_of_weberValues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (F : IntermediateField ℚ ℂ) (n : ℕ), 0 < n → (H.rt0 ∈ F → WeberIn H F n → CurveOver H F n) ∧ ∀ m, m ∣ n → CurveOver H F n → CurveOver H F m := by
  first | exact @GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn | exact GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn | (intros; apply GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | exact GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id | (intros; apply GlobalTheory.CompRat.FixedConst.fnAlgClosed_of_permutes_id <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.permutes_periodSpaces_id_of_fixes_cm_curve_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ l.M → ConjugationPermutesPeriods F τ id := by
  first | exact @GlobalTheory.CompRat.permutes_id_of_fixesCurve | exact GlobalTheory.CompRat.permutes_id_of_fixesCurve | (intros; apply GlobalTheory.CompRat.permutes_id_of_fixesCurve <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hA hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces E H D l Xo _ g ty F hD rfl hty hA c fun τ hτ => ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  exact GlobalTheory.T.permutes_periodSpaces_id_of_fixes_cm_curve_torsion E H D l Xo _ g ty F hD rfl hty hA hsig τ (hτ _ (c.le h1)) (hC τ hτ)

end GlobalTheory.CompRat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefinedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.coeffField_algClosed_functionField_of_torsionDefined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  first | exact @GlobalTheory.CompRat.fnAlgClosed_of_curveOver | exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver | (intros; apply GlobalTheory.CompRat.fnAlgClosed_of_curveOver <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.FieldAlg

theorem recordField_le_of_pinField {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem fnAlgClosed_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ n : ℕ, 0 < n → CurveOver (hostOfRecord D) (FO D) n → ∀ j, InR D j → ∀ (l₂ : Level Q.H) (Xo₂ : Moduli (Q.Dw j) l₂) (c₂ : Coeff l₂), l₂.A = 1 → l₂.M ∣ n → c₂.F = Q.c.F → FnAlgClosed (Xo := Xo₂) (c := c₂) := by
  intro D Q hP hC n hn hcurve j hj l₂ Xo₂ c₂ hA hM hF
  obtain ⟨⟨ι, hι⟩, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := GlobalTheory.RankOneDatum.exists_datum_rank_one D Q.H (Q.Dw j) (D.sp.W j) ι hι (by omega)
  have hle := recordField_le_of_pinField Q hP.2.2.1
  have hc : CurveOver Q.H (FO D) l₂.M := by
    have h0 : CurveOver Q.H (FO D) n := by rw [hC.1]; exact hcurve
    exact (GlobalTheory.T.cmCurveTorsion_definedOver_of_weberValues _ Q.H (FO D) n hn).2 _ hM h0
  refine GlobalTheory.T.coeffField_algClosed_functionField_of_torsionDefined _ Q.H (Q.Dw j) l₂ Xo₂ c₂ (by omega) hA (Or.inr (Or.inr ⟨by omega, h1⟩)) ?_
  intro τ hτ
  exact hc τ fun x hx => hτ x (by rw [hF]; exact hle hx)

end GlobalTheory.FinalJoin.FieldAlg
end
end

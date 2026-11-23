module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_every_point : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.MixHt.heightProj | exact GlobalTheory.MixHt.heightProj | (intros; apply GlobalTheory.MixHt.heightProj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arFormExists_of_isMix : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q →
    ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  intro hA hT k _ X _ p D hX ι _ L
  obtain ⟨T, hT⟩ := hT k X p (isAmb_of_isArithVar hX) (D + 1)
  have hg : HasDim (genericPoint X) (D + 1) :=
    ((GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)).2.2.2.2.2 X (D + 1)).2 hX.dim_eq
  obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D (fun M => T (D + 1) M (genericPoint X))
    (fun M N h => hT.iso (D + 1) M N _ le_rfl hg h)
    (fun M e => hT.symm (D + 1) M e _ le_rfl hg)
    (fun A B M => hT.add D A B M _ le_rfl hg) ι L
  refine ⟨Φ, fun n => ?_, hΦ0⟩
  obtain ⟨h, hh, hx⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hA k X p D hX T hT (comb L n)
  refine ⟨h, hh, ?_⟩
  rw [hx _ _ hg, ← Fin.prod_const (D + 1) (lin fun i => (n i : ℝ)), hΦ (fun _ => n)]

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeightsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  first | exact @GlobalTheory.MixHt.arFormExists_of_isMix | exact GlobalTheory.MixHt.arFormExists_of_isMix | (intros; apply GlobalTheory.MixHt.arFormExists_of_isMix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSuccStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.isMixedHeightByInduction_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  first | exact @GlobalTheory.MixHt.Step.isMix_succ | exact GlobalTheory.MixHt.Step.isMix_succ | (intros; apply GlobalTheory.MixHt.Step.isMix_succ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact GlobalTheory.T.isMixedHeightByInduction_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegralsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  first | exact @GlobalTheory.MixHt.exists_isMix_of_arch | exact GlobalTheory.MixHt.exists_isMix_of_arch | (intros; apply GlobalTheory.MixHt.exists_isMix_of_arch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatements

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals hI hR
  refine ⟨GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights hI hE, GlobalTheory.T.arithMixedInterInductive_of_mixedHeights hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', GlobalTheory.T.arithHeight_projectionFormula_every_point k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatementsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalyticStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic : ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := by
  first | exact @GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | exact GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | (intros; apply GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic <;> assumption)
end
end

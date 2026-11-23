module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartBaseLinksOfPrimitiveRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartBaseLinksOfPrimitiveRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealData

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTuple

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem primeToHost_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h PP hP
  rcases hP with hP | hP
  · exact GlobalTheory.LiftScalarCompare.primeToHost h.lev PP hP
  · rw [GlobalTheory.LiftLower.Q_base h.lev] at hP
    simp at hP

end GlobalTheory.LowRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTupleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.badPlacesPrimeToHost_baseTuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  first | exact @GlobalTheory.LowRow.primeToHost_base | exact GlobalTheory.LowRow.primeToHost_base | (intros; apply GlobalTheory.LowRow.primeToHost_base <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowRow

theorem l6m_le_log_lam3_base_place {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ∀ b : ℝ, R.WeakCharacterisation F → R.PThmA → R.PPos → LowTop R.toRealDat b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p, (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p A3.A.v0) := by
  intro b hC hA hP hL hB j p
  by_cases hW : R.Wp3 j p = ⊥
  · rw [hC.scal.abs0 j A3.A.μ0 p hW, Real.log_exp]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hpos : 0 < R.lam3 j A3.A.μ0 p A3.A.v0 := hP.2 j A3.A.μ0 p A3.A.v0
    have heig := hA j A3.A.μ0 p x hx
    exact (hB j).trans (hL j _ x hx0 hpos heig)

end GlobalTheory.LowRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → R.PThmA → R.PPos → LowTop R.toRealDat b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p, (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p A3.A.v0) := by
  first | exact @GlobalTheory.LowRow.l6m_le_log_lam3_base_place | exact GlobalTheory.LowRow.l6m_le_log_lam3_base_place | (intros; apply GlobalTheory.LowRow.l6m_le_log_lam3_base_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlaces

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowOff

theorem le_log_of_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) (m : ℂ) (lam B : ℝ)
    (hlam : 0 < lam) (hm : m ≠ 0) (hg : ⟪w, w⟫_ℂ = ((lam : ℝ) : ℂ) * m) (hl : Real.exp B * m.re ≤ ‖w‖ ^ 2) :
    B ≤ Real.log lam := by
  rw [inner_self_eq_norm_sq_to_K] at hg
  have hg' : ((‖w‖ ^ 2 : ℝ) : ℂ) = ((lam : ℝ) : ℂ) * m := by rw [Complex.ofReal_pow]; exact hg
  have hre := congrArg Complex.re hg'
  have him := congrArg Complex.im hg'
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  have him0 : m.im = 0 := by
    rcases mul_eq_zero.mp him.symm with h | h
    · exact absurd h hlam.ne'
    · exact h
  have hre0 : m.re ≠ 0 := fun h => hm (Complex.ext h him0)
  have hpos : 0 < m.re := by
    have : 0 ≤ lam * m.re := by rw [← hre]; positivity
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right (by linarith) hlam) (Ne.symm hre0)
  rw [Real.le_log_iff_exp_le hlam]
  have : Real.exp B * m.re ≤ lam * m.re := by rw [← hre]; exact hl
  exact le_of_mul_le_mul_right this hpos

theorem partAt_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j p v) :
    R.PartAt F j p v ↔ ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL,
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x x ≠ 0 := Iff.rfl



theorem l6m_le_log_lam3_other_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hC hph hP hG hL hb j p v hv
  by_cases hPA : R.PartAt F j p v
  · rw [partAt_iff, GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hPA
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hG hb ⊢
    obtain ⟨x, hx, hne⟩ := hPA
    exact (hb j).trans (le_log_of_inner_eq _ _ _ _ (hP.2 j A3.A.μ0 p v) hne (hG j v hv p x hx x) (hL j v hv x))
  · rw [hC.scal.abs j p v hv hPA, Real.log_exp]

end GlobalTheory.LowOff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  first | exact @GlobalTheory.LowOff.l6m_le_log_lam3_other_places | exact GlobalTheory.LowOff.l6m_le_log_lam3_other_places | (intros; apply GlobalTheory.LowOff.l6m_le_log_lam3_other_places <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisation

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace R F b hC prim.thmA prim.posScal htop hlow
  have h1 := GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @GlobalTheory.LowRow.lamLow_of_weak | exact GlobalTheory.LowRow.lamLow_of_weak | (intros; apply GlobalTheory.LowRow.lamLow_of_weak <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealDataThree

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow
theorem lamLow_closing_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCusp hWS hSWC hDM hUD hBZ hFD D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH
    hOk hSep hChar hEx hPrim hPhs hStd fw hBar hIo hPins hOne hTie hSizes hLow hNum hPar hStdV
  have hAd : AdelC R.toRealDat F.lv2 :=
    _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV hCusp hWS hSWC hDM hUD hBZ hFD R.toRealDat F.lv2 hPar hStdV
  have hCore := (GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hSep hChar hEx hPrim hPhs).1
  have hPT : PrimeToHost R.toRealDat A3.A.μ0 :=
    GlobalTheory.T.badPlacesPrimeToHost_baseTuple R.toRealDat F.lv2 (GlobalTheory.Core5.of_core hCore)
  exact GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s b C CH hOk hSep hChar hEx hPrim hPhs hStd fw hBar
    hIo hPins hOne hTie hSizes hLow hNum hAd hPT
end GlobalTheory.LowRow
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @_root_.GlobalTheory.LowRow.lamLow_closing_alt | exact _root_.GlobalTheory.LowRow.lamLow_closing_alt | (intros; apply _root_.GlobalTheory.LowRow.lamLow_closing_alt <;> assumption)
end
end
end

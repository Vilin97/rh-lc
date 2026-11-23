module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DsInfCharOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.PhMeasCore
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG

section

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

theorem coef_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H),
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) :=
  fun n ε H _ _ σ v w => coef_smoothOnG n ε H σ v w

end GlobalTheory.CompanionTheory.CoefSmooth
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef

section

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDSSkImpUpqRep

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiscreteSeries

theorem isDS_sk_imp_upqRep (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ :=
  fun h => h

end GlobalTheory.CompanionTheory.DiscreteSeries
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFinSmoothBoth

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KFinSmoothBoth

theorem kFin_smooth_both : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v →
    v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ := by
  intro n ε lam H _ _ σ _ hσ v hv
  have : CompleteSpace H := hσ.1
  have h : Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
    GlobalTheory.Published.KFiniteVectorsUnitary.smoothOnH
      GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
      hσ.2.2.1 hσ.2.2.2.1 hv
  exact ⟨h, h⟩

end GlobalTheory.CompanionTheory.KFinSmoothBoth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.TraceCycWord

theorem etr_succ_eq_sum_cycWord : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ),
    Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  intro A _ n E m
  rw [GlobalTheory.PhiEigenfun.sum_cycWord, Formalism.REAL.etr]
  exact Finset.sum_congr rfl fun c _ => GlobalTheory.PhiEigenfun.epow_eq E (m + 1) c c

end GlobalTheory.TraceCycWord
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCycWordEqEtr

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CycWordTrace

theorem sum_cycWord_eq_etr : ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B),
    ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod
      = Formalism.REAL.etr X (m + 1) := by
  intro B _ n m X
  exact (GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord X m).symm

end GlobalTheory.CompanionTheory.CycWordTrace
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitActGlRel

section

@[expose] public section

open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothVecGl

theorem unitAct_glRel : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ),
    Formalism.REAL.GlRel (fun a b => GlobalTheory.SmoothVecMod.unitAct hσ a b) := by
  intro n ε H _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  intro a b c d
  ext u
  have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
    (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
    n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
  rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
  split_ifs <;> simp [unitAct_coe]

end GlobalTheory.CompanionTheory.SmoothVecGl
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DiscreteSeriesInfinitesimalCharacter

section

@[expose] public section

namespace CompanionTheory.RgDsInf

theorem dsInfChar' : GlobalTheory.Dec.DSInfChar :=
  dsInfChar_of
    (fun V _ _ => GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V)
    GlobalTheory.CompanionTheory.SmoothVecGl.unitAct_glRel
    GlobalTheory.CompanionTheory.CapelliMap.map_qdet_etr
    GlobalTheory.CompanionTheory.CoefWord.eword_coef
    GlobalTheory.CompanionTheory.CycWordTrace.sum_cycWord_eq_etr
    GlobalTheory.CompanionTheory.KFinSmoothBoth.kFin_smooth_both
    GlobalTheory.CompanionTheory.DiscreteSeries.isDS_sk_imp_upqRep
    GlobalTheory.CompanionTheory.CoefSmooth.coef_smooth
    CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end CompanionTheory.RgDsInf
end
end

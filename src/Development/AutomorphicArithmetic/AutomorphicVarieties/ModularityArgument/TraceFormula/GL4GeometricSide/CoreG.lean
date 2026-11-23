module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracInequalityKTypes
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultGOfMultFor
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand
public import Formalism.FormalDegreeBessel.StatementDS
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondLeviFamily
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionActionHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultForOfCapCls

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignOne

section

@[expose] public section

noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dite_eq_left hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapPNeg

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.PairMult

theorem capelliPoly_neg {n : ℕ} (χ : Fin n → ℂ) (Y : ℂ) :
    Formalism.QuantumDeterminants.capP (fun a => -χ a) (-Y) = (-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y := by
  have h : ∀ s : Fin n, -Y + -χ s = (-1 : ℂ) * (Y + χ s) := fun s => by ring
  simp only [Formalism.QuantumDeterminants.capP, h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.CompanionTheory.PairMult
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowRightEqPow

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.PairMult

section Powers

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem epowLeft_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    PositivityTheory.RgBcC.RealD.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [PositivityTheory.RgBcC.RealD.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.RealD.epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem epowRight_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [Formalism.REAL.epow, pow_succ, Matrix.mul_apply, Matrix.of_apply, ih]

theorem etr_eq_gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) :
    Formalism.REAL.etr E m = PositivityTheory.RgBcC.RealD.gelA E m := by
  simp only [Formalism.REAL.etr, PositivityTheory.RgBcC.RealD.gelA, epowLeft_eq_pow, epowRight_eq_pow]

end Powers

end GlobalTheory.CompanionTheory.PairMult
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfAction

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CapClsA

open GlobalTheory.CompanionTheory.PairMult

theorem capOne_newton : CapOne := by
  intro n V _ _ E χ hE hg Y
  refine LinearMap.ext fun v => ?_
  have h := GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE
    (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v
  simpa [Formalism.QuantumDeterminants.capP] using h

theorem dualCap_newton : DualCap := by
  intro n V _ _ E χ hE hg Y
  obtain ⟨hF, hq⟩ := GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  have h := capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)
  have hq' := hq (-Y + ((n : ℂ) - 1) / 2)
  have harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by ring
  rw [harg] at hq'
  have hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; simp
  have h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V) := by
    rw [← hq', ← capelliPoly_neg]
    exact h
  calc Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
      = ((-1 : ℂ) ^ n) • (((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)) := by
        rw [smul_smul, hne, one_smul]
    _ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
        rw [h2, smul_smul, ← mul_assoc, hne, one_mul]

theorem capCls_of_actUU : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := fun hAct =>
  GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton

end GlobalTheory.CompanionTheory.CapClsA
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliClassificationOfActionStatement

section

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.capelli_classification_of_action : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := by
  first | exact @GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | exact GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU | (intros; apply GlobalTheory.CompanionTheory.CapClsA.capCls_of_actUU <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultiplicityFormulaHolds

section

@[expose] public section

namespace PositivityTheory.RgBcC.RealD

theorem multiplicity_formula_holds : MultFor :=
  multFor_of_capCls (GlobalTheory.T.capelli_classification_of_action injective_decomposition_action_holds.2.2)

end PositivityTheory.RgBcC.RealD
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.CoreG

section

@[expose] public section

open PositivityTheory.RgBcC.RealD

theorem UpperTheory.V.Z.GSp4Splitting.coreG : CoreG := coreG_of countG_holds (multG_of_multFor multiplicity_formula_holds) GlobalTheory.CompanionTheory.SignLine.signOne
end
end

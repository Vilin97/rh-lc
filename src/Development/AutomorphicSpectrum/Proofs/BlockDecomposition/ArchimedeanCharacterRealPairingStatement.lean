module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [_root_.NumberField.IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairing

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairingStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.archimedean_character_real_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.JSPair.exists_pairing | exact GlobalTheory.CompanionTheory.JSPair.exists_pairing | (intros; apply GlobalTheory.CompanionTheory.JSPair.exists_pairing <;> assumption)
end
end

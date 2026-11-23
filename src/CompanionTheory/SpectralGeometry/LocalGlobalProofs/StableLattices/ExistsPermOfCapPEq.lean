module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind

section

@[expose] public section

open Formalism.REAL Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef.CapLW

section perm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in
theorem glRel_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) :
    GlRel fun a b => E (σ a) (σ b) := by
  intro a b c d
  simpa only [σ.injective.eq_iff] using hE (σ a) (σ b) (σ c) (σ d)

theorem qdet_perm {E : Fin n → Fin n → A} (hE : GlRel E) (σ : Equiv.Perm (Fin n)) (u : ℂ) :
    qdet (fun a b => E (σ a) (σ b)) u = qdet E u := by
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => if c = σ a then 1 else 0
  let Q : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun b d => if d = σ b then 1 else 0
  have hQP : Q * P = 1 := by
    ext b a
    simp [P, Q, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have h := (Formalism.FourierDecayAlt.P.contractions_covariant A n E P Q hE hQP (mul_eq_one_comm.1 hQP) u 0 0 0 0).1
  rw [← h]
  congr 1
  funext a b
  simp [Formalism.FourierDecayAlt.Q.Econj, P, Q, ite_smul]

end perm

section order

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end order

end GlobalTheory.CompanionTheory.HolCoef.CapLW
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq

section

@[expose] public section

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
end
end
end

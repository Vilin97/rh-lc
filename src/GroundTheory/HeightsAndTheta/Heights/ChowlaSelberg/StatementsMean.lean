import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsWitness

private abbrev periodLatticeEnd (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  zero_mem' z _ := by rw [zero_mul]; exact zero_mem _
  one_mem' z hz := by simpa only [one_mul] using hz
  add_mem' ha hb z hz := by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
  neg_mem' ha z hz := by rw [neg_mul]; exact neg_mem (ha z hz)
  mul_mem' ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)

private abbrev cmRingOfEmbedding {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℂ) : Subring ℂ :=
  (σ.comp (algebraMap (NumberField.RingOfIntegers K) K)).range
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

def PeriodLatticeCM.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ s : F.k →+* ℂ, ∃ L : PeriodPair,
    F.periodLattice s = L.lattice ∧ periodLatticeEnd L = cmRingOfEmbedding (F.restrict s)

def IdealInvArea.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), periodLatticeEnd L = cmRingOfEmbedding σ →
    ∀ 𝔞 : (Ideal (𝓞 K))⁰,
      latticeArea (idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice) =
        latticeArea L.lattice / (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

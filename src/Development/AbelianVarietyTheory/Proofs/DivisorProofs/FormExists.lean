import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionCommutesWithEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionUpperLeftCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerRightCommutesEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact GlobalTheory.T.fock_action_upper_left_commutes_embedding P Q R h k a a' G
  · exact GlobalTheory.T.fock_action_commutes_with_embedding P Q R h k a b' G
  · exact GlobalTheory.T.fock_action_lower_left_commutes_embedding P Q R h k a' b G
  · exact GlobalTheory.T.fock_action_lower_right_commutes_embedding P Q R h k b b' G

theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

end GlobalTheory.CharPair

end

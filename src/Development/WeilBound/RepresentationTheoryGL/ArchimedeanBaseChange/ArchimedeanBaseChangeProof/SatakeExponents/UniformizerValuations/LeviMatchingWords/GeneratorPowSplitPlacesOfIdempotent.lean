module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOfStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Mathlib.Tactic.Basify
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorusStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Mathlib.NumberTheory.NumberField.CMField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSecondBlockOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOfStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.matching_identity_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOfStatement

section

section


theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.MuInertPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem delta_indep {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) : delta w μ Q₁ Q₂ = delta w μ' Q₁ Q₂ := by
  simp only [delta, hw, if_false]

theorem match_indep {n a b : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ) : Match n a b w μ f φ ↔ Match n a b w μ' f φ := by
  unfold Match
  simp only [delta_indep hw μ μ']

theorem muInert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  intro E _ _ _ n a b w hw μ μ' f φ
  exact match_indep hw μ μ' f φ

end GlobalTheory.CompanionTheory.MuInertPlace
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInertStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.multiplicity_inert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  first | exact @GlobalTheory.CompanionTheory.MuInertPlace.muInert | exact GlobalTheory.CompanionTheory.MuInertPlace.muInert | (intros; apply GlobalTheory.CompanionTheory.MuInertPlace.muInert <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyConjDiagonal

section

section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

namespace GlobalTheory.CompanionTheory.UnitarySide

theorem charpoly_conj_diagonal {K : Type} [Field K] {n : ℕ} (c D g : GL (Fin n) K) (d : Fin n → K)
    (hD : D.val = Matrix.diagonal d) (hg : g = c * D * c⁻¹) :
    g.val.charpoly = ∏ i, (X - C (d i)) := by
  subst hg
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hD,
    Matrix.charpoly_diagonal]

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.CompanionTheory.UnitarySide
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus

section

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MLM Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SepPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem zpow_mul_inj {w : Pl E} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a c : ℤ} {u v : w.adicCompletion E}
    (hu : Valued.v u = 1) (hv : Valued.v v = 1)
    (h : ((ϖ ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * u = ((ϖ ^ c : (w.adicCompletion E)ˣ) : w.adicCompletion E) * v) :
    a = c := by
  have e := congrArg Valued.v h
  rw [map_mul, map_mul, hu, hv, mul_one, mul_one] at e
  have h1 : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.BorelUMod.v_eq_exp ϖ.ne_zero, hϖ.1]
  have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by
    rw [h1]; exact WithZero.exp_ne_zero
  have hne : Valued.v (ϖ : w.adicCompletion E) ≠ 1 := by
    rw [h1, ← WithZero.exp_zero]
    intro h2
    have := WithZero.exp_injective h2
    omega
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀] at e
  exact zpow_right_injective₀ (zero_lt_iff.2 h0) hne e

theorem separable_of_fU {w : Pl E} {b : GLw n w} {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {l : Fin (n / 2) → ℤ}
    (hl : Cone l) {γ : UL n w} (h : fU n w b ϖ l γ ≠ 0) : γ.1.val.charpoly.Separable := by
  have hy := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).1
  have h' : ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 := by
    by_contra hc
    exact h (if_neg hc)
  obtain ⟨x, hx, z, hz, e⟩ := h'
  obtain ⟨x', hx', ex⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  obtain ⟨z', hz', ez⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
  have ex' : x.1 = b * x' * b⁻¹ := ex.symm
  have ez' : z.1 = b * z' * b⁻¹ := ez.symm
  have hδ : dcos n w (tdiag ϖ (wexp n l)) (b⁻¹ * γ.1 * b) ≠ 0 := by
    have : ∃ p ∈ iwGL n w, ∃ q ∈ iwGL n w, b⁻¹ * γ.1 * b = p * tdiag ϖ (wexp n l) * q :=
      ⟨x', hx', z', hz', by rw [e, ex', ez']; group⟩
    simp [dcos, this]
  obtain ⟨m, -, τ, hτ, em⟩ := GlobalTheory.CompanionTheory.IwahoriContraction.contr_id w ϖ hϖ n (wexp n l) hy _ hδ
  have hval : (tdiag ϖ (wexp n l) * τ).val = Matrix.diagonal fun i =>
      ((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * τ.val i i := by
    have hτd : τ.val = Matrix.diagonal fun i => τ.val i i := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · rw [hτ.1 i j hij, Matrix.diagonal_apply_ne _ hij]
    rw [Units.val_mul, GlobalTheory.CompanionTheory.FUMulPf.tdiag_val, hτd, Matrix.diagonal_mul_diagonal]
    simp
  have hg : γ.1 = (b * m) * (tdiag ϖ (wexp n l) * τ) * (b * m)⁻¹ := by
    rw [← em]; group
  rw [GlobalTheory.CompanionTheory.UnitarySide.charpoly_conj_diagonal (b * m) _ γ.1 _ hval hg, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  exact hy.injective (zpow_mul_inj hϖ (hτ.2 i) (hτ.2 j) hij)

theorem sepPowT : SepPowT := by
  intro E _ _ _ hU n d hd hm m w hT y hy
  obtain ⟨hs, hb, hϖ, hx⟩ := hm.T w hT
  have hx' : ∀ j, StrictAnti (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j) ∧ Cone (lOf (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w j)) :=
    fun j => hx j.1 j.2
  obtain ⟨J', _, c', x', hx'', e1, -⟩ := GlobalTheory.CompanionTheory.MatchPow.pow_claim GlobalTheory.CompanionTheory.FUMulPf.fuMul GlobalTheory.CompanionTheory.DcosProduct.dcosMul hU hs 0
    hb hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w) hx' m
  have hKU : d.KU w = iwU n w (d.b w) := by simp [LocData.KU, hT]
  have hG : d.gU (m + 1) w y = (((iwU n w (d.b w)).relIndex (KL n w) : ℕ) : ℂ) ^ (m + 1) *
      (GlobalTheory.CompanionTheory.MatchPow.alpha n w (d.b w) ^ m * ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y) := by
    unfold LocData.gU
    rw [hKU, GlobalTheory.CompanionTheory.MatchLMPlaces.unitary_function_at_T d hT, GlobalTheory.CompanionTheory.MatchLMPlaces.lpow_scale, e1]
  rw [hG] at hy
  have hsum : ∑ j, c' j * fU n w (d.b w) (d.ϖ w) (lOf (x' j)) y ≠ 0 := fun h0 => hy (by rw [h0]; simp)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact separable_of_fU hϖ (hx'' j).2 (right_ne_zero_of_mul hj)

end GlobalTheory.CompanionTheory.SepPow

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorusStatement

section

section


theorem _root_.GlobalTheory.T.separable_power_torus : PositivityTheory.Rg.BcB.F.MLM.SepPowT := by
  first | exact @GlobalTheory.CompanionTheory.SepPow.sepPowT | exact GlobalTheory.CompanionTheory.SepPow.sepPowT | (intros; apply GlobalTheory.CompanionTheory.SepPow.sepPowT <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent

section

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.MLM

theorem matchLMIdOf : MatchLMIdOf := GlobalTheory.T.matching_identity_of
theorem matchLMUnitOf : MatchLMUnitOf := GlobalTheory.T.matching_unit_of

theorem muInert : MuInert := GlobalTheory.T.multiplicity_inert
theorem regPowT : RegPowT := GlobalTheory.T.regular_power_torus
theorem sepPowT : SepPowT := GlobalTheory.T.separable_power_torus
theorem ctStar : CtStar := GlobalTheory.T.constant_term_star
theorem matchLMWordSOf : MatchLMWordSOf := GlobalTheory.T.match_levi_words_of

end PositivityTheory.Rg.BcB.F.MLM
end
end

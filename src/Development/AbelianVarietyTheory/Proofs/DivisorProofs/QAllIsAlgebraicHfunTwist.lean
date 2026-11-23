module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedWeierstrassPTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansionStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraicStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by
  first | exact @GlobalTheory.HilbFam.hser_coeff_isAlgebraic | exact GlobalTheory.HilbFam.hser_coeff_isAlgebraic | (intros; apply GlobalTheory.HilbFam.hser_coeff_isAlgebraic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValueStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.partialZeta_constTerm_eq_rational_value : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.constTerm_eq_zetaVal | exact GlobalTheory.HilbFam.constTerm_eq_zetaVal | (intros; apply GlobalTheory.HilbFam.constTerm_eq_zetaVal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficients

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L →
    ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ),
    QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  intro hE F _ _ _ hf s N L hs hN hL z hz κ Ch hCh
  obtain ⟨c, hc, halg⟩ := hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have hconst := GlobalTheory.T.partialZeta_constTerm_eq_rational_value F (2 * s) z _ Z (by omega) hz hZ
  have ha₀ : IsAlgebraic ℚ ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) := by
    rw [hconst]
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) _
  exact ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN (even_two_mul s) ha hL hc,
    fun n ↦ GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic F (2 * s) 𝔞 𝔟 _ a x s N κ c n rfl ha ha₀ halg⟩

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficientsStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ), QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | exact GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | (intros; apply GlobalTheory.HilbFam.qAll_isAlgebraic_hfun <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N x, fun k => ?_⟩, ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsionStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

theorem _root_.GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧ (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  first | exact @GlobalTheory.WpFam.qAll_isAlgebraic_torsion | exact GlobalTheory.WpFam.qAll_isAlgebraic_torsion | (intros; apply GlobalTheory.WpFam.qAll_isAlgebraic_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllIsAlgebraicHfunTwist

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (y : Fin 2 → ZMod N), y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (IsAlgebraic ℚ) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL z hz κ y hy α
  have hy' : vmul y α ≠ 0 := fun h => hy (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.2.1 y α).1 h)
  exact GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients hE F hF s N _ hs (Nat.pos_of_ne_zero (NeZero.ne N)) (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L _ hL) z hz κ _
    ((GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion N (vmul y α)).2.2 hy')

end GlobalTheory.HilbFam
end
end

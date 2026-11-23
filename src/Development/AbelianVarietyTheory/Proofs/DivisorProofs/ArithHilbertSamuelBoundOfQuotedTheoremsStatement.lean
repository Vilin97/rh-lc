module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSectionsStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRightInvOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExplicitArithmeticHilbertSamuelBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Mathlib.NumberTheory.Harmonic.Bounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurface

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuel

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem bertiniNF_of_bertini (h : Bertini) : BertiniNF := by
  intro F _ _ T hg hb δ f hf
  obtain ⟨hδ, Q, hQ, hs⟩ := h F T hg hb δ f hf
  exact ⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩

theorem bertiniNumberField_of_hilbertSamuel : GlobalTheory.HSCore.Quoted → BertiniNF :=
  fun hq => bertiniNF_of_bertini (GlobalTheory.T.bertini_simple_zeros_generic_sections hq)

end GlobalTheory.HSShort
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuelQuotedStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ : Quoted → BertiniNF := by
  first | exact @GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | exact GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel | (intros; apply GlobalTheory.HSShort.bertiniNumberField_of_hilbertSamuel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormHeightEqHt

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightTieProof

theorem formHeight_eq_ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) :
    formHeight δ w A f = ht w A f + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  have hr : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold ht formHeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  field_simp
  ring

theorem ht_pow (hM : HtMul) {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (e : ℕ) :
    ht w A (f ^ e) = e * ht w A f := by
  induction e with
  | zero =>
    have := (hM F B N n w A Λ hL).2 1 one_ne_zero
    simpa using this
  | succ k ih =>
    have hk : IsMultiHomogeneous (k • a) (f ^ k) :=
      isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 ha).pow k)
    rw [pow_succ, (hM F B N n w A Λ hL).1 (k • a) a _ _ (pow_ne_zero k hf) hf hk ha, ih]
    push_cast; ring

theorem heightTie : HtMul → HeightTie := by
  intro hM F _ _ T Λ hL h hh d e f c hf he hc
  obtain ⟨d', f', -, hf', e'⟩ := hh
  obtain ⟨rfl, c', hc', rfl⟩ := hf.isChowFormInt.unique hf'.isChowFormInt
  have hf0 := hf.isChowFormInt.ne_zero
  have hd := hf.isChowFormInt.pos
  rw [HeightUnique.formHeight_C_mul hL.pos d hL.spans hL.det hf0 hf.homog hc', formHeight_eq_ht] at e'
  have hpow : IsMultiHomogeneous (e • fun _ => d) (f ^ e) :=
    isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 hf.homog).pow e)
  have key : ht T.w T.A (C c * f ^ e) = e * ht T.w T.A f := by
    unfold ht
    rw [HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det (pow_ne_zero e hf0) hpow hc]
    exact ht_pow hM hL hf0 hf.homog e
  have hD : (0 : ℝ) < (T.D : ℝ) + 1 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have eq1 : ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) =
      h - (harmonic (T.N - 1) : ℝ) / 2 := by
    rw [key, div_eq_iff (by push_cast; positivity)]
    push_cast
    push_cast at e'
    have : ht T.w T.A f = ((T.D : ℝ) + 1) * d * h - ((T.D : ℝ) + 1) * d * (harmonic (T.N - 1) : ℝ) / 2 := by
      linarith
    rw [this]; ring
  refine ⟨eq1, ?_⟩
  rw [eq1]

  have hNn : T.N ≤ T.n := by
    have h1 := finrank_range_le_card (R := F) (b := T.w.col)
    rw [Set.finrank, hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hH : (harmonic (T.N - 1) : ℝ) ≤ 1 + Real.log (T.N - 1 : ℕ) := harmonic_le_one_add_log _
  have hlog : Real.log (T.N - 1 : ℕ) ≤ Real.log T.n := by
    rcases Nat.eq_zero_or_pos (T.N - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : T.N - 1 ≤ T.n))
  linarith

end GlobalTheory.HeightTieProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeLowerBoundTopLatticeOffHypersurfaceStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface : SlopeBound := by
  first | exact @GlobalTheory.HSShort.SlopeTop.slopeBound | exact GlobalTheory.HSShort.SlopeTop.slopeBound | (intros; apply GlobalTheory.HSShort.SlopeTop.slopeBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHilbertSamuelBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem geoBound_of_quoted' : Quoted → GeoBound := fun hQ =>
  GlobalTheory.T.explicit_arithmetic_hilbertSamuel_bound hQ (GlobalTheory.T.bertiniNumberField_of_hilbertSamuel₂ hQ) (GlobalTheory.HeightTieProof.heightTie GlobalTheory.HSShort.htMul) GlobalTheory.T.slopeLowerBound_topLattice_offHypersurface

end GlobalTheory.HSShort
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelBoundOfQuotedTheoremsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

theorem _root_.GlobalTheory.T.arithmeticHilbertSamuelBound : Quoted → GeoBound := by
  first | exact @GlobalTheory.HSShort.geoBound_of_quoted' | exact GlobalTheory.HSShort.geoBound_of_quoted' | (intros; apply GlobalTheory.HSShort.geoBound_of_quoted' <;> assumption)
end
end

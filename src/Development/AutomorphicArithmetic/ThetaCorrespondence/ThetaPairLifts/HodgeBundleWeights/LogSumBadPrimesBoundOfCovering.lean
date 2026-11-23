module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds2
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.RamEq
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
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.BadLog

section

@[expose] public section

open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.sum_log_bad_le :
    ∀ {φ : Frame} (H : HostAx φ) (M : ℕ) (S : Finset ℕ), M ≠ 0 →
      (∀ p ∈ S, p.Prime ∧ (p = 2 ∨ p = H.d ∨ p ∣ (discr H.E).natAbs ∨ p ∣ M)) →
        ∑ p ∈ S, Real.log p ≤ 2 * Real.log H.rd + Real.log M := by
  intro φ H M S hM hS
  have hD : (discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero H.E)
  obtain ⟨hA, hB, -⟩ := UpperTheory.HF.ram_eq H
  have hsub : S ⊆ H.ram ∪ M.primeFactors := by
    intro p hp
    obtain ⟨hpp, h⟩ := hS p hp
    rw [Finset.mem_union]
    rcases h with h | h | h | h
    · exact Or.inl ((hA p).2 (Or.inl (h ▸ hB)))
    · exact Or.inl ((hA p).2 (Or.inr (Or.inr h)))
    · exact Or.inl (Nat.mem_primeFactors.2 ⟨hpp, h, hD⟩)
    · exact Or.inr (Nat.mem_primeFactors.2 ⟨hpp, h, hM⟩)
  have h1 : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    simpa using (UpperTheory.HF.rad_bounds2 H).1 0 1 le_rfl zero_le_one
  have h2 : ∑ l ∈ M.primeFactors, Real.log l ≤ Real.log M := by
    have hne : ∀ l ∈ M.primeFactors, (l : ℝ) ≠ 0 := fun l hl =>
      Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hl).ne_zero
    rw [← Real.log_prod hne, ← Nat.cast_prod]
    refine Real.log_le_log ?_ ?_
    · exact Nat.cast_pos.2 (Finset.prod_pos fun l hl => (Nat.prime_of_mem_primeFactors hl).pos)
    · exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.prod_primeFactors_dvd M))
  have h3 : ∑ p ∈ S, Real.log p ≤ ∑ p ∈ H.ram ∪ M.primeFactors, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.log_natCast_nonneg p
  have h4 := Finset.sum_union_inter (s₁ := H.ram) (s₂ := M.primeFactors) (f := fun p : ℕ => Real.log p)
  have h5 : 0 ≤ ∑ p ∈ H.ram ∩ M.primeFactors, Real.log p :=
    Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogSumBadPrimesBoundOfCovering

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

noncomputable section
namespace GlobalTheory.BadLogCov
theorem log_sum_bad_primes_le_sq : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  intro _
  refine ⟨37, by norm_num, fun D T hT j hj Y e o hY Lb hL hM hE hfr => ?_⟩
  have hQ := hT.pins
  have hM0 : Y.d.l₂.M ≠ 0 := by have := Y.d.l₂.three_le; omega
  have h1 := UpperTheory.KR.sum_log_bad_le D.host.toHostAx Y.d.l₂.M (badPrimes T.Q.H Y.d.l₂) hM0 fun p hp => by
    obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
    refine ⟨hp, ?_⟩
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hQ.1.1))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · rw [hY.lev.2] at h'
      exact absurd (Nat.dvd_one.1 h') hp.ne_one
  have hrd : Real.log D.host.rd ≤ fieldSz D.host.E := by
    refine le_trans (le_of_eq ?_) (log_rd_le_fieldSz D.host.E)
    unfold Formalism.HC.HostRaw.rd
    rw [Real.log_rpow (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E))]; ring
  have hsum : GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ 37 * Lb := by
    refine le_trans h1 ?_; linarith
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1' := D.R.two_le_m
  have h2' := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hX : Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have a : Lb ≤ (D.R.f : ℝ) * D.R.r * Lb := le_mul_of_one_le_left (by linarith) hfr1
    have b : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * Lb := hL.trans a
    nlinarith
  linarith
end GlobalTheory.BadLogCov
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  first | exact @_root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | exact _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq | (intros; apply _root_.GlobalTheory.BadLogCov.log_sum_bad_primes_le_sq <;> assumption)
end
end
end

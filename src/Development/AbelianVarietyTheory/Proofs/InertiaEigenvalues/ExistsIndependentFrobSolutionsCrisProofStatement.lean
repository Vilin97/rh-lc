module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResiduesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesOntoAndIndependentZerosStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeries

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSerExist

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have h3 : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by push_cast; rfl
  rw [h3] at h
  rw [h]; exact h2

theorem exists_zeros (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (hh : 2 ≤ h) (hμ : μ ≠ 0) :
    ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧
      (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧
      ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) →
        c = 0 := by
  have h1 : 1 ≤ h := le_trans (by norm_num) hh
  obtain ⟨τ, hsurj, x, hxS, hxη, hxind⟩ := GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros l h μ h1 hμ
  let η : Fl l → Unit → ℂ_[l] := fun y _ => ∑ i : Fin h, μ i * lam h i y
  let S : Set (Fl l) := {y | ‖sh y‖ ≤ ‖(l : ℂ_[l])‖}
  have hlift := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fl l) Unit η (fun _ => τ) S
    (fun t ht => by
      obtain ⟨y, hy, hyt⟩ := hsurj (t ()) (ht ())
      exact ⟨y, hy, fun i => by cases i; exact hyt⟩)
  have hy : ∀ a : Fin h, ∃ z : ℕ → Fl l, z 0 = x a ∧ (∀ k, z k ∈ S) ∧
      ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (z k) i) 0 :=
    fun a => hlift (x a) (hxS a) (fun _ => hxη a)
  choose y hy0 hyS hysum using hy
  have hr : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  have hyS' : ∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖ := fun a k => hyS a k
  refine ⟨y, hyS', ?_, ?_⟩
  · intro a
    have hs : ∀ i : Fin h, HasSum (fun k : ℕ => μ i * ((l : ℂ_[l]) ^ k * lam h i (y a k)))
        (μ i * abelian₂ h i (y a)) := fun i =>
      ((GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i ‖(l : ℂ_[l])‖ (y a) h1 hr (hyS' a)).1).mul_left (μ i)
    have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
    have hsum' : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y a k) ())
        (∑ i : Fin h, μ i * abelian₂ h i (y a)) := by
      convert hsum using 1
      funext k
      dsimp [η]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    exact hsum'.unique (hysum a ())
  · refine GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h h ‖(l : ℂ_[l])‖ y hh (norm_nonneg _) hr hyS' ?_
    intro n hn a
    simp only [hy0] at hn
    exact hxind n hn a

end GlobalTheory.PSerExist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeriesStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSerExist.exists_zeros | exact GlobalTheory.PSerExist.exists_zeros | (intros; apply GlobalTheory.PSerExist.exists_zeros <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProof

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per
theorem GlobalTheory.PMon.exI_of_ser_core (hser : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧ ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y) (hcore : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Formalism.Per.Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0) : ExI := by
  intro l _ P AI T h hh μ hμ hne
  obtain ⟨S, θ, hS, hker, hq, hb⟩ := hser l P AI T
  let μ' : Fin h → ℂ_[l] := fun i => θ ⟨μ i, (hS _).2 (hμ i)⟩
  have hμ' : μ' ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    exact hi ((hker ⟨μ i, (hS _).2 (hμ i)⟩).1 (congrFun h0 i))
  obtain ⟨y, hy, hz, hind⟩ := hcore l h μ' hh hμ'
  choose b hplus hφ hev using fun a => hb h _ (y a) hh GlobalTheory.RingBasics.norm_p_lt (hy a)
  choose hm hev using hev
  choose hq0 hq using hq
  refine ⟨b, hplus, hφ, ?_, fun a => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have : c = 0 := by
      refine hind c fun j _ => ?_
      have e : ∀ x : P.R.B, ev P j x = P.ιB ((P.φB ^ j) x) := fun x => by
        simp only [ev, AlgHom.coe_pow]
      have h1 : (∑ a, (⟨_, hq0 (c a)⟩ : S) * ⟨_, hm a j⟩) = 0 := by
        apply Subtype.ext
        have := congrArg (fun x => P.ιB ((P.φB ^ j) x)) hc

        simp only [map_sum, map_smul, map_zero] at this
        simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, e, ZeroMemClass.coe_zero]
        simpa only [Algebra.smul_def] using this
      have h2 := congrArg θ h1

      rw [map_sum, map_zero] at h2
      simpa only [map_mul, hq, hev] using h2
    exact fun i => congrFun this i
  · have h2 : θ (∑ i : Fin h, (⟨μ i, (hS _).2 (hμ i)⟩ : S) * ⟨_, hm a i⟩) = 0 := by

      rw [map_sum]
      simpa only [map_mul, hev] using hz a
    have := (hker _).1 h2
    simpa only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul] using this

theorem GlobalTheory.PMon.exI_main : ExI := GlobalTheory.PMon.exI_of_ser_core GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentFrobSolutionsCrisProofStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.existsIndependentFrobSolutionsCris_proof : ExI := by
  first | exact @GlobalTheory.PMon.exI_main | exact GlobalTheory.PMon.exI_main | (intros; apply GlobalTheory.PMon.exI_main <;> assumption)
end
end

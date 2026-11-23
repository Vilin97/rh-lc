module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.HalfUnit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.halfUnit :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (p : GlobalTheory.ChiGrid.Pair T) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ c : ℕ, (∀ w ∈ P, ((c : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ u ∈ pairLat G p, IsHalf e u → ∃ u' ∈ pairLat G p, IsHalf e u' ∧ c • u' = u := by
  intro D T L sc G p P e he c hc u hu hhalf
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hc0 : c = 0
  · subst hc0
    have hS : ∑ PP ∈ P, es PP = 0 :=
      Finset.sum_eq_zero fun PP hPP => (hc PP hPP (by simp)).elim
    have hu0 : u = 0 := by
      ext i j
      have h := hhalf i j
      rw [hS, zero_mul] at h
      exact h.symm
    subst hu0
    exact ⟨0, (pairLat G p).zero_mem, fun i j => by simp, by simp⟩
  · have hx : ((c : 𝓞 D.host.E)) ≠ 0 := by exact_mod_cast hc0
    let w : AE D := (∑ PP ∈ P, es PP) * incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹
    have hw : finPart D w ∈ intAE D := by

      simp only [w, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ ?_
      intro PP hPP
      by_contra hn
      exact hc PP hPP (((hes PP hPP).2 _ hx).mpr hn)
    have h1 : incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← map_mul]
      have hce : (((c : 𝓞 D.host.E) : D.host.E)) = (c : D.host.E) := by simp
      rw [hce, inv_mul_cancel₀ (by exact_mod_cast hc0), map_one]
    have hcw : (c : AE D) * w = ∑ PP ∈ P, es PP := by
      calc (c : AE D) * w
          = (∑ PP ∈ P, es PP) * (incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D)) := by
            simp only [w]; ring
        _ = ∑ PP ∈ P, es PP := by rw [h1, mul_one]
    refine ⟨w • u, GlobalTheory.LatticeStable.smul_mem_latO _ _ _ _ _ _ w hw u hu, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm _ w, mul_assoc, hhalf i j]
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [← mul_assoc, hcw, hhalf i j]
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepthDrop

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mx_eq_of_nsmul_eq_of_ne_zero {D : D7} {m n : ℕ} (c : ℕ) (hc : c ≠ 0) {x y : Mx D m n}
    (h : c • x = c • y) : x = y := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h1
  have hF : ((c : ↥D.host.F)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← Nat.cast_smul_eq_nsmul (↥D.host.F), ← Nat.cast_smul_eq_nsmul (↥D.host.F)] at h1
  calc x i j = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • x i j) := (inv_smul_smul₀ hF _).symm
    _ = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • y i j) := by rw [h1]
    _ = y i j := inv_smul_smul₀ hF _

theorem UpperTheory.WildA.depthDrop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p) (l : ℕ), l.Prime → (∀ w ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ k : ℕ, 0 < k → IsCosetDatum k d → ∃ k' : ℕ, 0 < k' ∧ ¬ l ∣ k' ∧ IsCosetDatum k' d := by
  intro D T L sc G t p d l hl hP k hk hcos
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hcos
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' l hl.one_lt.ne'
  have hc : ∀ w ∈ d.P, (((l ^ a : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw h
    rw [Nat.cast_pow] at h
    exact hP w hw (w.isPrime.mem_of_pow_mem _ h)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hhalf : ∀ (c : ℕ) (u : Mx D (G.pT p).rank (G.pS p).rank), IsHalf d.e u → IsHalf d.e (c • u) := by
    intro c u hu i j
    simp only [Matrix.smul_apply, mul_smul_comm, hu i j]
  obtain ⟨v, hvL, hvH, hv⟩ :=
    UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc _ hkx (hhalf _ _ hx₀)
  have hmx : m • x₀ = v := by
    apply mx_eq_of_nsmul_eq_of_ne_zero (l ^ a) (pow_ne_zero _ hl.ne_zero)
    rw [hv, smul_smul]
  refine ⟨m, hm0, hm, x₀, hx₀, by rw [hmx]; exact hvL, ?_⟩
  rw [hfn]
  congr 1
  ext x
  simp only [GlobalTheory.RowTest.halfCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, huH, rfl⟩
    refine ⟨(l ^ a) • u, AddSubgroup.nsmul_mem _ hu _, hhalf _ _ huH, ?_⟩
    rw [smul_smul, mul_comm m]
  · rintro ⟨u, hu, huH, rfl⟩
    obtain ⟨u', hu', hu'H, rfl⟩ := UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc u hu huH
    exact ⟨u', hu', hu'H, by rw [smul_smul, mul_comm m]⟩
end
end

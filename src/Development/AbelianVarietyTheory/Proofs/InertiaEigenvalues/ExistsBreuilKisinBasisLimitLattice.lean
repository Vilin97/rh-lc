module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfExistsMulEqPowSmulOfModLPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfRightInverseUpToPowModLPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatingLatticesTransitionMatrixModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPoles
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeApproximationMittagLefflerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorsInvertibleBasisOverOEStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SaturatedAinfLatticeFreeOverBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedMatrixCongruenceLiftSequenceStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (T A0 A0' : Matrix (Fin d) (Fin d) (WCb l)) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T.map (frobW l) = T * A0 → A0 * A0' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T) → Y.map (inclW l) = inclW l τ ^ N • T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → ∃ F : Pre bk N d ρ, F.T = T := by
  first | exact @GlobalTheory.BKLim.pre_of_etale | exact GlobalTheory.BKLim.pre_of_etale | (intros; apply GlobalTheory.BKLim.pre_of_etale; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverse

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.descend_rightInverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  intro l _ K bk τ hτ M
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB M
  obtain ⟨t, ht⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  refine ⟨r, fun d d' n R a h => ?_⟩
  refine ⟨∑ k ∈ t.support, t k • (a.map (TB.c k)), fun i j => ?_⟩
  have hl : ∀ k (y : Ainf l), TB.c k ((l : Ainf l) ^ n * y) = (l : bk.S) ^ n * TB.c k y := by
    intro k y
    have e : (l : Ainf l) ^ n = bk.ev ((l : bk.S) ^ n) := by rw [map_pow, map_natCast]
    rw [e, TB.c_mul]
  obtain ⟨y, hy⟩ := h i j
  rw [Matrix.sub_apply] at hy
  have hy' := sub_eq_iff_eq_add.1 hy
  have hG : (R * ∑ k ∈ t.support, t k • (a.map (TB.c k))) i j = ∑ k ∈ t.support, t k * TB.c k ((R.map bk.ev * a) i j) := by

    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Finset.mul_sum, map_sum, TB.c_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sub_apply, hG, hy']
  simp only [map_add (f := _), hl, mul_add, Finset.sum_add_distrib]
  refine ⟨∑ k ∈ t.support, t k * TB.c k y, ?_⟩
  rw [← ht]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finsupp.sum, Finset.mul_sum]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero, sub_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_right_inverse_mod_pow_of_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  first | exact @GlobalTheory.BKLim.descend_rightInverse | exact GlobalTheory.BKLim.descend_rightInverse | (intros; apply GlobalTheory.BKLim.descend_rightInverse; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnit

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem GlobalTheory.ChangeEtaleBasis.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  intro l _ K bk d ρ T0 Wm Wm' A0 A0' hT0 hA0 hA0' hfr hAA hW hW' hWW
  have hO := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → Wm.map (galW l (g : GQ l)) = Wm := by
    intro g hg
    exact Matrix.ext fun i j => by
      simp only [Matrix.map_apply]
      exact hO.2.2.2.2.2.1 g hg _ (hW i j)
  have hfrob : ∀ M : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → ∀ i j, M.map (frobW l) i j ∈ bk.OE := by
    intro M hM i j
    exact hO.2.2.2.2.2.2 _ (hM i j)
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M i j ∈ bk.OE) → (∀ i j, N i j ∈ bk.OE) → ∀ i j, (M * N) i j ∈ bk.OE := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ (fun k _ => Subring.mul_mem _ (hM i k) (hN k j))
  have hW'W : Wm' * Wm = 1 := mul_eq_one_comm.mp hWW
  refine ⟨?_, Wm' * A0 * Wm.map (frobW l), Wm'.map (frobW l) * A0' * Wm, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hmap : (T0 * Wm).map (galW l (g : GQ l)) = T0.map (galW l (g : GQ l)) * Wm.map (galW l (g : GQ l)) :=
      Matrix.map_mul (f := ((galW l (g : GQ l)) : WCb l →+* WCb l))
    rw [hmap, hgal g hg, ← Matrix.mul_assoc, hT0 g hg]
  · exact hmul _ _ (hmul _ _ hW' hA0) (hfrob _ hW)
  · exact hmul _ _ (hmul _ _ (hfrob _ hW') hA0') hW
  · have hmap : (T0 * Wm).map (frobW l) = T0.map (frobW l) * Wm.map (frobW l) :=
      Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
    rw [hmap, hfr]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wm Wm', hWW, Matrix.one_mul]
  · have hφ : Wm.map (frobW l) * Wm'.map (frobW l) = 1 := by
      have e : (Wm * Wm').map (frobW l) = Wm.map (frobW l) * Wm'.map (frobW l) :=
        Matrix.map_mul (f := ((frobW l) : WCb l →+* WCb l))
      rw [← e, hWW]; exact Matrix.map_one _ (map_zero _) (map_one _)
    calc Wm' * A0 * Wm.map (frobW l) * (Wm'.map (frobW l) * A0' * Wm)
        = Wm' * A0 * (Wm.map (frobW l) * Wm'.map (frobW l)) * A0' * Wm := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hφ, Matrix.mul_one, Matrix.mul_assoc Wm', hAA, Matrix.mul_one, hW'W]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantEtaleBasisChangeByOEUnitStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (T0 Wm Wm' A0 A0' : Matrix (Fin d) (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T0.map (galW l (g : GQ l)) = T0) → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T0.map (frobW l) = T0 * A0 → A0 * A0' = 1 → (∀ i j, Wm i j ∈ bk.OE) → (∀ i j, Wm' i j ∈ bk.OE) → Wm * Wm' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * (T0 * Wm).map (galW l (g : GQ l)) = T0 * Wm) ∧ ∃ A1 A1' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A1 i j ∈ bk.OE) ∧ (∀ i j, A1' i j ∈ bk.OE) ∧ (T0 * Wm).map (frobW l) = (T0 * Wm) * A1 ∧ A1 * A1' = 1 := by
  first | (exact @GlobalTheory.ChangeEtaleBasis.main) | (exact GlobalTheory.ChangeEtaleBasis.main) | (intros; apply GlobalTheory.ChangeEtaleBasis.main  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorMemOEAndAinf

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal



theorem GlobalTheory.BKLim.limvec_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hR hF v hv
  have hcl := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hevW : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  have key : ∀ (k : ℕ) (z : WCb l), (l : WCb l) ^ k ∣ z ↔
      Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) z = 0 := fun k z => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun i => ?_, ?_⟩
  · apply hcl.2.1
    intro n
    obtain ⟨s', hs'⟩ := hv n
    refine ⟨(R n *ᵥ fun j => bk.evW (s' j)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hevW _)
  · have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
      fun x => (inclWA l).commutes x
    have hx : ∀ i k, ∃ a : Ainf l, (l : WCb l) ^ k ∣
        (l : WCb l) ^ 0 * (inclW l τ ^ N • (T0 *ᵥ v)) i - inclW l (1 * a) := by
      intro i k
      obtain ⟨s', hs'⟩ := hv k
      obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' k) (fun g => (tw.ρ' k g).val) (F k)
      refine ⟨(((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i, ?_⟩
      set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ k}) with hq
      rw [key, pow_zero, one_mul, one_mul, map_sub, sub_eq_zero]
      have h1 : (fun i => q (v i)) = fun i => q ((R k *ᵥ fun j => bk.evW (s' j)) i) := funext fun i => by
        have := (key k _).1 (hs' i); rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this
      have h2 : (zW (tw.Pi k) * (F k).T).map q = (T0 * R k).map q := by
        ext i j; have := (key k _).1 (hF k i j); rwa [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      have e1 : inclW l ((((tw.Pi k).map (algebraMap ℤ_[l] (Ainf l)) * Y) *ᵥ fun j => bk.ev (s' j)) i) =
          (inclW l τ ^ N • ((zW (tw.Pi k) * (F k).T) *ᵥ fun j => bk.evW (s' j))) i := by
        rw [RingHom.map_mulVec, Matrix.map_mul, hY, Matrix.map_map]
        have : (tw.Pi k).map ((inclW l) ∘ (algebraMap ℤ_[l] (Ainf l))) = zW (tw.Pi k) := by
          ext a b; simp [zW, hinc]
        rw [this, Matrix.mul_smul, Matrix.smul_mulVec]
        rfl
      rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
        RingHom.map_mulVec, RingHom.map_mulVec, h2, Matrix.map_mul, ← Matrix.mulVec_mulVec]
      have h1' : (⇑q ∘ v) = (R k).map q *ᵥ (⇑q ∘ fun j => bk.evW (s' j)) := funext fun j => by
        rw [Function.comp_apply, ← RingHom.map_mulVec]; exact congrFun h1 j
      rw [h1']
    refine ⟨fun i => Classical.choose (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i)), funext fun i => ?_⟩
    have := Classical.choose_spec (GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) 0 _ (hx i))
    rw [one_mul] at this
    exact this.symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitVectorMemOEAndAinfStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.limitVector_mem_OE_and_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  first | (exact @GlobalTheory.BKLim.limvec_mem) | (exact GlobalTheory.BKLim.limvec_mem) | (intros; apply GlobalTheory.BKLim.limvec_mem  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_pre_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F
  obtain ⟨T0, hT0, hT0R⟩ := GlobalTheory.T.exists_etale_basis_limit_lattice_tower l K bk τ hτ d N ρ tw F
  obtain ⟨hfix0, A0, A0', hA0, hA0', hφ0, hAA0⟩ := GlobalTheory.T.limit_breuilKisin_basis_invariant_etale l K bk τ hτ d N ρ tw F T0 hT0 hT0R
  choose R R' hRO hR'O hR hRR' using hT0R
  obtain ⟨Yt, hYt⟩ := GlobalTheory.T.approximatingLattices_transitionMatrix_modPow l K bk τ hτ d N ρ tw F T0 R hT0 hR
  have hc := GlobalTheory.T.latticeApproximation_mittagLeffler l K bk τ hτ d N ρ tw F T0 R hT0 hRO hR
  have hlim := GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow l K bk d tw.d' R Yt hYt hc
  have hL3 := GlobalTheory.T.limitVector_mem_OE_and_ainf l K bk τ hτ d N ρ tw F T0 R hRO hR
  obtain ⟨V, V', hVO, hV'O, hVV, hVlim⟩ := GlobalTheory.T.limitVectors_invertible_basis_over_OE l K bk d tw.d' R (fun n => ⟨R' n, hR'O n, hRR' n⟩) hlim hRO
  choose y1 hy1 using fun j => (hL3 _ (hVlim j)).2
  have hY1 : (Matrix.of fun i j => y1 j i).map (inclW l) = inclW l τ ^ N • (T0 * V) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hy1 j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  obtain ⟨Y, Wm, Wm', hYu, hWO, hW'O, hWW, hYW, hmem⟩ := GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin l K bk τ hτ d N T0 V V' _ hT0 hVO hV'O hVV hY1
  have hlink := GlobalTheory.T.twisted_matrix_congruence_lift_sequence l K bk τ hτ d N ρ tw F T0 R hR hlim hL3 Y (T0 * Wm) hYW hmem
  obtain ⟨Y', hYY'⟩ := GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow l d (2 * N) τ Y hYu (fun n => by
    obtain ⟨m, _, Rn, Q, _, h⟩ := hlink n
    exact ⟨Rn.map bk.ev * Q, h⟩)
  obtain ⟨hfixT, A1, A1', hA1, hA1', hφ1, hAA1⟩ := GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit l K bk d (fun g => (ρ g).val) T0 Wm Wm' A0 A0' hfix0 hA0 hA0' hφ0 hAA0 hWO hW'O hWW
  have hTu : IsUnit (T0 * Wm) := hT0.mul ⟨⟨Wm, Wm', hWW, mul_eq_one_comm.1 hWW⟩, rfl⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) (T0 * Wm) A1 A1' Y Y' hTu hA1 hA1' hφ1 hAA1 hfixT hYW hYY'
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_right_inverse_mod_pow_of_ev l K bk τ hτ (2 * N)
  refine ⟨P, r, fun n => ?_⟩
  obtain ⟨m, hnm, Rn, Q, h1, h2⟩ := hlink n
  have h3 := GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow l d (tw.d' m) n (2 * N) τ Y Y' (Rn.map bk.ev) Q (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1 hYu hYY' h2
  obtain ⟨G, hG⟩ := hr d (tw.d' m) n Rn (Q * Y) h3
  exact ⟨m, hnm, Rn, G, by rw [hP]; exact h1, hG⟩

end GlobalTheory.BKLim
end
end

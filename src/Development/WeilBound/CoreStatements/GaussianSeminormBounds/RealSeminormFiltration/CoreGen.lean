module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreHarm
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockHarmSplit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockJointMult
public import Formalism.PeriodIntegrals.FockDegreeTwoParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.EqZeroOfFockInnerSelfRe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.KroneckerMapOneRightNeZero
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KroneckerOneRightSwap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.SameBlockOfPosC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockRaiseLow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.ConjTransposeOneKronecker
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.MinusPartOfMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.MinDeg
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KernelHarmonic

section

@[expose] public section

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_Xd (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by

  rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]

theorem sum_rows (c d e : Ix r s) (a : Ix p q) (F G : Ix p q → Pol p q r s) :
    ∑ a' : Ix p q, (if linePos ((a', d) : Ln p q r s) = true then
      ((if ((a', d) : Ln p q r s) = (a, e) then F a' else 0) +
       (if ((a', c) : Ln p q r s) = (a, e) then G a' else 0)) else 0) =
    if linePos ((a, d) : Ln p q r s) = true then
      ((if d = e then F a else 0) + (if c = e then G a else 0)) else 0 := by
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro b _ hb
    simp [Prod.mk.injEq, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))

theorem lowOp_posOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (posOp a b P) =
      posOp a b (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])

  rw [posOp_apply, posOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) =
      (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) +
      (if linePos ((a, e) : Ln p q r s) = true then
        (if linePos ((a, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((a, c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((a, d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0))
          else 0) else 0) := by
    intro e
    by_cases h : linePos ((a, e) : Ln p q r s) = true
    · simp only [h, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single d]
  · by_cases h : linePos ((a, d) : Ln p q r s) = true
    · simp [h, hcd']
    · simp [h]
  · intro e _ hed
    by_cases h1 : linePos ((a, e) : Ln p q r s) = true
    · by_cases h2 : linePos ((a, d) : Ln p q r s) = true
      · have hce : c ≠ e := by
          rintro rfl; exact not_both c d hcd a h1 h2
        simp [h1, h2, Ne.symm hed, hce]
      · simp [h1, h2]
    · simp [h1]
  · simp

theorem lowOp_negOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)

  rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem kernel_harmonic : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add (f := _), map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]

end PI.FockOneDegW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockOneDeg

section

@[expose] public section

theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
end
end

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreGen

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {p q r s : ℕ}

theorem gen_minus_small {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {g : MvPolynomial σ ℂ} (hg : g ∈ homog σ d) : minusPart A g = 0 := by
  unfold minusPart
  have h : ∀ e : ℕ, homogeneousComponent e (A (homogeneousComponent (e + 2) g)) = 0 := by
    intro e
    rw [homogeneousComponent_of_mem hg, if_neg (by omega)]
    simp
  simp [h]

theorem th_gen_harm (c τ : ℂ) (c0 : ℚ) (hc : c = c0) (N : Submodule ℂ (ThC p q r s c))
    (hH : (jHarm p q r s ⊓ polChi p q r s c).map (thMkC p q r s c) ≤ N)
    (hN : ∀ W, ∀ x ∈ N, thAct p q r s c τ W x ∈ N) : N = ⊤ := by
  have hharm : ∀ d, ∀ g ∈ homog (Ix p q × Ix r s) d, g ∈ jHarm p q r s → thMkC p q r s c g ∈ N := by
    intro d g hg hj
    have h1 := charSplit c c0 hc d (jHarm p q r s ⊓ homog (Ix p q × Ix r s) d) inf_le_right
      (fun a b hab x hx => ⟨jHarmonic_stable_first_action a b hab x hx.1, homogeneous_stable_first_action d a b hab x hx.2⟩)
    refine hH (Submodule.map_mono ?_ (h1 (Submodule.mem_map_of_mem (show g ∈ _ from ⟨hj, hg⟩))))
    exact inf_le_inf_right _ inf_le_left
  have key : ∀ d, ∀ g ∈ homog (Ix p q × Ix r s) d, thMkC p q r s c g ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro g hg
      by_cases hd : d < 2
      · exact hharm d g hg (Submodule.subset_span
          ⟨fun X _ => gen_minus_small _ hd hg, fun Y _ => gen_minus_small _ hd hg⟩)
      · obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
        have hmin : ∀ (A : Module.End ℂ (Pol p q r s)), ∀ Q ∈ homog (Ix p q × Ix r s) e,
            thMkC p q r s c (minusPart A Q) ∈ N := by
          intro A Q hQ
          by_cases he : e < 2
          · rw [gen_minus_small A he hQ, map_zero]; exact N.zero_mem
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
            rw [PI.FHS.minusPart_of_mem hQ]
            exact ih e' (by omega) _ (homogeneousComponent_mem e' _)
        have hs := harmonicSplitting_holds p q r s true true rfl e
        rw [hs] at hg
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hg
        rw [map_add (f := _)]
        refine N.add_mem (hharm _ y hy.1 (Submodule.span_mono ?_ hy.2)) ?_
        · intro P hP
          exact ⟨hP.1 rfl, hP.2 rfl⟩
        · have : Submodule.span ℂ (raised p q r s true true e) ≤ N.comap (thMkC p q r s c) := by
            refine Submodule.span_le.2 ?_
            rintro R ⟨Q, hQ, ⟨-, Z, hZ, rfl⟩ | ⟨-, Z, hZ, rfl⟩⟩
            · show thMkC p q r s c _ ∈ N
              rw [th_plus1 c hZ]
              exact N.neg_mem (hmin _ Q hQ)
            · show thMkC p q r s c _ ∈ N
              have h4 := (gradedOscillatorProperty p q r s).2.2.2.1 Z hZ Q
              have h5 : plusPart (fockAct2 p q r s Z) Q =
                  twAct p q r s τ Z Q - (τ * Z.trace) • Q - minusPart (fockAct2 p q r s Z) Q := by
                rw [twAct_apply, add_sub_cancel_right]
                exact eq_sub_of_add_eq h4.symm
              have hQN := ih e (by omega) Q hQ
              rw [h5, map_sub, map_sub, map_smul, ← thAct_mk]
              exact N.sub_mem (N.sub_mem (hN _ _ hQN) (N.smul_mem _ hQN)) (hmin _ Q hQ)
          exact this hz
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change thMkC p q r s c f ∈ N

  rw [← sum_homogeneousComponent f, map_sum]
  exact N.sum_mem fun d _ => key d _ (homogeneousComponent_mem d f)

theorem gen_oneDeg (c : ℂ) (c0 : ℚ) (hc : c = c0) {g : Pol p q r s} (h0 : g ≠ 0)
    (hj : g ∈ jHarm p q r s) (hχ : g ∈ polChi p q r s c) :
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0) ∧ g ∈ homog (Ix p q × Ix r s) d := by
  have hJ : g ∈ Jset p q r s := PI.FJMF.span_jset g hj
  refine (fock_degree_one p q r s).1 _ g h0 ⟨Submodule.span ℂ {g}, inferInstance,
    Submodule.mem_span_singleton_self g, ?_, ?_⟩ hJ.2
  · intro X hX w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 : fockAct1 p q r s X g = chiTr c X • g := by
      have := (Submodule.mem_iInf _).1 hχ ⟨X, hX⟩
      rw [LinearMap.mem_ker] at this
      exact sub_eq_zero.1 this
    rw [map_smul, h1]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g))
  · intro ν w hw hhw
    have hwχ : w ∈ polChi p q r s c := (Submodule.span_singleton_le_iff_mem _ _).2 hχ hw
    have h1 := (hwK_of_hwSub.1 ((mem_polChi_iff_hw c c0 hc w).1 hwχ)).1
    have h2 := (hwK_of_hwSub.1 hhw.2).1
    funext a
    have h3 : ((ν a : ℚ) : ℂ) • w = ((c0 : ℚ) : ℂ) • w := (h2 a).symm.trans (h1 a)
    have h4 := smul_left_injective ℂ hhw.1 h3
    exact_mod_cast h4

theorem jHarm_polChi_homog (c : ℂ) (c0 : ℚ) (hc : c = c0) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    jHarm p q r s ⊓ polChi p q r s c ≤ homog (Ix p q × Ix r s) d0 := by
  intro g hg
  by_cases h0 : g = 0
  · rw [h0]; exact Submodule.zero_mem _
  · obtain ⟨d, h1, h2⟩ := gen_oneDeg c c0 hc h0 hg.1 hg.2
    have : d = d0 := by exact_mod_cast h1.trans hd.symm
    rwa [this] at h2

theorem exists_gen (c : ℂ) (c0 : ℚ) (hc : c = c0) (La : Ix r s → ℚ)
    (hJ : JointShape p q r s (fun _ => c0) La) (hU : ∀ ν, JointShape p q r s (fun _ => c0) ν → ν = La) :
    ∃ (d0 : ℕ) (f : Pol p q r s), (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0) ∧
      f ∈ homog (Ix p q × Ix r s) d0 ∧ HwK (units (fockAct2 p q r s)) La f ∧
      ∀ U : Submodule ℂ (Pol p q r s), f ∈ U → KSt (units (fockAct2 p q r s)) U →
        jHarm p q r s ⊓ polChi p q r s c ≤ U := by
  obtain ⟨⟨f, hf⟩, hf0, hline⟩ := finrank_eq_one_iff'.1 ((fock_joint_multiplicity p q r s _ La).1 hJ)
  have hf0' : f ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfχ : f ∈ polChi p q r s c := (mem_polChi_iff_hw c c0 hc f).2 hf.1.1
  have hfj : f ∈ jHarm p q r s := hf.2
  obtain ⟨d0, hd, hfd⟩ := gen_oneDeg c c0 hc hf0' hfj hfχ
  refine ⟨d0, f, hd, hfd, hwK_of_hwSub.1 hf.1.2, fun U hfU hUK => ?_⟩
  have hVd := jHarm_polChi_homog (p := p) (q := q) (r := r) (s := s) c c0 hc d0 hd
  set V := jHarm p q r s ⊓ polChi p q r s c with hV
  have hVK : KSt (units (fockAct2 p q r s)) V := fun a b hab x hx =>
    ⟨jHarmonic_stable_second_action a b hab x hx.1, polChi_stable_second_action c _ hx.2⟩
  let Z : Submodule ℂ (Pol p q r s) :=
    { carrier := {z | z ∈ V ∧ ∀ x ∈ U ⊓ V, fockInner x z = 0}
      zero_mem' := ⟨V.zero_mem, fun x _ => PI.FHS.fockInner_zero_right x⟩
      add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun x hx => by
        rw [PI.FHS.fockInner_add_right, ha.2 x hx, hb.2 x hx, add_zero]⟩
      smul_mem' := fun t a ha => ⟨V.smul_mem t ha.1, fun x hx => by
        rw [PI.FHS.fockInner_smul_right, ha.2 x hx, mul_zero]⟩ }
  have hZ : Z = ⊥ := by
    by_contra hne
    have : FiniteDimensional ℂ (homog (Ix p q × Ix r s) d0) :=
      Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ ℂ d0)
    have : FiniteDimensional ℂ Z :=
      Submodule.finiteDimensional_of_le (S₂ := homog (Ix p q × Ix r s) d0) fun z hz => hVd hz.1
    have hZK : KSt (units (fockAct2 p q r s)) Z := by
      intro a b hab z hz
      refine ⟨hVK a b hab z hz.1, fun x hx => ?_⟩
      have hba := PI.FHS.sameBlock_symm hab
      have h1 : fockInner (fockAct2 p q r s (Eab b a) x) z =
          epsB b a * fockInner x (fockAct2 p q r s (Eab a b) z) := adj2 p q r s b a x z
      have h2 := hz.2 _ (show units (fockAct2 p q r s) b a x ∈ U ⊓ V from
        ⟨hUK b a hba x hx.1, hVK b a hba x hx.2⟩)
      rw [epsB, if_pos hba, one_mul] at h1
      exact h1.symm.trans h2
    obtain ⟨ν, g, hgZ, hg0, hgw⟩ := hwExist2 Z hne hZK
    have hg1 := (mem_polChi_iff_hw c c0 hc g).1 hgZ.1.2
    have hsh : JointShape p q r s (fun _ => c0) ν := by
      by_contra hn
      have h := (fock_joint_multiplicity p q r s _ ν).2 hn
      have : g ∈ (⊥ : Submodule ℂ (Pol p q r s)) := h ▸ ⟨⟨hg1, hgw⟩, hgZ.1.1⟩
      exact hg0 ((Submodule.mem_bot ℂ).1 this)
    obtain rfl := hU ν hsh
    obtain ⟨t, ht⟩ := hline ⟨g, ⟨hg1, hgw⟩, hgZ.1.1⟩
    have ht' : t • f = g := congrArg Subtype.val ht
    have hgU : g ∈ U ⊓ V := ⟨ht' ▸ U.smul_mem t hfU, hgZ.1⟩
    exact hg0 (PI.FHS.fockInner_self_eq_zero (hgZ.2 g hgU))
  intro v hv
  obtain ⟨y, hy, hperp⟩ := PI.FHS.exists_orth (U ⊓ V) d0 (inf_le_right.trans hVd) v
  have hz : v - y ∈ Z := ⟨V.sub_mem hv hy.2, hperp⟩
  rw [hZ, Submodule.mem_bot, sub_eq_zero] at hz
  exact hz ▸ hy.1

end PositivityTheory.KReal

end
end
end

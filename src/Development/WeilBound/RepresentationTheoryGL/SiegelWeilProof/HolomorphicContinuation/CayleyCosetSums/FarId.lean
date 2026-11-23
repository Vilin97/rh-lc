module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveGR
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CosetSumApply
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopSeries
import Mathlib.Tactic.Basify
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarLoc
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveHasDerivAt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DirSeries

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem dirSeries (hC : CurveGR) (hF : FzDer) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) {z : ℂ} (hz : t < z.re)
    (Z : M2 n) (b : Bool) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0) ∧
    deriv (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 =
      d.eval z * ∑' q, C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 := by
  obtain ⟨γ, hγc, hγ0, hγadd, hγe⟩ := hC n Z b
  obtain ⟨Cd, hCd0, hR⟩ := hF n m e (z - s₀) Z b
  choose Rf hRf using hR
  have hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
      fz m e (z - s₀) (mR (y₁ * γ s)) := by
    intro y₁ s
    rw [mR_mul, hγe]
  have hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s := by
    intro y₁ s
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)
    have hfe : (fun u : ℝ => fz m e (z - s₀)
        (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) =
        fun x : ℝ => fz m e (z - s₀)
          (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))) := by
      funext u
      rw [hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]
    rw [hfe]
    exact h1
  have hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))
  obtain ⟨u, hu, hbound⟩ := (h.far z hz).1 _ hK
  have hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q := by
    intro q s hs
    have hb := hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q
    rw [mul_assoc (y₀ q), ← hyC q (y * γ s)]
    simpa only [GlobalTheory.Eis.term, trm, mul_assoc] using hb
  have hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q := by
    intro q s hs
    have h1 := (hRf (y₀ q * y * γ s)).2
    have h2 := hterm q s (Ioo_subset_Icc_self hs)
    rw [norm_mul] at h2 ⊢
    calc ‖C q‖ * ‖Rf (y₀ q * y * γ s)‖
        ≤ ‖C q‖ * (Cd * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cd * (‖C q‖ * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) := by ring
      _ ≤ Cd * u q := mul_le_mul_of_nonneg_left h2 hCd0
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun q => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))) :=
    hu.of_norm_bounded fun q => by
      simpa only [hfzγ] using hterm q 0 ⟨by norm_num, by norm_num⟩
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo
    (g := fun q (s : ℝ) => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))))
    (g' := fun q s => C q * Rf (y₀ q * y * γ s))
    (fun q s _ => (hderiv (y₀ q * y) s).const_mul (C q)) hbd h0mem hg0 h0mem
  rw [hγ0] at hsum
  simp only [mul_one] at hsum
  have hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y) :=
    fun q => (hRf (y₀ q * y)).1.deriv
  have hfun : (fun s : ℝ => resG ι (Ê z) g
      (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) =
      fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) := by
    funext s
    have hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
        Ê z (g * ι (y * γ s)) := by
      rw [← hγe, ← mR_mul, resG_mR]
    rw [hl, (h.far z hz).2]
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]
  simp only [hRfd]
  refine ⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩
  · simpa only [hγ0, mul_one] using hbd q 0 h0mem
  · rw [hfun, (hsum.const_mul (d.eval z)).deriv]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarIdOf

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FarP

theorem farId_of (hC : CurveGR) (hF : FzDer) : FarId := by
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD hS _ _ μ _ _ Q N ρ ψ a b D M hρ hψ hab hDd hM hid
  refine ⟨⟨t, ?_⟩, FarP.klaw hS hD⟩
  intro z hz g y
  have key : ∀ (F : M2 n → ℂ) (x : M2 n), rC (lowQ Q) F x =
      deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => F (x * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    intro F x
    simp only [rC, dir1, dir2, if_true]
    rfl
  choose y₀ C hyC using fun q : GlobalTheory.Eis.Cosets Pp Γ => FarP.termSplit hS hD z (↑(Quotient.out q) * g)
  have d1 := FarP.dirSeries hC hF hD hz (lowQ Q) true g y y₀ C hyC
  have d2 := FarP.dirSeries hC hF hD hz (lowQ Q) false g y y₀ C hyC
  have tp := fun l : Fin N => FarP.topSeries hS hD μ hz (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1
    (hab l).1 (hab l).2 g y y₀ C hyC
  have hq : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) =
      ∑ l : Fin N, M l (z - s₀) * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    intro q
    have h := hid (z - s₀) (mR (y₀ q * y)) (y₀ q * y).2
    rw [key] at h
    exact h
  rw [key, d1.2, d2.2, Finset.sum_congr rfl (fun l _ => by rw [(tp l).2])]
  have e1 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (d1.1.mul_left _).tsum_add (d2.1.mul_left _)]
    congr 1
    funext q
    ring
  have e2 : ∑' q, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
      ∑ l : Fin N, M l (z - s₀) * ∑' q, C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y)) := by
    have hq2 : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, C q * (D (z - s₀) * (deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0)) =
        ∑ l : Fin N, M l (z - s₀) * (C q * tOp μ (⇑(ιK n)) (ρ l) (ψ l) (a l) (b l) (fz m e (z - s₀)) (mR (y₀ q * y))) := by
      intro q
      rw [hq q, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [tsum_congr hq2]
    rw [Summable.tsum_finsetSum (fun l _ => ((tp l).1.mul_left (M l (z - s₀))))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← tsum_mul_left]
  have e3 := e1.symm.trans e2
  calc D (z - s₀) * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        Complex.I * (Polynomial.eval z d * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0))
        = Polynomial.eval z d * (D (z - s₀) * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if true = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0 +
        D (z - s₀) * Complex.I * ∑' q, C q * deriv (fun (s : ℝ) => fz m e (z - s₀) (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • if false = true then dir1 (lowQ Q) else dir2 (lowQ Q)))) 0) := by ring
    _ = _ := by
      rw [e3, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring

end PositivityTheory.Rg.Sw.HSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ReConjMulLe

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_curve {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) (s : ℝ) :
    fz m e w (x * cE X s) = (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) := by
  have hg : InG (x * cE X s) := inG_mul hx (inG_cE hX s)
  have hd := det_first_cayley_block_ne_zero hg
  have hmul : (u1 (x * cE X s)).det * (ub1 (x * cE X s)).det =
      ((Complex.normSq (u1 (x * cE X s)).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_adjoint hg, Matrix.det_conjTranspose]
    exact Complex.mul_conj _
  have hpos : (0 : ℝ) < Complex.normSq (u1 (x * cE X s)).det := Complex.normSq_pos.mpr hd
  unfold fz
  rw [hmul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), Complex.ofReal_log hpos.le]

theorem fz_deriv {X x : M2 n} (hX : IsLie X) (hx : InG x) (m : ℕ) (e : ℤ) (w : ℂ) :
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (x * cE X s)) R 0 ∧
      ‖R‖ ≤ ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
  have hd0 : det x ≠ 0 := (isUnit_det_of_InG hx).ne_zero
  have ha0 : (u1 x).det ≠ 0 := det_first_cayley_block_ne_zero hx
  have hfun : (fun s : ℝ => fz m e w (x * cE X s)) = fun s : ℝ =>
      (x * cE X s).det ^ e * (u1 (x * cE X s)).det ^ (-(m : ℤ)) *
        Complex.exp (((Real.log (Complex.normSq (u1 (x * cE X s)).det) : ℝ) : ℂ) * (-w)) :=
    funext fun s => fz_curve hX hx m e w s
  have hf0 : fz m e w x = (det x) ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w)) := by
    have h := fz_curve hX hx m e w 0
    rw [cE_zero, mul_one] at h
    exact h
  have hD : HasDerivAt (fun s : ℝ => det (x * cE X s))
      ((fderiv ℂ (fun y : M2 n => det y) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => det y) cd_det X x
  have hA : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)) 0 :=
    curve_deriv (fun y : M2 n => (u1 y).det) cd_detu1 X x
  have hD0 : det (x * cE X 0) = det x := by rw [cE_zero, mul_one]
  have hA0 : (u1 (x * cE X 0)).det = (u1 x).det := by rw [cE_zero, mul_one]
  have hzD : HasDerivAt (fun z : ℂ => z ^ e) (↑e * det x ^ (e - 1)) (det (x * cE X 0)) := by
    rw [hD0]
    exact hasDerivAt_zpow e (det x) (Or.inl hd0)
  have hzA : HasDerivAt (fun z : ℂ => z ^ (-(m : ℤ)))
      (↑(-(m : ℤ)) * (u1 x).det ^ (-(m : ℤ) - 1)) ((u1 (x * cE X 0)).det) := by
    rw [hA0]
    exact hasDerivAt_zpow _ _ (Or.inl ha0)
  have hDz := hzD.comp (0 : ℝ) hD
  have hAz := hzA.comp (0 : ℝ) hA
  have hre : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.re)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).re 0 := by
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have him : HasDerivAt (fun s : ℝ => (u1 (x * cE X s)).det.im)
      ((fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X)).im 0 := by
    have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    exact h2
  have hN := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => Complex.normSq_apply (u1 (x * cE X s)).det)
  have hNne : Complex.normSq (u1 (x * cE X 0)).det ≠ 0 := by
    rw [hA0]
    exact (Complex.normSq_pos.mpr ha0).ne'
  have hL := hN.log hNne
  have hE := (hL.ofReal_comp.mul_const (-w)).cexp
  have hfin := (hDz.mul hAz).mul hE
  rw [hfun]
  refine ⟨_, hfin, ?_⟩
  simp only [hA0, hD0, Function.comp_apply]
  have hd' : (fderiv ℂ (fun y : M2 n => det y) x) (x * X) = rD X x * det x := by
    unfold rD
    field_simp
  have ha' : (fderiv ℂ (fun y : M2 n => (u1 y).det) x) (x * X) = rA X x * (u1 x).det := by
    unfold rA
    field_simp
  have bound : ‖(det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      Complex.exp (((Real.log (Complex.normSq (u1 x).det) : ℝ) : ℂ) * (-w))) *
      ((e : ℂ) * rD X x + (-(m : ℂ)) * rA X x + ((2 * (rA X x).re : ℝ) : ℂ) * (-w))‖ ≤
      ‖fz m e w x‖ * (|(e : ℝ)| * ‖rD X x‖ + ((m : ℝ) + 2 * ‖w‖) * ‖rA X x‖) := by
    rw [norm_mul, hf0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine norm_add₃_le.trans ?_
    have h1 : |(rA X x).re| ≤ ‖rA X x‖ := Complex.abs_re_le_norm _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    simp only [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  convert bound using 2
  rw [hd', ha']
  have hq : ((rA X x * (u1 x).det).re * (u1 x).det.re + (u1 x).det.re * (rA X x * (u1 x).det).re +
      ((rA X x * (u1 x).det).im * (u1 x).det.im + (u1 x).det.im * (rA X x * (u1 x).det).im)) /
      Complex.normSq (u1 x).det = 2 * (rA X x).re := by
    have hn : Complex.normSq (u1 x).det ≠ 0 := (Complex.normSq_pos.mpr ha0).ne'
    rw [div_eq_iff hn, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  rw [hq]
  simp only [Pi.mul_apply, Function.comp_apply, cE_zero, mul_one]
  rw [zpow_sub_one₀ hd0, zpow_sub_one₀ ha0]
  push_cast
  field_simp

end PositivityTheory.Rg.Sw.HSt.FL
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FzDer

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.FL
open PositivityTheory.Rg.Sw.LVs.II (cE)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fzDer : FzDer := by
  intro n m e w Z b
  have hX : IsLie (if b = true then dir1 Z else dir2 Z) := lie_dir Z b
  haveI := kRCpt n
  have hc1 : Continuous fun k : KR n => rD (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rD _).comp continuous_subtype_val
  have hc2 : Continuous fun k : KR n => rA (if b = true then dir1 Z else dir2 Z) (mR (k : GR n)) :=
    (continuous_rA _).comp continuous_subtype_val
  obtain ⟨C1, hC1⟩ := (isCompact_range hc1).isBounded.exists_norm_le
  obtain ⟨C2, hC2⟩ := (isCompact_range hc2).isBounded.exists_norm_le
  refine ⟨|(e : ℝ)| * max C1 0 + ((m : ℝ) + 2 * ‖w‖) * max C2 0, by positivity, fun y => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  obtain ⟨R, hR, hRb⟩ := fz_deriv (x := mR (p * k)) hX (p * k).2 m e w
  refine ⟨R, ?_, ?_⟩
  · simp only [cE_eq_exp]
    exact hR
  · refine hRb.trans ?_
    have e1 : rD (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rD (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rD_up]
    have e2 : rA (if b = true then dir1 Z else dir2 Z) (mR (p * k)) =
        rA (if b = true then dir1 Z else dir2 Z) (mR k) := by
      rw [mR_mul, rA_up _ _ _ hp]
    have b1 : ‖rD (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C1 0 :=
      (hC1 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    have b2 : ‖rA (if b = true then dir1 Z else dir2 Z) (mR k)‖ ≤ max C2 0 :=
      (hC2 _ ⟨⟨k, hk⟩, rfl⟩).trans (le_max_left _ _)
    rw [e1, e2, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    gcongr

end PositivityTheory.Rg.Sw.HSt
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarId

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.HSt

theorem farId : FarId := farId_of curveGR fzDer

end PositivityTheory.Rg.Sw.HSt
end
end

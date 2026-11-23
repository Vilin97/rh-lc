module

public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.Columns.MaxSlopeOrthogonalNegLog

section

@[expose] public section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section F3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable [_root_.NumberField.IsTotallyComplex K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem slope_line_le_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : c ^ (nPl K) ≤ ht b X L := by
    rw [hL, hg]
    have h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re := by
      intro v
      rw [Matrix.det_fin_one]
      simp only [gramPl, Matrix.of_apply]
      rw [Formalism.ExtensionFiltration.majAt_self_re]
      exact hn v
    calc c ^ (nPl K) = ∏ _v : InfinitePlace K, c := by rw [Finset.prod_const, Finset.card_univ]; rfl
      _ ≤ ∏ v, (gramPl b X v (fun _ : Fin 1 => x)).det.re := Finset.prod_le_prod₀ (fun v _ => hc.le) (fun v _ => h1 v)
  have hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hht
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk]
  have : Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem max_slope_line_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muMaxDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  have : Module.Finite K V := Module.Finite.of_basis b
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_
  have h1 : rkK (K := K) Q ≤ 1 := by
    rw [← hrk]
    exact Submodule.finrank_mono (Submodule.span_mono hQ)
  have h2 : 0 < rkK (K := K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hrkQ : rkK (K := K) Q = rkK (K := K) L := by omega
  have hi := (Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1
  have hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
  have hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
    rw [hrk]
    positivity
  have := slope_line_le_neg_log b X hX x hx c hc hn
  rw [hi]
  linarith

end F3

section F3b

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]

end F3b

end Formalism.L2.Col
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.MuMaxLeMon

section

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms Formalism.L2.Col

section Gen

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

theorem muMax_le_mon {V κ : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype κ] [DecidableEq κ]
    (b : Basis κ K V) (X : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) (hN : N.FG) (φ : V →ₗ[K] (MonI lam → K)) (hinj : Set.InjOn φ N)
    (hne : N.map (φ.restrictScalars (𝓞 K)) ≠ ⊥)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0)
    (hint : ∀ x ∈ N, ∀ m, φ x m ∈ (I : Submodule (𝓞 K) K))
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (hnorm : ∀ v x, normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (φ x) ^ 2 ≤ B v * normAt b X v x ^ 2)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    muMaxDef b X N ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + (1 / (nPl K : ℝ)) * ∑ v, Real.log (B v) := by
  have hX' : ∀ v : InfinitePlace K, IsUnit ((fun _ : InfinitePlace K => (monD lam)⁻¹) v).det :=
    fun v => (Matrix.isUnit_nonsing_inv_det_iff).mpr (monD_det lam)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hne
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    simp
  obtain ⟨L0, hL0⟩ : ∃ L0 : Submodule (𝓞 K) (MonI lam → K),
      L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) := ⟨_, rfl⟩
  have hmemL0 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) ∈ L0 := fun m => by
    rw [hL0]
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem (Finset.mem_univ m)
      (Submodule.mem_span_singleton_self _))
  have hmapT : N.map (φ.restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hdec : φ x = ∑ m, (φ x m) • (Pi.single m (1 : K) : MonI lam → K) := by
      ext m'
      simp [Finset.sum_apply, Pi.single_apply]
    show φ x ∈ _
    rw [hdec]
    exact Submodule.sum_mem _ fun m _ => Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul (hint x hx m) (hmemL0 m)
  have horth : ∀ s t : MonI lam, s ≠ t → Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single s (1 : K) : MonI lam → K))
      (𝓞 K ∙ (Pi.single t (1 : K) : MonI lam → K)) := by
    intro s t hst v x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [majAt, monH_fcoord]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = s
    · subst hm
      simp [Pi.single_apply, hst]
    · simp [Pi.single_apply, hm]
  have hline : ∀ m, muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹)
      (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) ≤ -Real.log c0 := by
    intro m
    refine max_slope_line_neg_log _ _ hX' _ ?_ c0 hc0 fun v => ?_
    · simp
    · rw [monH_norm, Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simpa using hc m
  have hmain := Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX'
    (fun m => 𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) (fun m => Submodule.fg_span_singleton _) horth
    Finset.univ
  rw [← hL0] at hmain
  have hL0ne : L0 ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    have h1 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) = 0 := fun m => by
      have := hmemL0 m
      rwa [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    funext m
    exact absurd (h1 m) (by simp)
  have hL0mu : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) L0 ≤ -Real.log c0 := by
    have h2 := hmain.2.2.2 ((-Real.log c0 - slopeNormalisingConstant K) / 2) (fun m _ _ => by
      have := hline m
      rw [frameB_muMaxDef] at this
      linarith) hL0ne
    rw [frameB_muMaxDef]
    linarith
  have hT := Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' hmain.1 hL0ne hI0
  have hS := ((Formalism.HN.slopeIneqMean K V κ (MonI lam → K) (MonI lam) b X (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' φ N hN hne).2 (idealSmul (I : Submodule (𝓞 K) K) L0)
    (Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg I hmain.1) hmapT).2 hinj
  have hht : htMap b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) φ ≤
      1 / (nPl K : ℝ) * ∑ v, Real.log (B v) := by
    unfold htMap
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' v φ hφ0
    have hle : opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ≤ √(B v) := by
      apply Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X _ _ hX φ v _ (Real.sqrt_nonneg _)
      intro f
      have h0 : 0 ≤ normAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v (φ f) :=
        Real.sqrt_nonneg _
      have h1 : 0 ≤ normAt b X v f := Real.sqrt_nonneg _
      have := Real.sqrt_le_sqrt (hnorm v f)
      rwa [Real.sqrt_sq h0, Real.sqrt_mul (hB v).le, Real.sqrt_sq h1] at this
    apply Real.log_le_log (by positivity)
    calc opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ^ 2
        ≤ √(B v) ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      _ = B v := Real.sq_sqrt (hB v).le
  linarith [hS, hT, hL0mu, hht]

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end

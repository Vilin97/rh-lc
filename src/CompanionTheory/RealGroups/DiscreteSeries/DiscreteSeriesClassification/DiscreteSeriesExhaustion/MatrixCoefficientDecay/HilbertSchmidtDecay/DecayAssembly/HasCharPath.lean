module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.EnormAddSqLe
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Imports
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.ChainGen

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem line_deriv (hR : N.RightRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : Formalism.REAL.inG ε A)
    (hexp : ∀ t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT A t)) (i : D × List (Fin n)) (u : (path ⟨D, E, hK.gl⟩ χ ss).V)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : ReciprocityTheory.ChartRestriction.DS.inUJ ε g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s))
      (famP σ D E hK.gl χ ss i (actM (path ⟨D, E, hK.gl⟩ χ ss) A u) (g * aT A t)) t := by
  have hgt : ReciprocityTheory.ChartRestriction.DS.inUJ ε (g * aT A t) := by
    have h2 := hexp t
    unfold ReciprocityTheory.ChartRestriction.DS.inUJ at hg h2 ⊢
    rw [Matrix.conjTranspose_mul]
    calc (aT A t)ᴴ * gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * (g * aT A t)
        = (aT A t)ᴴ * (gᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * g) * aT A t := by simp only [Matrix.mul_assoc]
      _ = ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [hg, h2]
  have h0 := hR n ε H σ D E hK χ ss hU i u A hA (g * aT A t) hgt
  have h1 := HasDerivAt.comp_sub_const (f := fun s : ℝ => (famP σ D E hK.gl χ ss i u)
    (g * aT A t * NormedSpace.exp ((s : ℂ) • A))) t t (by rw [sub_self]; exact h0)
  have hfun : (fun s : ℝ => (famP σ D E hK.gl χ ss i u) (g * aT A t * NormedSpace.exp (((s - t : ℝ) : ℂ) • A))) =
      fun s : ℝ => famP σ D E hK.gl χ ss i u (g * aT A s) := by
    funext s
    unfold aT
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute]
    · rw [← add_smul, ← Complex.ofReal_add, add_comm t (s - t), sub_add_cancel]
    · exact ((Commute.refl A).smul_left _).smul_right _
  have hval : (∑ a, ∑ b, A a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b u) = actM (path ⟨D, E, hK.gl⟩ χ ss) A u := by
    simp [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hval] at h1
  simpa only [hfun] using h1

def wv {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ) : X.V :=
  ((zs.drop k).map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod u

theorem wv_succ {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) (k : ℕ)
    (hk : k < zs.length) :
    actM X A (wv X A zs u (k + 1)) = zs[k] • wv X A zs u (k + 1) + wv X A zs u k := by
  have h : wv X A zs u k = actM X A (wv X A zs u (k + 1)) - zs[k] • wv X A zs u (k + 1) := by
    simp only [wv]
    rw [List.drop_eq_getElem_cons hk, List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.sub_apply,
      LinearMap.smul_apply, one_apply_eq_self]
  rw [h]
  abel

theorem wv_length {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (zs : List ℂ) (u : X.V) :
    wv X A zs u zs.length = u := by
  simp [wv]

theorem wv_zero {n : ℕ} (X : GMod n) (A : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ) (hp : p.Monic) (u : X.V) :
    wv X A p.roots.toList u 0 = Polynomial.aeval (actM X A) p u := by
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have hl : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      ((p.roots.toList).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    conv_lhs => rw [← Multiset.coe_toList p.roots]
    rw [Multiset.map_coe, Multiset.prod_coe]
  have key : (p.roots.toList.map (fun z => actM X A - z • (1 : Module.End ℂ X.V))).prod =
      Polynomial.aeval (actM X A) p := by
    conv_rhs => rw [hsplit, hl, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    simp [Algebra.algebraMap_eq_smul_one]
  unfold wv
  rw [List.drop_zero, key]

end CompanionTheory.RgExh.Dec.L.SA
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Source

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem source_gen (hL : N.LeftRule) {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (A : Matrix (Fin n) (Fin n) ℂ) (τ : S7.UJ ε → ℝ) (C : ℝ)
    (hC : ∀ (x : PSub ε A) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilpC A → 0 ≤ τ x →
      Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Y * (S7.toM (x : S7.UJ ε))⁻¹) ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs Y)
    (i : D × List (Fin n)) (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin m → (path ⟨D, E, hK.gl⟩ χ ss).V) (hY : ∀ k, Y k ∈ nilpC A) :
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧
      ∀ x : PSub ε A, 0 ≤ τ x →
        ‖famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) (S7.toM (x : S7.UJ ε))‖ ≤
          Real.exp (-τ x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
  classical
  obtain ⟨l, hl⟩ := hL n ε H σ D E hK χ ss hU i
  let Lf : Fin n → Fin n → (path ⟨D, E, hK.gl⟩ χ ss).V → (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
    fun c d w => (l c d).sum (fun i' r => r • famP σ D E hK.gl χ ss i' w)
  have hLf_mem : ∀ c d w, Lf c d w ∈ SS σ D E hK.gl χ ss := fun c d w =>
    Submodule.sum_mem _ (fun i' _ => Submodule.smul_mem _ _ (gen_mem σ D E hK.gl χ ss i' w))
  have hLf_apply : ∀ c d w g, Lf c d w g = (l c d).sum (fun i' r => r * famP σ D E hK.gl χ ss i' w g) := by
    intro c d w g
    simp only [Lf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hmat : ∀ (g Y' : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      (g * Y' * g⁻¹) c d = ∑ a, ∑ b, Y' a b * (g * Matrix.single a b (1 : ℂ) * g⁻¹) c d := by
    intro g Y' c d
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y']
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y' a b) = Y' a b • Matrix.single a b (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hcomm : ∀ (F : Fin n → Fin n → Fin n → Fin n → ℂ),
      ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
    intro F
    have h := Finset.sum_comm (s := (Finset.univ : Finset (Fin n × Fin n))) (t := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun p q => F p.1 p.2 q.1 q.2)
    simpa only [Fintype.sum_prod_type] using h

  have hid : ∀ g, Formalism.REAL.inUJ ε g → famP σ D E hK.gl χ ss i (∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k)) g =
      ∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g := by
    intro g hg

    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hact : actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) = ∑ a, ∑ b, Y k a b • (path ⟨D, E, hK.gl⟩ χ ss).E a b (v k) := by
      delta actM
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hact]

    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hl _ _ _ g hg, ← hLf_apply]
    simp only [hmat g (Y k), Finset.mul_sum, Finset.sum_mul]
    rw [hcomm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

  have hent : ∀ (x : PSub ε A) (k : Fin m) (c d : Fin n), 0 ≤ τ x →
      ‖(S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹) c d‖ ≤
        Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := by
    intro x k c d hx
    set M := S7.toM (x : S7.UJ ε) * Y k * (S7.toM (x : S7.UJ ε))⁻¹
    have e1 : ‖M c d‖ ^ 2 ≤ Formalism.REAL.hs M := by
      unfold Formalism.REAL.hs
      exact (Finset.single_le_sum (f := fun j => ‖M c j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ c))
    have hexp2 : Real.exp (-τ x) ^ 2 = Real.exp (-2 * τ x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 : Formalism.REAL.hs M ≤ (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2 := by
      rw [hexp2]
      calc Formalism.REAL.hs M ≤ C * Real.exp (-2 * τ x) * Formalism.REAL.hs (Y k) := hC x (Y k) (hY k) hx
        _ = (C * Formalism.REAL.hs (Y k)) * Real.exp (-2 * τ x) := by ring
    calc ‖M c d‖ = Real.sqrt (‖M c d‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) ^ 2) := Real.sqrt_le_sqrt (e1.trans e2)
      _ = Real.sqrt (C * Formalism.REAL.hs (Y k)) * Real.exp (-τ x) := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
      _ = Real.exp (-τ x) * Real.sqrt (C * Formalism.REAL.hs (Y k)) := mul_comm _ _

  let hq : Fin m × Fin n × Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) := fun q =>
    ((Real.sqrt (C * Formalism.REAL.hs (Y q.1)) : ℝ) : ℂ) • Lf q.2.1 q.2.2 (v q.1)
  obtain ⟨T, hTS, hT⟩ := absorb (SS σ D E hK.gl χ ss) (Finset.univ : Finset (Fin m × Fin n × Fin n)) hq
    (fun q _ => Submodule.smul_mem _ _ (hLf_mem _ _ _)) 1 le_rfl
  refine ⟨T, hTS, fun x hx => ?_⟩
  have hg : Formalism.REAL.inUJ ε (S7.toM (x : S7.UJ ε)) := (x : S7.UJ ε).2
  rw [hid _ hg]
  set g := S7.toM (x : S7.UJ ε)
  have hq_norm : ∀ q : Fin m × Fin n × Fin n, ‖hq q g‖ =
      Real.sqrt (C * Formalism.REAL.hs (Y q.1)) * ‖Lf q.2.1 q.2.2 (v q.1) g‖ := by
    intro q
    simp only [hq, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc ‖∑ k, ∑ c, ∑ d, (g * Y k * g⁻¹) c d * Lf c d (v k) g‖
      ≤ ∑ k, ∑ c, ∑ d, ‖(g * Y k * g⁻¹) c d‖ * ‖Lf c d (v k) g‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
        rw [norm_mul]
    _ ≤ ∑ k, ∑ c, ∑ d, Real.exp (-τ x) * (Real.sqrt (C * Formalism.REAL.hs (Y k)) * ‖Lf c d (v k) g‖) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hent x k c d hx) (norm_nonneg _)
    _ = Real.exp (-τ x) * ∑ q : Fin m × Fin n × Fin n, ‖hq q g‖ ^ 1 := by
        simp only [pow_one, hq_norm, Finset.mul_sum, Fintype.sum_prod_type]
    _ ≤ Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ ^ 1 :=
        mul_le_mul_of_nonneg_left (hT g) (Real.exp_pos _).le
    _ = Real.exp (-τ x) * ∑ h ∈ T, ‖h g‖ := by simp only [pow_one]

end CompanionTheory.RgExh.Dec.L.SA
end
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.HasCharPath

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem hasChar_path (hS : StepChar) {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (h : HasChar X χ) : HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss generalizing X χ with
  | nil => exact h
  | cons s ss ih => exact ih _ _ (hS n X χ s h)

theorem assembly_of : Assembly := by
  intro hSC hAbs hGeo hLF hHaar hPoly hRR hLR hKR hGr hPk
  intro _ n ε H _ _ _ σ D E hK χ ss hU hSq hChar hN
  have hXc : HasChar (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) := hasChar_path hSC _ χ ss hChar
  obtain ⟨m, A, τ, c₁, R₀, C, hc₁, hgrad, hτc, hτK, hline, hτadd, hcover, hhs, hcontr⟩ := hGeo n ε
  choose ν hν using fun j => hHaar n ε (A j) (hgrad j)
  choose p hpm hp using fun j => hPoly n ε (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) (A j) hXc (hgrad j)
  obtain ⟨M, hM⟩ := hGr n ε H σ D E hK χ ss hU hSq
  apply hPk n ε H σ D E hK χ ss hU
  intro i u

  have hexp : ∀ j t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT (A j) t) := fun j t => by
    obtain ⟨y, hy⟩ := hline j 1 t
    have hm : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (y : S7.UJ ε)) := (y : S7.UJ ε).2
    rw [hy] at hm
    simpa [show S7.toM (1 : S7.UJ ε) = 1 from rfl] using hm

  have hgline : ∀ j (q : (D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V) (x : S7.UJ ε),
      Continuous fun t : ℝ => gen σ D E hK.gl χ ss q (S7.toM x * aT (A j) t) := fun j q x =>
    continuous_iff_continuousAt.mpr fun t =>
      (line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1 q.2 (S7.toM x) x.2 t).continuousAt
  have hcontS : ∀ f ∈ SS σ D E hK.gl χ ss, Continuous fun g : S7.UJ ε => f (S7.toM g) :=
    cont_span (gen σ D E hK.gl χ ss) (fun g : S7.UJ ε => S7.toM g)
      (fun q => (hKR n ε H σ D E hK χ ss hU q.1 q.2).1)
  have hdomS : ∀ f ∈ SS σ D E hK.gl χ ss, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ),
      (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ (g : S7.UJ ε) (k k' : S7.KG ε),
        ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2 := by
    intro f hf
    obtain ⟨T, Cf, hTS, hb⟩ := dom_span (gen σ D E hK.gl χ ss)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toMK b.2.1 * S7.toM b.1 * S7.toMK b.2.2)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toM b.1)
      (fun q => by
        obtain ⟨T, Cf, h⟩ := (hKR n ε H σ D E hK χ ss hU q.1 q.2).2
        exact ⟨T, Cf, fun b => h b.1 b.2.1 b.2.2⟩) f hf
    exact ⟨T, Cf, hTS, fun g k k' => hb (g, k, k')⟩
  have hchainS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε (SS σ D E hK.gl χ ss) (A j) ((p j).roots.toFinset) f f₀ ∧
        (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ x : PSub ε (A j), 0 ≤ τ j x →
          ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
    intro f hf j
    set zs := (p j).roots.toList with hzs
    have hQ := chain_span (gen σ D E hK.gl χ ss) ε (A j) (τ j) zs.length (fun k => zs[(k : ℕ)]'k.isLt)
      (fun q => by
        refine ⟨fun k => famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 (k : ℕ)),
          fun k => gen_mem σ D E hK.gl χ ss _ _, ?_, ?_, ?_⟩
        · show famP σ D E hK.gl χ ss q.1 (wv _ (A j) zs q.2 (Fin.last zs.length : ℕ)) = _
          rw [Fin.val_last, wv_length]
          rfl
        · intro k g t hg
          have hd := line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1
            (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((k : ℕ) + 1)) g hg t
          rw [wv_succ _ (A j) zs q.2 k k.isLt, LinearMap.map_add, LinearMap.map_smul] at hd
          simpa only [aT, Fin.val_succ, Fin.val_castSucc, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul] using hd
        · obtain ⟨m', Y, v, hY, hpu⟩ := hp j q.2
          obtain ⟨T, hTS, hT⟩ := source_gen hLR hK χ ss hU (A j) (τ j) C (hcontr j) q.1 m' Y v hY
          refine ⟨T, hTS, fun x hx => ?_⟩
          have e : wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((0 : Fin (zs.length + 1)) : ℕ) =
              ∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) := by
            rw [Fin.val_zero, hzs, wv_zero _ (A j) (p j) (hpm j) q.2, hpu]
          show ‖famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2
            ((0 : Fin (zs.length + 1)) : ℕ)) (S7.toM (x : S7.UJ ε))‖ ≤ _
          rw [e]
          exact hT x hx) f hf
    obtain ⟨F, hFS, hFl, hFd, T, hTS, hT⟩ := hQ
    refine ⟨F 0, T, ⟨zs.length, fun k => zs[(k : ℕ)]'k.isLt, F, fun k => ?_, hFS, hFl, rfl, hFd⟩, hTS, hT⟩
    exact Multiset.mem_toFinset.mpr (Multiset.mem_toList.mp (List.getElem_mem _))
  have hqualS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) < ⊤ := by
    intro f hf j
    refine ae_lint_span (gen σ D E hK.gl χ ss) (ν j) (volume.restrict (Set.Ioi (0 : ℝ)))
      (fun (x : PSub ε (A j)) (t : ℝ) => S7.toM (x : S7.UJ ε) * aT (A j) t)
      (fun t => ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) ?_ ?_ f hf
    · intro f' hf' x
      have hc := cont_span (gen σ D E hK.gl χ ss) (fun t : ℝ => S7.toM (x : S7.UJ ε) * aT (A j) t)
        (fun q => hgline j q (x : S7.UJ ε)) f' hf'
      exact ((continuous_enorm.comp hc).measurable.pow_const 2).mul
        (Measurable.ennreal_ofReal (by fun_prop)) |>.aemeasurable
    · intro q
      have h := hN (A j) (muPar ε (A j) (ν j)) (hgrad j) ⟨ν j, rfl, hν j⟩ q.2
      simp only [NSet, Set.mem_ofPred_eq] at h
      have h2 : ∀ᵐ y ∂((ν j).map Subtype.val), lineInt ε (famP σ D E hK.gl χ ss q.1 q.2) (A j) (-rhoA (A j) - 1) y < ⊤ :=
        h q.1
      have h3 := ae_of_ae_map measurable_subtype_coe.aemeasurable h2
      filter_upwards [h3] with x hx
      have e : ∀ t : ℝ, -2 * (-rhoA (A j) - 1) * t = 2 * (rhoA (A j) + 1) * t := fun t => by ring
      simp only [lineInt, e] at hx
      exact hx
  have hlevelS : ∀ f ∈ SS σ D E hK.gl χ ss, LevelF ε f (-M) := by
    intro f hf
    have hhs : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
      unfold Formalism.REAL.hs
      have := S7.continuous_toM ε
      fun_prop
    exact lint_span (gen σ D E hK.gl χ ss) Measure.haar (fun g : S7.UJ ε => S7.toM g)
      (fun g => ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-M)))
      (fun f' hf' => (((continuous_enorm.comp (hcontS f' hf')).measurable.pow_const 2).mul
        (hhs.measurable.pow_const (-M)).ennreal_ofReal).aemeasurable)
      (fun q => hM q.1 q.2) f hf
  have key := hAbs n ε (SS σ D E hK.gl χ ss) m A ν τ (fun j => rhoA (A j)) (fun j => (p j).roots.toFinset) M c₁ R₀ C
    hc₁ (fun j => hLF n ε (A j) (ν j) (τ j) (hgrad j) (hν j) (hτc j) (fun x t y hy => hτadd j x t y hy))
    hτc hτK (fun j x t => by obtain ⟨y, hy⟩ := hline j x t; exact ⟨y, hy, hτadd j x t y hy⟩)
    hcover hhs hcontS hdomS hchainS hqualS hlevelS
  exact key _ (gen_mem σ D E hK.gl χ ss i u)

end CompanionTheory.RgExh.Dec.L.SA
end
end
end

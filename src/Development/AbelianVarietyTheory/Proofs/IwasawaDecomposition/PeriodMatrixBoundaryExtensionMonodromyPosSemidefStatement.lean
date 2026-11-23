module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydiscStatement
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonneg

section

@[expose] public section

namespace GlobalTheory

open Matrix

theorem intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  intro g B hB hQ
  set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM

  set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf
  have hcont : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x := by
    intro c x
    simp only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by
    intro v
    simp only [hf, hM, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  have hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ)) := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
    have hdvd : ∀ i, (q i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    let v : Fin g → ℤ := fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)
    have hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ) := by
      funext i
      have hd : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
      simp only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div (hdvd i) hd, Rat.cast_def]
      field_simp
    have h1 := hscale (N : ℝ) (fun i => (q i : ℝ))
    rw [hv, hint] at h1
    have h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by exact_mod_cast hQ v
    have h3 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hall : ∀ x : Fin g → ℝ, 0 ≤ f x := by
    intro x
    have hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have := hdense.closure_range ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hM, conjTranspose_apply, hB.apply i j]
  · simpa [hf] using hall x

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonnegStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidef

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerExt

theorem logExp_add_single {n a : ℕ} (s : Fin n → ℂ) (j : Fin n) (hj : (j : ℕ) < a) :
    logExp a (s + Pi.single j (2 * Real.pi * Complex.I)) = logExp a s := by
  funext k
  simp only [logExp, Pi.add_apply]
  by_cases hk : k = j
  · subst hk
    simp [hj, Complex.exp_add]
  · simp [Pi.single_apply, hk]

theorem mem_logDom_add_single {n a : ℕ} {s : Fin n → ℂ} (hs : s ∈ logDom n a) (j : Fin n) (hj : (j : ℕ) < a) :
    s + Pi.single j (2 * Real.pi * Complex.I) ∈ logDom n a := by
  intro k
  have := hs k
  by_cases hk : k = j
  · subst hk
    simp only [if_pos hj] at this ⊢
    simpa using this
  · simpa [Pi.single_apply, hk] using this

theorem quad_single {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i : Fin g) :
    dotProduct (Pi.single i 1) (M.mulVec (Pi.single i 1)) = M i i := by
  simp [Matrix.mulVec_single, single_dotProduct]

theorem quad_add {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i j : Fin g) :
    dotProduct (Pi.single i 1 + Pi.single j 1) (M.mulVec (Pi.single i 1 + Pi.single j 1)) =
      M i i + M i j + M j i + M j j := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single, single_dotProduct]
  simp
  ring

theorem cast_single {g : ℕ} (i : Fin g) : (fun l => ((Pi.single i (1 : ℤ) : Fin g → ℤ) l : ℂ)) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem cast_single_add {g : ℕ} (i j : Fin g) :
    (fun l => (((Pi.single i (1 : ℤ) + Pi.single j 1 : Fin g → ℤ)) l : ℂ)) = Pi.single i 1 + Pi.single j 1 := by
  funext l
  by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [Pi.single_apply, h1, h2]

theorem periodMatrix_extension : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  intro n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon

  have hs₀ : ∃ s₀, s₀ ∈ logDom n a ∧ logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by
    refine ⟨fun k => if (k : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0, ?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) < a
      · simp only [if_pos hk, Complex.ofReal_re]
        exact Real.log_neg (by positivity) (by linarith)
      · simp [hk]
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [logExp, if_pos hk]
        rw [← Complex.ofReal_exp, Real.exp_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      · simp [logExp, hk, hρ]
  obtain ⟨s₀, hs₀D, hs₀B⟩ := hs₀

  have hBsym : ∀ k, (B k).IsSymm := by
    intro k
    have hj : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
    have h1 := hmon s₀ hs₀D hs₀B k
    have h2 := (hsym _ (mem_logDom_add_single hs₀D _ hj) (by rw [logExp_add_single _ _ hj]; exact hs₀B)).1
    have h3 := (hsym s₀ hs₀D hs₀B).1
    rw [h1] at h2
    refine Matrix.IsSymm.ext fun i j => ?_
    have e1 := congrFun (congrFun h2 i) j
    have e2 := congrFun (congrFun h3 i) j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.map_apply] at e1 e2
    have : ((B k j i : ℤ) : ℂ) = B k i j := by rw [e2] at e1; exact add_left_cancel e1
    exact_mod_cast this
  have hnn := GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon
  refine ⟨fun k => GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg g (B k) (hBsym k) (hnn k), ?_⟩
  have hF : ∀ v : Fin g → ℤ, ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
        dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) -
          ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) =
            F (logExp a s) :=
    fun v => GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc n a g ha ρ₁ τ B v hρ hρ1 hdiff hsym hmon (fun k => hnn k v)
  choose F hFd hFe using hF
  let e : Fin g → Fin g → ℤ := fun i => Pi.single i 1
  refine ⟨fun z => Matrix.of fun i j => if i = j then F (e i) z else (F (e i + e j) z - F (e i) z - F (e j) z) / 2,
    fun i j => ?_, fun z _ => ?_, fun s hs hsB => ?_⟩
  · simp only [Matrix.of_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]; exact hFd _
    · simp only [if_neg hij]
      have h1 := hFd (e i + e j)
      have h2 := hFd (e i)
      have h3 := hFd (e j)
      fun_prop
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg (Ne.symm hij), if_neg hij, add_comm (e j)]
      ring
  · refine Matrix.ext fun i j => ?_
    beta_reduce
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
    have hsm : ∀ k, ((s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) i j =
        s (Fin.castLE ha k) / (2 * Real.pi * Complex.I) * ((B k i j : ℤ) : ℂ) := fun k => rfl
    rw [Finset.sum_congr rfl fun k _ => hsm k]
    set c : ℂ := 2 * Real.pi * Complex.I
    have hi := hFe (e i) s hs hsB
    have hj := hFe (e j) s hs hsB
    simp only [e, cast_single, quad_single] at hi hj
    have hsum1 : ∀ l, ∑ k, s (Fin.castLE ha k) * ((B k l l : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) / c * ((B k l l : ℤ) : ℂ) :=
      fun l => Finset.sum_congr rfl fun k _ => by ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hee : F (e i) (logExp a s) = F (Pi.single i 1) (logExp a s) := rfl
      rw [hee, ← hi, hsum1 i]
      ring
    · simp only [if_neg hij]
      have hp := hFe (e i + e j) s hs hsB
      simp only [e, cast_single_add, quad_add] at hp
      have hsi : (τ s) j i = (τ s) i j := ((hsym s hs hsB).1.apply i j)
      have hbi : ∀ k, B k j i = B k i j := fun k => (hBsym k).apply i j
      have hsum2 : ∑ k, s (Fin.castLE ha k) * ((B k i i + B k i j + B k j i + B k j j : ℤ) : ℂ) / c =
          ∑ k, s (Fin.castLE ha k) * ((B k i i : ℤ) : ℂ) / c + 2 * ∑ k, s (Fin.castLE ha k) / c * ((B k i j : ℤ) : ℂ) +
            ∑ k, s (Fin.castLE ha k) * ((B k j j : ℤ) : ℂ) / c := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hbi k]; push_cast; ring
      rw [hsum2] at hp
      rw [← hp, ← hi, ← hj, hsi]
      ring

end GlobalTheory.ShFam.Hor.LogCh.PerExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixBoundaryExtensionMonodromyPosSemidefStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | exact GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension <;> assumption)
end
end

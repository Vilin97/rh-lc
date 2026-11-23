module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecSmOfDecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PmInduction
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJOfSigLam

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Equiv

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem dSW_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ x : H₁, dSW σ₂ w (U x) = U (dSW σ₁ w x)
  | [], _, _ => rfl
  | X :: w, hw, x => by
    simp only [dSW]
    rw [dSW_map_isometry U hU w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) x,
      dS_map_isometry U hU (hw X List.mem_cons_self)]

theorem nuJ_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (x : H₁) :
    nuJ σ₂ Ws (U x) = nuJ σ₁ Ws x := by
  delta nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [dSW_map_isometry U hU w (hWs w hw) x, U.norm_map]

end Equiv

theorem decBoundJ_of_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) (m N : ℕ) (hL : DecBoundJ ε (sigLam ε Ψ v₀) m N) :
    DecBoundJ ε σ m N := by
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hstd hP hv₀
  obtain ⟨C, Ws, hWs, hB⟩ := hL
  have hWs' : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  refine ⟨C, Ws, hWs, fun u v hu hv g hg => ?_⟩
  obtain ⟨x, rfl⟩ := U.surjective u
  obtain ⟨y, rfl⟩ := U.surjective v
  have hx := smooth_symm_of_isometry U hU hu
  have hy := smooth_symm_of_isometry U hU hv
  rw [U.symm_apply_apply] at hx hy
  have hb := hB x y hx hy g hg
  rw [← hU g hg x, U.inner_map_map, nuJ_map_isometry U hU hWs' x, nuJ_map_isometry U hU hWs' y]
  exact hb

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.HsPowMulLe

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem hs_pow_mul_le (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) {c A : ℝ} (hc : 0 ≤ c)
    (h : ∀ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ ≤ A) :
    Real.sqrt (S7.hs g) ^ m * c ≤ (n : ℝ) ^ (2 * m) * A := by
  have hsq : Real.sqrt (S7.hs g) ≤ ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ := by
    have h1 : S7.hs g = ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 := by
      rw [S7.hs, ← Finset.univ_product_univ, Finset.sum_product]
    have h2 : ∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖ ^ 2 ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ 2 := by
      rw [sq (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖), Finset.sum_mul]
      refine Finset.sum_le_sum fun ab _ => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun ab : Fin n × Fin n => ‖g ab.1 ab.2‖)
        (fun (i : Fin n × Fin n) _ => norm_nonneg (g i.1 i.2)) (Finset.mem_univ ab)) (norm_nonneg (g ab.1 ab.2))
    rw [h1, Real.sqrt_le_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    exact h2
  have hpow : (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m =
      ∑ idx : Fin m → Fin n × Fin n, ∏ t, ‖g (idx t).1 (idx t).2‖ := by
    rw [← Fin.prod_const, Finset.prod_univ_sum]
    rfl
  calc Real.sqrt (S7.hs g) ^ m * c ≤ (∑ ab : Fin n × Fin n, ‖g ab.1 ab.2‖) ^ m * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq m) hc
    _ = ∑ idx : Fin m → Fin n × Fin n, c * ∏ t, ‖g (idx t).1 (idx t).2‖ := by
        rw [hpow, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∑ _idx : Fin m → Fin n × Fin n, A := Finset.sum_le_sum fun idx _ => h idx
    _ = (n : ℝ) ^ (2 * m) * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [Fintype.card_fin]; push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem hs_eq_of_compact {n : ℕ} {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : S7.hs g = n := by
  have h2 : inUJ ε g := hg
  delta inUJ Jm at h2
  delta pOf qOf at hpq
  have hU : g.conjTranspose * g = 1 := by
    rcases hpq with hp | hq
    · have hall : ∀ a, ε a = false := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = -1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
    · have hall : ∀ a, ε a = true := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hq) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
  delta S7.hs
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, ‖g i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have hjj := congrFun (congrFun hU j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
    have hc : ∀ i, g.conjTranspose j i * g i j = ((‖g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [hc] at hjj
    exact_mod_cast hjj
  simp [key]

theorem decBound_of_compact {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0) (m N : ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m N := by
  obtain ⟨_, _, hU, _⟩ := hσ
  refine ⟨Real.sqrt (n : ℝ) ^ m, [[]], ?_, ?_⟩
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp
  · intro u v _ _ g hg
    have hn : S7.hs g = n := hs_eq_of_compact hpq hg
    have hnorm : ‖σ g u‖ = ‖u‖ := hU.2.1 g hg u
    simp only [nuJ, dSW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hn, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
    calc ‖inner ℂ v (σ g u)‖ ≤ ‖v‖ * ‖σ g u‖ := norm_inner_le_norm v (σ g u)
      _ = ‖u‖ * ‖v‖ := by rw [hnorm, mul_comm]

theorem decSmJ {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (m : ℕ) (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m (m * (n - 1)) := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · exact decBound_of_compact hpq m _ hσ
  have hp : 1 ≤ pOf ε := by omega
  have hq : 1 ≤ qOf ε := by omega
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have hth : thrStar ε < h := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε := le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hlam hgap hq0 h8
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨C, hC⟩ := pm_induction hp hq m hlam hgap hm hP hv₀
  refine decBoundJ_of_sigLam hlam hgap hth hP hv₀ hσ m _ ?_
  refine decBoundJ_sigLam hlam hstd hP hv₀ m _ ⟨(n : ℝ) ^ (2 * m) * C, fun x hx y hy g hg => ?_⟩
  have := hs_pow_mul_le m g (norm_nonneg _) fun idx => hC x hx y hy g hg idx
  calc _ ≤ _ := this
    _ = _ := by ring

theorem decSm {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m : ℕ)
    (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ m * (2 * r + k) ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hJ := decSmJ ((mir_isHCParam_iff lam).1 hlam) ((mir_gapAtLeast_iff ε lam h).1 hgap) m hm hDS
  have hN : m * (2 * r + k + 1 - 1) = m * (2 * r + k) := by rw [Nat.add_sub_cancel]
  rw [hN] at hJ
  exact decSm_of_decBoundJ hP m _ hJ

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

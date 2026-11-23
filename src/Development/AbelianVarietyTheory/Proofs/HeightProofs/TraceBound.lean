module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EllipticEstimateWordLeOnePlusLaplacianPowStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesPropsStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidt

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrame

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have h := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, hL, Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

theorem frame_sm_sum {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Sm ε σ (∑ i, c i • x i) :=
  (smooth (Jm ε) σ).sum_mem fun i _ => (smooth (Jm ε) σ).smul_mem (c i) (hx i)

theorem frame_dRep2_sum (hσ : IsURepOn (UJset ε) σ) {X : Mx n} (hX : X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    dRep σ X (dRep σ X (∑ i, c i • x i)) = ∑ i, c i • dRep σ X (dRep σ X (x i)) := by
  have := frame_Dw_sum hσ (l := [X, X]) (by simp [hX]) c hx
  simpa [Dw] using this

theorem frame_lapOne_sum (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    lapOne ε σ (∑ i, c i • x i) = ∑ i, c i • lapOne ε σ (x i) := by
  simp only [lapOne, onePlusCas, frame_dRep2_sum hσ (hk _) c hx, frame_dRep2_sum hσ (hp _) c hx,
    smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (γ := Fin q), Finset.sum_comm (γ := Fin q)]

theorem frame_lapOne_eig {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {e : H} (he : Sm ε σ e) {μ : ℝ} (h : onePlusCas σ (kB ε) e = (μ : ℂ) • e) :
    lapOne ε σ e = (((2 * μ : ℝ) : ℂ) - (1 + χ)) • e := by
  have hs : ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) e) = e - (μ : ℂ) • e := by
    rw [← h, onePlusCas]; abel
  rw [lapOne, hcas e he, hs, h]
  push_cast
  module

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_iterate (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} {e : Fin q → H} (he : ∀ j, Sm ε σ (e j)) (c : Fin q → ℂ) (hc : ∀ j, lapOne ε σ (e j) = c j • e j)
    (r : ℕ) (b : Fin q → ℂ) :
    (lapOne ε σ)^[r] (∑ j, b j • e j) = ∑ j, (b j * c j ^ r) • e j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, frame_lapOne_sum hσ hk hp _ he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, smul_smul, pow_succ, mul_assoc]

theorem frame_norm_sq {q : ℕ} {e : Fin q → H} (ho : Orthonormal ℂ e) (d : Fin q → ℂ) :
    ‖∑ j, d j • e j‖ ^ 2 = ∑ j, ‖d j‖ ^ 2 := by
  have h := ho.inner_sum d d Finset.univ
  rw [@norm_sq_eq_re_inner ℂ, h]

  simp only [Complex.conj_mul', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.re_to_complex]
  norm_cast

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_coef_bound (χ : ℂ) {μ : ℝ} (hμ : 1 ≤ μ) {s₀ s : ℕ} (hs : s₀ ≤ s) (z : ℂ) :
    ‖((((μ ^ s)⁻¹ : ℝ) : ℂ) * z) * (((2 * μ : ℝ) : ℂ) - (1 + χ)) ^ s₀‖ ≤ (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by
  have hc : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ (2 + ‖1 + χ‖) * μ := by
    calc ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ ‖((2 * μ : ℝ) : ℂ)‖ + ‖1 + χ‖ := norm_sub_le _ _
      _ = 2 * μ + ‖1 + χ‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ _ := by nlinarith [norm_nonneg (1 + χ)]
  have hμs : 0 < μ ^ s := pow_pos (by linarith) _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hμs.le)]
  have h1 : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀ ≤ ((2 + ‖1 + χ‖) * μ) ^ s₀ := pow_le_pow_left₀ (norm_nonneg _) hc s₀
  have h2 : μ ^ s₀ ≤ μ ^ s := pow_le_pow_right₀ hμ hs
  have hK : 0 ≤ (2 + ‖1 + χ‖) ^ s₀ := by positivity
  rw [mul_pow] at h1
  calc (μ ^ s)⁻¹ * ‖z‖ * ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀
      ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s₀) := by gcongr
    _ ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s) := by gcongr
    _ = (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by field_simp

theorem frame_word (hσ : IsURepOn (UJset ε) σ) (hKS : ∀ v, IsKFin ε σ v → Sm ε σ v)
    (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε) {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {m : List (Mx n)} (hm : ∀ X ∈ m, X ∈ lieSet ε) {s₀ : ℕ} {C₀ : ℝ}
    (hest : ∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) {s : ℕ} (hs : s₀ ≤ s)
    {q : ℕ} {e : Fin q → H} {μ : Fin q → ℝ} (ho : Orthonormal ℂ e) (hkf : ∀ i, IsKFin ε σ (e i))
    (hμ : ∀ i, 1 ≤ μ i) (heig : ∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) (z : Fin q → ℂ) :
    ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤
      (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) * ∑ j, ‖z j‖ ^ 2 := by
  have he : ∀ j, Sm ε σ (e j) := fun j => hKS _ (hkf j)
  have hc : ∀ j, lapOne ε σ (e j) = (fun j => ((2 * μ j : ℝ) : ℂ) - (1 + χ)) j • e j := fun j =>
    frame_lapOne_eig hcas (he j) (heig j)
  rw [← frame_Dw_sum hσ hm _ he]
  have h1 := hest _ (frame_sm_sum (fun j => (((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) he)
  rw [frame_iterate hσ hk hp he _ hc s₀] at h1
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, frame_norm_sq ho] at h3
  refine h3.trans ?_
  rw [mul_assoc (max C₀ 0 ^ 2), Finset.mul_sum Finset.univ (fun j => ‖z j‖ ^ 2) ((2 + ‖1 + χ‖) ^ (2 * s₀))]
  gcongr with j
  have := frame_coef_bound χ (hμ j) hs (z j)
  calc _ ≤ ((2 + ‖1 + χ‖) ^ s₀ * ‖z j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := by ring

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

theorem frame_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  intro n ε H _ _ _ σ hstd hk hp χ hcas hell T hT
  have hσ := hstd.1
  have hKS := hstd.2.2.1
  have key : ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∃ (s₀ : ℕ) (C₀ : ℝ),
      s₀ ≤ s ∧ (∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) ∧
        max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀) ≤ C := by
    intro T
    induction T with
    | nil => intro _; exact ⟨0, 0, by simp⟩
    | cons m T ih =>
      intro hT
      obtain ⟨s₁, C₁, h₁⟩ := ih (fun l hl => hT l (List.mem_cons_of_mem _ hl))
      obtain ⟨s₀, C₀, h₀⟩ := hell m (hT m List.mem_cons_self)
      refine ⟨max s₀ s₁, max (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) C₁, fun l hl => ?_⟩
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨s₀, C₀, le_max_left _ _, h₀, le_max_left _ _⟩
      · obtain ⟨s', C', hs', he', hC'⟩ := h₁ l hl
        exact ⟨s', C', hs'.trans (le_max_right _ _), he', hC'.trans (le_max_right _ _)⟩
  obtain ⟨s, C, hsC⟩ := key T hT
  refine ⟨s, C, fun m hm q e μ ho hkf hμ heig z => ?_⟩
  obtain ⟨s₀, C₀, hs, hest, hC⟩ := hsC m hm
  exact (frame_word hσ hKS hk hp hcas (hT m hm) hest hs ho hkf hμ heig z).trans
    (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun j _ => by positivity))

end GlobalTheory.TypeSum.CasBasis

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.WordsOnWeightedCasimirEigenvectorsBoundedFrameStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace


theorem _root_.GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.frame_bounded | exact GlobalTheory.TypeSum.CasBasis.frame_bounded | (intros; apply GlobalTheory.TypeSum.CasBasis.frame_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.TraceBound

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.TraceBound

theorem trace_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε ∧ (X i)ᴴ = -X i ∧ hs (X i) ≤ 1) ∧ ∀ S : List (List (Mx n)), Words (lieSet ε) S → ∃ (r : ℕ) (A : ℝ), ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ S (e i) ^ 2 / μ i ^ r ≤ A := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨hk, hp⟩ := GlobalTheory.T.indefinite_unitary_lie_orthonormal_bases_props n ε
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors n ε H σ hσ
  refine ⟨_, kB ε, hk, fun S hS => ?_⟩
  obtain ⟨S0, C0, hS0, hC0, HS⟩ := SobHS.sobolev_hilbertSchmidt n ε H σ hσ
  have hT : Words (lieSet ε) (S.flatMap fun l => S0.map (· ++ l)) := by
    intro m hm X hX
    obtain ⟨l, hl, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hm
    exact (List.mem_append.1 hX).elim (hS0 l' hl' X) (hS l hl X)
  obtain ⟨s, C, hC⟩ := GlobalTheory.T.words_on_weighted_casimir_eigenvectors_bounded_frame n ε H σ hσ (fun i => (hk i).1) (fun b => (hp b).1) χ hχ (GlobalTheory.T.elliptic_estimate_word_le_onePlusLaplacian_pow n ε H σ hσ) _ hT
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨2 * s, S.length * (S.length * (C0 * C')), fun q e μ he hK hμ heig => ?_⟩
  have hsm : ∀ j, Sm ε σ (e j) := fun j => hσ.2.2.1 _ (hK j)
  have hμ0 : ∀ j, 0 < μ j := fun j => lt_of_lt_of_le one_pos (hμ j)

  have key : ∀ l ∈ S, ∑ j, ‖Dw σ l (e j)‖ ^ 2 / μ j ^ (2 * s) ≤ C0 * C' := by
    intro l hl
    have hlw : ∀ X ∈ l, X ∈ lieSet ε := hS l hl
    set c : Fin q → ℝ := fun j => (μ j ^ s)⁻¹ with hc
    have hc0 : ∀ j, 0 ≤ c j := fun j => inv_nonneg.2 (pow_nonneg (hμ0 j).le _)
    set x : Fin q → H := fun j => ((c j : ℝ) : ℂ) • Dw σ l (e j) with hx
    have hxs : ∀ j, Sm ε σ (x j) := fun j =>
      sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ((hsm j).word hσ.1 hlw)))
    have hframe : ∀ l' ∈ S0, ∀ z : Fin q → ℂ, ‖∑ j, z j • Dw σ l' (x j)‖ ^ 2 ≤ C' * ∑ j, ‖z j‖ ^ 2 := by
      intro l' hl' z
      have e1 : ∀ j, z j • Dw σ l' (x j) = (((c j : ℝ) : ℂ) * z j) • Dw σ (l' ++ l) (e j) := fun j => by
        rw [hx, Dw_smul hσ.1 (hS0 l' hl') _ ((hsm j).word hσ.1 hlw), Dw_append, smul_smul, mul_comm]
      simp only [e1]
      have hm : l' ++ l ∈ S.flatMap fun l => S0.map (· ++ l) :=
        List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨l', hl', rfl⟩⟩
      refine (hC _ hm q e μ he hK hμ heig z).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => by positivity)
    have hH := HS (Fin q) x x C' hC'0 hxs hframe
    have eQ : ∑ j, ⟪x j, x j⟫_ℂ = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq_to_K (x j)
    rw [eQ, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hH
    have hQ0 : 0 ≤ ∑ j, ‖x j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hQ : ∑ j, ‖x j‖ ^ 2 ≤ C0 * C' := by
      by_contra hne
      push_neg at hne
      have hK0 : 0 ≤ C0 * C' := mul_nonneg hC0 hC'0
      nlinarith
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) hQ
    rw [hx]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 j), mul_pow, hc, inv_pow, ← pow_mul,
      mul_comm s 2, div_eq_mul_inv, mul_comm]

  have hcs : ∀ j, sobNorm σ S (e j) ^ 2 ≤ S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2 := by
    intro j
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin S.length)))
      (f := fun i => ‖Dw σ S[i] (e j)‖)
    rw [Finset.card_univ, Fintype.card_fin] at this
    unfold sobNorm
    rw [← Fin.sum_univ_fun_getElem]
    exact this
  calc ∑ j, sobNorm σ S (e j) ^ 2 / μ j ^ (2 * s)
      ≤ ∑ j, (S.length * ∑ i : Fin S.length, ‖Dw σ S[i] (e j)‖ ^ 2) / μ j ^ (2 * s) :=
        Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hcs j) (pow_nonneg (hμ0 j).le _)
    _ = S.length * ∑ i : Fin S.length, ∑ j, ‖Dw σ S[i] (e j)‖ ^ 2 / μ j ^ (2 * s) := by
        simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc]
        exact Finset.sum_comm
    _ ≤ S.length * ∑ _i : Fin S.length, C0 * C' := by
        gcongr with i
        exact key _ (List.getElem_mem _)
    _ = S.length * (S.length * (C0 * C')) := by simp

end GlobalTheory.TypeSum.TraceBound
end
end

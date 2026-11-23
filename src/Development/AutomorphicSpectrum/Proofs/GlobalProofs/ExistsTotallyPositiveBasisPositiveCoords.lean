module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrank

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard

theorem finite_and_card_realEmbeddings (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  have e : (F →+* ℝ) ≃ (F →+* ℂ) :=
    { toFun := fun σ => Complex.ofRealHom.comp σ
      invFun := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
      left_inv := fun σ => by
        ext x
        apply Complex.ofReal_injective
        simp [ComplexEmbedding.IsReal.coe_embedding_apply]
      right_inv := fun φ => by
        ext x
        simp [ComplexEmbedding.IsReal.coe_embedding_apply] }
  have hc : Nat.card (F →+* ℂ) = Module.finrank ℚ F := by
    rw [Nat.card_eq_fintype_card]
    exact Embeddings.card F ℂ
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrankStatement

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.card_real_embeddings_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.DiagDom

theorem perturb_bound {κ : Type} [Fintype κ] [DecidableEq κ] (W : κ → κ → ℝ) (ε C : ℝ)
    (hW : ∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) (c : κ → ℝ)
    (hC : ∀ i, |c i| ≤ C) (σ : κ) :
    |∑ i, W σ i * c i - c σ| ≤ (Fintype.card κ : ℝ) * ε * C := by
  have hrw : ∑ i, W σ i * c i - c σ = ∑ i, (W σ i - if σ = i then 1 else 0) * c i := by
    simp [sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [hrw]
  calc |∑ i, (W σ i - if σ = i then 1 else 0) * c i|
      ≤ ∑ i, |(W σ i - if σ = i then 1 else 0) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : κ, ε * C := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hW σ i).le (hC i) (abs_nonneg _) ((abs_nonneg _).trans (hW σ i).le)
    _ = (Fintype.card κ : ℝ) * ε * C := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem small_perturbation_injective_pos :
    ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ,
      (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
      (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
      ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) →
        (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  intro κ _ _ M
  have hn0 : (0 : ℝ) ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hM1 : 0 < |M| + 1 := by positivity
  refine ⟨1 / (2 * ((Fintype.card κ : ℝ) + 1) * (|M| + 1)), by positivity, fun W hW => ?_⟩
  set n : ℝ := (Fintype.card κ : ℝ) with hn
  set ε := 1 / (2 * (n + 1) * (|M| + 1)) with hε
  have hδ : n * ε * (2 * (|M| + 1)) ≤ 1 := by
    have e : n * ε * (2 * (|M| + 1)) = n / (n + 1) := by
      rw [hε]
      field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 ≤ n * ε := by positivity
  have hδh : n * ε ≤ 1 / 2 := by nlinarith [abs_nonneg M]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨fun c _ => funext fun i => (IsEmpty.false i).elim, fun c _ _ i => (IsEmpty.false i).elim⟩
  have bound : ∀ c : κ → ℝ, ∃ j, ∀ σ,
      |∑ i, W σ i * c i - c σ| ≤ n * ε * |c j| ∧ |c σ| ≤ |c j| := by
    intro c
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) Finset.univ_nonempty
    exact ⟨j, fun σ => ⟨perturb_bound W ε |c j| hW c (fun i => hj i (Finset.mem_univ i)) σ,
      hj σ (Finset.mem_univ σ)⟩⟩
  constructor
  · intro c hc
    obtain ⟨j, hj⟩ := bound c
    have h1 := (hj j).1
    rw [hc j, zero_sub, abs_neg] at h1
    have hC : |c j| = 0 := by nlinarith [abs_nonneg (c j)]
    funext i
    have h2 := (hj i).2
    rw [hC] at h2
    exact abs_nonpos_iff.mp h2
  · intro c hpos hratio i
    obtain ⟨j, hj⟩ := bound c
    have hC0 : 0 ≤ |c j| := abs_nonneg _
    have h1 : |c j| ≤ ∑ k, W j k * c k + n * ε * |c j| := by
      have e := abs_sub_abs_le_abs_sub (c j) (∑ k, W j k * c k)
      rw [abs_sub_comm (c j), abs_of_pos (hpos j)] at e
      linarith [(hj j).1]
    have h2 : ∑ k, W i k * c k - n * ε * |c j| ≤ c i := by
      linarith [(abs_le.mp (hj i).1).2]
    have h3 := hratio j i
    have hyi := hpos i
    have hMy : M * ∑ k, W i k * c k ≤ |M| * ∑ k, W i k * c k :=
      mul_le_mul_of_nonneg_right (le_abs_self M) hyi.le
    have s1 : n * ε * |c j| * (2 * (|M| + 1)) ≤ |c j| := by
      nlinarith [mul_le_mul_of_nonneg_right hδ hC0]
    have s2 : |c j| * (1 - n * ε) ≤ |M| * ∑ k, W i k * c k := by nlinarith
    have s3 : n * ε * |c j| * (|M| + 1) < (∑ k, W i k * c k) * (|M| + 1) := by
      nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (n * ε))]
    have s4 : n * ε * |c j| < ∑ k, W i k * c k := lt_of_mul_lt_mul_right s3 hM1.le
    linarith

end GlobalTheory.CompanionTheory.DiagDom
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolutionStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.near_identity_matrix_positive_solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  first | exact @GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | exact GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | (intros; apply GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddings

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density

theorem denseRange_real_places (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange fun (x : F) (w : InfinitePlace F) =>
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  have hq : ∀ w : InfinitePlace F, ∃ q : ℚ, |(q : ℝ) - z w| < ε / 2 := by
    intro w
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show z w < z w + ε / 2 by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hq
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (InfinitePlace.denseRange_algebraMap_pi F)
    (fun w => WithAbs.toAbs w.1 ((q w : ℚ) : F)) (ε / 2) (by linarith)
  refine ⟨x, (dist_pi_lt_iff hε).mpr fun w => ?_⟩
  have hxw := (dist_pi_lt_iff (by linarith : (0 : ℝ) < ε / 2)).mp hx w
  try dsimp only at hxw
  rw [Pi.algebraMap_apply, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs,
    WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs, Algebra.algebraMap_self, RingHom.id_apply] at hxw
  have h2 : w.1 ((q w : F) - x) =
      |(q w : ℝ) - InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x| := by
    have h := InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) ((q w : F) - x)
    rw [Real.norm_eq_abs, map_sub, map_ratCast] at h
    exact h.symm
  rw [h2] at hxw
  show dist (z w) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) < ε
  rw [Real.dist_eq]
  have h3 : |z w - (q w : ℝ)| < ε / 2 := by
    rw [abs_sub_comm]
    exact hq w
  linarith [abs_sub_le (z w) (q w : ℝ) (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x)]

theorem exists_place_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : F →+* ℝ) :
    ∃ w : InfinitePlace F, InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) = σ := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp σ), ?_⟩
  ext x
  have h1 := InfinitePlace.embedding_of_isReal_apply
    (IsTotallyReal.isReal (InfinitePlace.mk (Complex.ofRealHom.comp σ))) x
  rw [InfinitePlace.embedding_mk_eq_of_isReal hφ, RingHom.comp_apply, Complex.ofRealHom_eq_coe] at h1
  exact_mod_cast h1

theorem exists_approx : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ),
    0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  intro F _ _ _ y ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_real_places F)
    (fun w => y (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) ε hε
  refine ⟨x, fun σ => ?_⟩
  obtain ⟨w, hw⟩ := exists_place_eq F σ
  have h := (dist_pi_lt_iff hε).mp hx w
  rw [Real.dist_eq, hw, abs_sub_comm] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyRealFieldDenseEmbeddingsStatement

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.totally_real_field_dense_embeddings : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (F →+* ℝ) → ℝ) (ε : ℝ), 0 < ε → ∃ x : F, ∀ σ : F →+* ℝ, |σ x - y σ| < ε := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Density.exists_approx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoords

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens

theorem map_sum_ratSmul {F κ : Type} [Field F] [Fintype κ] (σ : F →+* ℝ) (q : κ → ℚ) (v : κ → F) :
    σ (∑ i, q i • v i) = ∑ i, σ (v i) * (q i : ℝ) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem exists_totPos_basis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  intro F _ _ _ M
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_real_embeddings_eq_finrank F
  letI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  obtain ⟨ε, hε, hW⟩ := GlobalTheory.T.near_identity_matrix_positive_solution (κ := F →+* ℝ) M
  have hex : ∀ i : F →+* ℝ, ∃ v : F, ∀ σ : F →+* ℝ,
      |σ v - ((if σ = i then 1 else 0) + ε / 2)| < ε / 2 :=
    fun i => GlobalTheory.T.totally_real_field_dense_embeddings F (fun σ => (if σ = i then 1 else 0) + ε / 2) (ε / 2) (by positivity)
  choose v hv using hex
  have hclose : ∀ σ i : F →+* ℝ, |σ (v i) - if σ = i then 1 else 0| < ε := by
    intro σ i
    have h := abs_lt.mp (hv i σ)
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  have hpos : ∀ σ i : F →+* ℝ, 0 < σ (v i) := by
    intro σ i
    have h := (abs_lt.mp (hv i σ)).1
    split_ifs at h <;> linarith
  obtain ⟨h1, h2⟩ := hW (fun σ i => σ (v i)) hclose
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq i
    have hz : (fun i => (q i : ℝ)) = 0 := h1 _ fun σ => by
      rw [← map_sum_ratSmul σ q v, hq, map_zero]
    have hi : (q i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  have hcardκ : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : Nonempty (F →+* ℝ) := by
    apply Fintype.card_pos_iff.mp
    rw [hcardκ]
    exact Module.finrank_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcardκ
  have hb : ∀ i, b i = v i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨F →+* ℝ, inferInstance, b, fun i σ => ?_, fun x hx hM i => ?_⟩
  · rw [hb]; exact hpos σ i
  · have hrep : ∀ σ : F →+* ℝ, σ x = ∑ i, σ (v i) * ((b.repr x i : ℚ) : ℝ) := by
      intro σ
      rw [← map_sum_ratSmul σ (fun i => b.repr x i) v]
      congr 1
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.sum_congr rfl fun j _ => by rw [hb]
    have hc := h2 (fun i => ((b.repr x i : ℚ) : ℝ))
      (fun σ => by rw [← hrep σ]; exact hx σ)
      (fun σ τ => by rw [← hrep σ, ← hrep τ]; exact hM σ τ) i
    exact_mod_cast hc

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens
end
end

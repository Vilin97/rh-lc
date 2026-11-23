module

public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChainLowerBound
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainLoweringStatement
public import Development.AbelianVarietyTheory.Definitions.Jets.Imports
public import Formalism.HermitianCurvature.FrameExists2
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntCoordsOfRegularParam

section

@[expose] public section

namespace GlobalTheory

theorem exists_int_coords_of_regular_param (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by
  have key : ∀ j : ℕ, j ≤ n → ∃ z : ℤ, (z : ℝ) = u (j + 1) - u 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨N, hN⟩ := h (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      refine ⟨z - N - 1, ?_⟩
      push_cast
      linarith
  choose z hz using key
  refine ⟨(u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2, fun j => z j (Nat.lt_succ_iff.1 j.2), ?_, ?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    obtain ⟨N, hN⟩ := h (i + 1) (Finset.mem_Icc.2 ⟨by omega, i.2⟩)
    have h1 := hz (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2)
    have h2 := hz (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : ((z (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2) : ℤ) : ℝ)
        < (z (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2) : ℤ) := by
      rw [h1, h2]
      simp only [Fin.val_succ, Fin.val_castSucc]
      linarith
    exact_mod_cast this
  · intro j
    have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hz j (Nat.lt_succ_iff.1 j.2))
    simp only [Complex.ofReal_intCast, Complex.ofReal_sub] at h1
    simp only [h1]
    ring
  · intro i j
    simp only [hz]
    ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaisingStatement

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.exists_wignerContraction_chain_raising : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.chain_raise | exact GlobalTheory.WigSh.chain_raise | (intros; apply GlobalTheory.WigSh.chain_raise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointApplyOfNormPreserving

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqAdjointAddGeOfJointEigenspaces

section

@[expose] public section

namespace GlobalTheory

open scoped InnerProductSpace

theorem norm_sq_adjoint_add_ge_of_joint_eigenspaces (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by
  have hA : ∀ x : V, (⟪A (ContinuousLinearMap.adjoint A x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint A x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hB : ∀ x : V, (⟪B (ContinuousLinearMap.adjoint B x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint B x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsm : ∀ (r : ℝ) (x : V), (⟪(r : ℂ) • x, x⟫_ℂ).re = r * ‖x‖ ^ 2 := by
    intro r x
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let X : V →ₗ[ℂ] V := (A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B : V →L[ℂ] V).toLinearMap
  have hX : ∀ x, X x = A (ContinuousLinearMap.adjoint A x) + B (ContinuousLinearMap.adjoint B x) := fun x => rfl
  have hsym : X.IsSymmetric := by
    intro x y
    rw [hX, hX, inner_add_left, inner_add_right]
    rw [← ContinuousLinearMap.adjoint_inner_right A, ← ContinuousLinearMap.adjoint_inner_right B,
      ← ContinuousLinearMap.adjoint_inner_left A, ← ContinuousLinearMap.adjoint_inner_left B]
  have hge : ∀ i, ∀ x ∈ S i, x ≠ 0 → c ≤ wp i + wm i := by
    intro i x hx hx0
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h1 := hA x
    have h2 := hB x
    rw [(hw i x hx).1, hsm] at h1
    rw [(hw i x hx).2, hsm] at h2
    have p1 : 0 ≤ wp i := by
      have : 0 ≤ wp i * ‖x‖ ^ 2 := by rw [h1]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    have p2 : 0 ≤ wm i := by
      have : 0 ≤ wm i * ‖x‖ ^ 2 := by rw [h2]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    rcases hc i with h | h <;> linarith
  have hev : ∀ (μ : ℝ) (e : V), X e = (μ : ℂ) • e → e ≠ 0 → c ≤ μ := by
    intro μ e he he0
    by_contra hlt
    apply he0
    have hmem : e ∈ (⨆ i, S i)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro i
      rw [Submodule.mem_orthogonal]
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hle := hge i x hx hx0
      have hXx : X x = ((wp i + wm i : ℝ) : ℂ) • x := by
        rw [hX, (hw i x hx).1, (hw i x hx).2, ← add_smul]; push_cast; rfl
      have h := hsym x e
      rw [hXx, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have hne : ((wp i + wm i : ℝ) : ℂ) ≠ (μ : ℂ) := by
        intro h'
        have := Complex.ofReal_injective h'
        apply hlt; linarith
      by_contra h0
      exact hne (mul_right_cancel₀ h0 h)
    rw [hS, Submodule.top_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  set b := hsym.eigenvectorBasis hn with hb
  have hμ : ∀ j, c ≤ hsym.eigenvalues hn j := fun j =>
    hev _ (b j) (hsym.apply_eigenvectorBasis hn j) (b.orthonormal.ne_zero j)
  rw [← hA, ← hB, ← Complex.add_re, ← inner_add_left, ← hX]
  rw [← b.sum_inner_mul_inner (X v) v, Complex.re_sum, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ⟪X v, b j⟫_ℂ = (hsym.eigenvalues hn j : ℂ) * ⟪v, b j⟫_ℂ := by
    rw [hsym v (b j), hb, hsym.apply_eigenvectorBasis hn j, inner_smul_right]; rfl
  rw [h1, mul_assoc, Complex.re_ofReal_mul, ← inner_conj_symm v (b j), Complex.conj_mul']
  have : ((‖⟪b j, v⟫_ℂ‖ : ℂ) ^ 2).re = ‖⟪b j, v⟫_ℂ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hμ j) (sq_nonneg _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound

section

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem exists_shifted_types_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ k r z π u l n₀ b hz hT hπ hreg hl1 hlk hgap hb hn hb1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < n := by omega
  let i : Fin n := ⟨m, hm⟩
  obtain ⟨β, L, hL, hu, hd⟩ := GlobalTheory.exists_int_coords_of_regular_param n u (by simpa using hreg)
  obtain ⟨B, hB⟩ := (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).1
  have hgapZ : L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc := by
    have h := hd i.castSucc i.succ
    simp only [Fin.val_succ, Fin.val_castSucc, i] at h
    have : ((L i.succ + 2 * (n₀ : ℤ) + 1 : ℤ) : ℝ) ≤ ((L i.castSucc : ℤ) : ℝ) := by
      push_cast
      simp only [i]
      linarith
    exact_mod_cast this
  have hwide : (L 0 : ℝ) - (L (Fin.last n) : ℝ) ≤ 2 * b := by
    rw [hd]
    have h1 := abs_le.mp (hb (((0 : Fin (n + 1)) : ℕ) + 1) (by simp))
    have h2 := abs_le.mp (hb (((Fin.last n : Fin (n + 1)) : ℕ) + 1) (by simp))
    linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, πp, Ap, hπp, hAp, hwp⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_raising V n r z π u β L B i.succ n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hj
      have := hL.antitone hj'
      omega)
  obtain ⟨Vm, familyMassRatio, familyMassSecondLine, iM3, πm, Am, hπm, hAm, hwm⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_lowering V n r z π u β L B i.castSucc n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
      have := hL.antitone hj'
      omega)
  refine ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, ?_⟩
  refine GlobalTheory.WigSh.lower_bound_spreads V Vp Vm n r z π πp πm B Ap Am n₀ b hz hT hπ.2.2.2.1 hπp.2.2.2.1
    hπm.2.2.2.1 hB hAp hAm ?_
  intro v
  have hyp := (GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB).1
  have hdec := (Formalism.FourierDecayAlt.P.branching_decomposition V n (EB π B) β L hyp).2
  have hspan : ⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA (EB π B)) (shf β M.1) = ⊤ := by
    rw [← hdec, iSup_subtype]
  have key := GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces V Vp Vm {M : Fin n → ℤ // Box L M}
    (fun M => CapSp (subA (EB π B)) (shf β M.1)) (Ap (B (Fin.last n))) (Am (B (Fin.last n))) _ _
    ((3 * b) ^ (2 * n₀))⁻¹ hspan (fun M w hw => ⟨hwp M.1 w hw, hwm M.1 w hw⟩)
    (fun M => GlobalTheory.WigSh.chain_lower_bound n L M.1 i n₀ b hL M.2 hgapZ hb1 hn hwide) v
  have hpos : 0 < (3 * b) ^ (2 * n₀) := by positivity
  rwa [inv_mul_le_iff₀ hpos] at key

end GlobalTheory.WigSh
end
end

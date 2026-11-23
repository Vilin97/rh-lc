module

public import ReciprocityTheory.DualLattices.MulVecMemPP
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
public import ReciprocityTheory.DualLattices.HasLenLeOfSurj
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthStatement
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: ReciprocityTheory.DualLattices.ThetaQSurj

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section F3c

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}

def bvec (U : UnramData p g v R O σ cp H) (τ : Fin U.m) (s : Fin (U.r τ)) : Fin g → R :=
  ((U.rank τ).some.symm (Pi.single s 1)).1

def thetaL (U : UnramData p g v R O σ cp H) (τ : Fin U.m) : (Fin g → R) →ₗ[R] (Fin (U.r τ) → R) where
  toFun l s := l ⬝ᵥ bvec U τ s
  map_add' l l' := by funext s; simp [add_dotProduct]
  map_smul' r l := by funext s; simp [smul_dotProduct]

lemma theta_kill (U : UnramData p g v R O σ cp H) {τ σ' : Fin U.m} (h : σ' ≠ τ) (μ : Fin g → R) :
    thetaL U τ ((U.εL σ')ᵀ *ᵥ μ) = 0 := by
  funext s
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  show ((U.εL σ')ᵀ *ᵥ μ) ⬝ᵥ bvec U τ s = 0
  rw [hb, mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, U.εL_orth, if_neg h,
    vecMul_zero, zero_dotProduct]

lemma theta_surj (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaL U τ) := by
  intro y
  classical
  have key : ∀ (φ : (Fin g → R) →ₗ[R] R) (z : Fin g → R),
      (fun i => φ (fun j => if i = j then 1 else 0)) ⬝ᵥ z = φ z := by
    intro φ z
    rw [LinearMap.pi_apply_eq_sum_univ φ z, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by simp only [smul_eq_mul]; exact mul_comm _ _
  refine ⟨fun i => ((∑ s, y s • LinearMap.proj s : (Fin (U.r τ) → R) →ₗ[R] R) ∘ₗ
      (U.rank τ).some.toLinearMap ∘ₗ (Matrix.mulVecLin (U.εL τ)).rangeRestrict)
      (fun j => if i = j then 1 else 0), ?_⟩
  funext s
  show _ ⬝ᵥ bvec U τ s = y s
  refine (key _ _).trans ?_
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 ((U.rank τ).some.symm (Pi.single s 1)).2
  have hb : bvec U τ s = U.εL τ *ᵥ x := hx.symm
  have hfix : (Matrix.mulVecLin (U.εL τ)).rangeRestrict (bvec U τ s) =
      (U.rank τ).some.symm (Pi.single s 1) := by
    apply Subtype.ext
    show U.εL τ *ᵥ bvec U τ s = bvec U τ s
    rw [hb, mulVec_mulVec, U.εL_orth, if_pos rfl]
  simp only [LinearMap.comp_apply, hfix, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

def redP (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R)}) :=
  LinearMap.pi fun s => (Ideal.span {(p : R)}).mkQ ∘ₗ LinearMap.proj s

lemma redP_pP {n : ℕ} {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) : redP (p := p) n w = 0 := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  funext s
  show (Ideal.span {(p : R)}).mkQ (((p : R) • w') s) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def thetaQ (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    LieDualModP p R g →ₗ[R] (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
  (Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R))).liftQ (redP (U.r τ) ∘ₗ thetaL U τ)
    (fun w hw => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
      rw [map_smul]
      exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩))

lemma thetaQ_surj (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    Function.Surjective (thetaQ U τ) := by
  intro y
  choose y' hy' using fun s => Submodule.mkQ_surjective (Ideal.span {(p : R)}) (y s)
  obtain ⟨l, hl⟩ := theta_surj U τ y'
  refine ⟨Submodule.Quotient.mk l, ?_⟩
  show redP (p := p) (U.r τ) (thetaL U τ l) = y
  rw [hl]
  funext s
  exact hy' s

end F3c

end ReciprocityTheory.PGsh.Up
end
end
end

-- Source module: ReciprocityTheory.DualLattices.SumX

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem u7F3 : FrobeniusLengthBoundStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hdet hbasis τ N z hN hNsq hz
  have hv : v.Integers R := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj

  have hsqle : sqIdeal (augIdeal H.AA.carrier) ≤ augIdeal H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf, f', hf', rfl⟩
    rw [SetLike.mem_coe]
    obtain ⟨hfA, hf0⟩ := Submodule.mem_inf.1 hf
    obtain ⟨hfA', -⟩ := Submodule.mem_inf.1 hf'
    refine Submodule.mem_inf.2 ⟨H.AA.mul_mem f f' hfA hfA', ?_⟩
    rw [LinearMap.mem_ker] at hf0 ⊢
    simp only [LinearMap.proj_apply, Pi.mul_apply] at hf0 ⊢
    rw [hf0, zero_mul]

  have hkill : ∀ k, D.κ k ≠ τ → thetaQ U τ (H.φ ⟨xL D k, D.x_mem k⟩) = 0 := by
    intro k hk
    obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (H.φ ⟨xL D k, D.x_mem k⟩)
    have hg := phi_x_grade hS D k τ (Ne.symm hk) l hl.symm
    obtain ⟨w', hw'⟩ := (mem_pP _).1 hg
    rw [← hl]
    change redP (U.r τ) (thetaL U τ l) = 0
    have hl_sum : ∑ i, (U.εL i)ᵀ *ᵥ l = l := by
      funext j
      simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      have h1 : ∀ k', ∑ i, U.εL i k' j = (1 : Matrix (Fin g) (Fin g) R) k' j := fun k' => by
        rw [← U.εL_sum, Matrix.sum_apply]
      simp [h1, Matrix.one_apply]
    have hθ : thetaL U τ l = (p : R) • thetaL U τ w' := by

      rw [← hl_sum, map_sum,
      Finset.sum_eq_single τ (fun i _ hi => theta_kill U hi l) (by simp), hw', map_smul]
    rw [hθ]
    exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩)
  have hsx : ∀ d : Ix g → R,
      sumX D d = ∑ k, d k • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) := by
    intro d
    apply Subtype.ext
    simp [sumX]
  let π : (blockL D τ ⧸ N.comap (blockL D τ).subtype) →ₗ[R]
      (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
    (N.comap (blockL D τ).subtype).liftQ
      (thetaQ U τ ∘ₗ H.φ ∘ₗ sumX D ∘ₗ (blockL D τ).subtype) (by
        intro c hc
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hc
        obtain ⟨f, hf, hfc⟩ := hNsq _ hc
        obtain ⟨c', hc', hsub⟩ := sub_lin_mem_sq hv D hdet hbasis (hsqle hf)
        have hcc : c' = (c : Ix g → R) := funext fun k => hinj ((hc' k).trans (hfc k).symm)
        rw [hcc] at hsub
        have hmem : sumX D (c : Ix g → R) ∈ LinearMap.ker H.φ := by
          rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
          have h2 := Submodule.sub_mem _ hf hsub
          rw [sub_sub_cancel] at h2
          simpa [sumX] using h2
        rw [LinearMap.mem_ker] at hmem ⊢
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, hmem, map_zero])
  have hsurj : Function.Surjective π := by
    intro w
    obtain ⟨y, rfl⟩ := thetaQ_surj U τ w
    obtain ⟨f, rfl⟩ := H.cotangent_surjective y
    obtain ⟨c0, -, hsub0⟩ := sub_lin_mem_sq hv D hdet hbasis f.2
    let c : blockL D τ :=
      ⟨fun k => if D.κ k = τ then c0 k else 0, fun k hk => by simp [hk]⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    change thetaQ U τ (H.φ (sumX D (c : Ix g → R))) = thetaQ U τ (H.φ f)
    have hf0 : H.φ f = H.φ (sumX D c0) := by
      rw [← sub_eq_zero, ← map_sub]
      apply LinearMap.mem_ker.1
      rw [H.cotangent_ker_eq, Submodule.mem_comap, Submodule.subtype_apply]
      simpa [sumX] using hsub0
    rw [hf0]
    have hzero : thetaQ U τ (H.φ (sumX D (c0 - (c : Ix g → R)))) = 0 := by

      rw [hsx, map_sum, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_smul, map_smul]
      by_cases hk : D.κ k = τ
      · have hck : (c0 - (c : Ix g → R)) k = 0 := by simp [c, hk]
        rw [hck, zero_smul]
      · rw [hkill k hk, smul_zero]
    rw [map_sub, map_sub, map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  exact hasLen_le_of_surj hv hz (p : R) (U.r τ) π hsurj

end ReciprocityTheory.PGsh.Up
end
end
end

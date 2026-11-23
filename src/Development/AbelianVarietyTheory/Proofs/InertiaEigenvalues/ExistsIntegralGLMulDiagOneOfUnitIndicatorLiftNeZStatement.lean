module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Normed.Group.Ultra

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLeMaxUltra

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.LatL

theorem norm_sub_le_max_ultra' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem exists_glO_pair {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (v w : Fin (r + 1) → F) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) (hwv : w ⬝ᵥ v = 1) :
    ∃ k ∈ glO (r + 1) F, (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧
      w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => ‖w i‖)
  have hw0 : w i₀ ≠ 0 := by
    intro h
    have : w = 0 := funext fun i => norm_le_zero_iff.mp (by simpa [h] using hi₀ i)
    simp [this] at hwv
  have hratio : ∀ i, ‖w i / w i₀‖ ≤ 1 := fun i => by
    rw [norm_div]; exact div_le_one_of_le₀ (hi₀ i) (norm_nonneg _)
  let s : Fin r → Fin (r + 1) := i₀.succAbove
  have hs : ∀ c, s c ≠ i₀ := fun c => Fin.succAbove_ne i₀ c
  let u : Fin r → Fin (r + 1) → F := fun c =>
    Pi.single (s c) 1 - (w (s c) / w i₀) • Pi.single i₀ 1
  let ρ : Fin r → Fin (r + 1) → F := fun c => Pi.single (s c) 1 - v (s c) • w
  let col : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases v u
  let row : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases w ρ
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => col b a
  let L : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => row a b
  have hwu : ∀ c, w ⬝ᵥ u c = 0 := by
    intro c
    simp only [u, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
    field_simp; ring
  have hdot : ∀ a b, row a ⬝ᵥ col b = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b := by
    intro a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [row, col, hwv]
      | cast c => simp [row, col, hwu, Matrix.one_apply, (Fin.castSucc_lt_last c).ne']
    | cast c =>
      induction b using Fin.lastCases with
      | last =>
        simp [row, col, ρ, sub_dotProduct, smul_dotProduct, single_dotProduct, hwv,
          Matrix.one_apply, (Fin.castSucc_lt_last c).ne]
      | cast c' =>
        simp only [row, col, Fin.lastCases_castSucc, ρ, sub_dotProduct, smul_dotProduct,
          single_dotProduct, hwu, smul_eq_mul, mul_zero, sub_zero, one_mul, u, Pi.sub_apply,
          Pi.smul_apply, Pi.single_apply, hs c, if_false, mul_zero, sub_zero, Matrix.one_apply,
          Fin.castSucc_inj]
        by_cases h : c = c'
        · subst h; simp
        · have : s c ≠ s c' := fun e => h (Fin.succAbove_right_injective e)
          simp [this, h]
  have hLK : L * K = 1 := by
    ext a b
    rw [← hdot a b]
    simp [L, K, Matrix.mul_apply, dotProduct]
  have hKL : K * L = 1 := mul_eq_one_comm.mp hLK
  let k : GL (Fin (r + 1)) F := ⟨K, L, hKL, hLK⟩
  have hsingle : ∀ i j : Fin (r + 1), ‖(Pi.single i (1 : F) : Fin (r + 1) → F) j‖ ≤ 1 := by
    intro i j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : ∀ b a, ‖col b a‖ ≤ 1 := by
    intro b a
    induction b using Fin.lastCases with
    | last => simpa [col] using hv a
    | cast c =>
      simp only [col, Fin.lastCases_castSucc, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hratio _) (norm_nonneg _) (hsingle _ _)
  have hrow : ∀ a b, ‖row a b‖ ≤ 1 := by
    intro a b
    induction a using Fin.lastCases with
    | last => simpa [row] using hw b
    | cast c =>
      simp only [row, Fin.lastCases_castSucc, ρ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hv _) (norm_nonneg _) (hw _)
  refine ⟨k, fun i j => ⟨by simpa [k, K] using hcol j i, by simpa [k, L] using hrow i j⟩, ?_, ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext a
    change col (Fin.last r) a = v a
    simp [col]
  · ext b
    rw [show (w ᵥ* (k : Matrix _ _ F)) b = row (Fin.last r) ⬝ᵥ col b by
      simp [k, K, row, Matrix.vecMul, dotProduct]]
    rw [hdot, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]

theorem glO_transitive_pairs : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v w : Fin (r + 1) → F), (∀ i, ‖v i‖ ≤ 1) →
    (∀ i, ‖w i‖ ≤ 1) → w ⬝ᵥ v = 1 → ∃ k ∈ glO (r + 1) F,
      (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧ w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  intro F E _ _ _ _ hU r v w hv hw hwv
  haveI : IsUltrametricDist F := hU.ultraF
  exact exists_glO_pair r v w hv hw hwv

end GlobalTheory.LatL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem exists_emb_of_last {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl

end GlobalTheory.JR.GLift

namespace GlobalTheory.JR.GLift

theorem support_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
      ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  intro F E _ _ _ _ _ r Z μ l hμ g hg
  classical
  obtain ⟨-, hb, hc, -⟩ := Set.mem_of_indicator_ne_zero hg
  simp only [act, GlobalTheory.JR.Step.lift] at hb hc
  set e : Fin (r + 1) → F := GlobalTheory.JR.Step.eL r F with he
  have hv : ∀ i, ‖((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) i‖ ≤ 1 := by
    intro i
    have := hb i
    rwa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hμ, one_mul] at this
  have hw : ∀ i, ‖(e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) i‖ ≤ 1 := hc
  have hgg : ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul g
  have hee : e ⬝ᵥ e = 1 := by simp [he, GlobalTheory.JR.Step.eL]
  have hwv : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ⬝ᵥ ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hee]
  obtain ⟨k, hk, hkv, hkw⟩ := GlobalTheory.LatL.glO_transitive_pairs F E r _ _ hv hw hwv
  have hkv' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e = (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e := hkv
  have hkw' : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ᵥ* (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e := hkw
  have hkk : ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul k
  have hkk' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.mul_inv k
  have hek : e ᵥ* ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    conv_lhs => rw [← hkw']
    rw [Matrix.vecMul_vecMul, hkk', Matrix.vecMul_one]
  obtain ⟨s, hs⟩ := exists_emb_of_last r (k⁻¹ * g) (by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hkv', Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec])
    (by rw [Units.val_mul, ← Matrix.vecMul_vecMul, hek, Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one])
  exact ⟨k, hk, s, by rw [← hs, mul_inv_cancel_left]⟩

end GlobalTheory.JR.GLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  first | exact @GlobalTheory.JR.GLift.support_lift | exact GlobalTheory.JR.GLift.support_lift | (intros; apply GlobalTheory.JR.GLift.support_lift <;> assumption)
end
end

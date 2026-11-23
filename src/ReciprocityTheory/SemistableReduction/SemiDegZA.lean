module

public import ReciprocityTheory.SemistableReduction.SemiDegSt
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.SemistableReduction.SemiDegE
public import ReciprocityTheory.SemistableReduction.SemiDegF
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.SemistableReduction.SemiDegM
public import ReciprocityTheory.SemistableReduction.SemiDegW
public import ReciprocityTheory.SemistableReduction.SemiDegZ

-- Source module: Lemmata.GeneralBFactSecondAlt.Imports

section

@[expose] public section

namespace Bl.general_b_fact_second_alt

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)) (v : Fin r → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (a : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} a 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} a v)) := by
  intro K _ _ r L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨(d : NumberField.RingOfIntegers K) * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ha, ?_⟩
    have key : ((d : NumberField.RingOfIntegers K) * a) • (c • x) = n • (a • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * a), ← algebraMap_smul K a,
        ← algebraMap_smul K n, smul_smul, smul_smul]
      simp only at hnd
      rw [← hnd, map_mul]
      congr 1
      ring
    rw [key]
    exact L.smul_mem n hax

end Bl.general_b_fact_second_alt
end
end

-- Source module: ReciprocityTheory.SemistableReduction.SemiDegG

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem herm_cGP {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (a b : Fin r) :
    S.c (((P.map S.c)ᵀ * S.G * P) a b) = ((P.map S.c)ᵀ * S.G * P) b a := by

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
  S.c_invol, S.G_herm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem g_fix {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K)
    (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g) (i : Fin r) (h1 : m ≤ (i : ℕ))
    (h2 : (i : ℕ) + m < r) : S.c (g i) = g i := by
  have h := herm_cGP S P i i
  rw [hJ] at h
  simpa [wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2] using h

theorem exists_adapted_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ)
    (hP : P.det ≠ 0) (h2m : 2 * m ≤ r) (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g)
    (hdd : ∀ i, 0 < dd i) (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) :
    ∃ M : Majorant S, ∀ σ,
      M.H σ = ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ := by
  classical
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hG : S.G = ((P⁻¹).map S.c)ᵀ * wittMat r m g * P⁻¹ := by
    rw [← hJ]
    have h1 : ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP,
        Matrix.map_one _ (map_zero S.c) (map_one S.c), Matrix.transpose_one]
    calc S.G = ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ * S.G * (P * P⁻¹) := by
          rw [h1, hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

  have key : ∀ σ : K →+* ℂ,
      let A := (P⁻¹).map σ
      let D := diagMet (adMet r m g dd) σ
      (Aᴴ * D * A).PosDef ∧ Aᴴ * D * A * (S.G.map σ)⁻¹ * (Aᴴ * D * A) = S.G.map σ := by
    intro σ A D
    set Ai := P.map σ with hAi
    have e1 : A * Ai = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e2 : Ai * A = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e3 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    have e4 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
    have hpos : ∀ i, 0 < adMet r m g dd σ i := adMet_pos r m g dd hdd hg σ
    let Dinv : Matrix (Fin r) (Fin r) ℂ :=
      diagonal fun i => (((adMet r m g dd σ i : ℝ) : ℂ))⁻¹
    have e5 : D * Dinv = 1 := by
      simp only [D, Dinv, diagMet, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have : ((adMet r m g dd σ i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      exact mul_inv_cancel₀ this
    have hGσ : S.G.map σ = Aᴴ * (wittMat r m g).map σ * A := by
      rw [hG, Matrix.map_mul, Matrix.map_mul]
      congr 2
      ext a b
      simp [A, Matrix.conjTranspose_apply, S.c_emb]
    have hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i) := by
      intro i h1 h2
      rw [← S.c_emb, g_fix S P m g hJ i h1 h2]
    have hKey : (wittMat r m g).map σ * Dinv * (wittMat r m g).map σ = D := by
      rw [wittMat_map_mul]
      simp only [D, diagMet]
      congr 1
      funext i
      exact wVal_adMet r m g dd h2m hg σ hreal i
    set Y := S.G.map σ with hY
    set Jσ := (wittMat r m g).map σ with hJσ
    set H := Aᴴ * D * A with hH
    set Hinv := Ai * Dinv * Aiᴴ with hHinv
    have hHH : H * Hinv = 1 := by
      calc H * Hinv = Aᴴ * D * (A * Ai) * Dinv * Aiᴴ := by simp only [H, Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (D * Dinv) * Aiᴴ := by rw [e1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e5, Matrix.mul_one, e4]
    have hHH' : Hinv * H = 1 := mul_eq_one_comm.1 hHH
    have hYHY : Y * Hinv * Y = H := by
      rw [hGσ]
      calc Aᴴ * Jσ * A * Hinv * (Aᴴ * Jσ * A)
          = Aᴴ * Jσ * (A * Ai) * Dinv * (Aiᴴ * Aᴴ) * Jσ * A := by
            simp only [Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (Jσ * Dinv * Jσ) * A := by
            rw [e1, e3, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hKey]
    have hYinv : Y⁻¹ = Hinv * Y * Hinv := by
      apply Matrix.inv_eq_left_inv
      calc Hinv * Y * Hinv * Y = Hinv * (Y * Hinv * Y) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hYHY, hHH']
    refine ⟨?_, ?_⟩
    · have hD : D.PosDef := by
        simp only [D, diagMet]
        exact Matrix.posDef_diagonal_iff.2 fun i => by exact_mod_cast hpos i
      have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2
        (Matrix.isUnit_det_of_right_inverse e1)
      exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAu)
    · rw [hYinv]
      calc H * (Hinv * Y * Hinv) * H = (H * Hinv) * Y * (Hinv * H) := by
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hHH, hHH', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨fun σ => ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ,
    fun σ => (key σ).1, fun σ => (key σ).2, ?_⟩, fun σ => rfl⟩
  intro σ
  have hmap : (P⁻¹).map ((starRingEnd ℂ).comp σ) = ((P⁻¹).map σ).map (starRingEnd ℂ) := by
    rw [Matrix.map_map]
    rfl
  have hDc : diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) =
      (diagMet (adMet r m g dd) σ).map (starRingEnd ℂ) := by
    simp only [diagMet, adMet_conj]
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact (Complex.conj_ofReal (adMet r m g dd σ i)).symm
  show ((P⁻¹).map ((starRingEnd ℂ).comp σ))ᴴ * diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) *
      (P⁻¹).map ((starRingEnd ℂ).comp σ) =
    (((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ).map (starRingEnd ℂ)
  rw [hmap, hDc, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map]
  intro x
  simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
end

-- Source module: ReciprocityTheory.SemistableReduction.SemiDegZA

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem det_map_hom {K L : Type} [Field K] [Field L] {r : ℕ} (f : K →+* L)
    (A : Matrix (Fin r) (Fin r) K) : (A.map f).det = f A.det := (RingHom.map_det f A).symm

theorem gram_det_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (M : Majorant S) (hG : S.G.det ≠ 0) (σ : K →+* ℂ) (b : Fin r → Fin r → K) :
    (gramC (M.H σ) σ b).det.re = ‖σ (hGram S b).det‖ := by
  have hσG : (S.G.map σ).det ≠ 0 := by
    rw [det_map_hom]
    exact fun h => hG (σ.injective (by rw [h, map_zero]))
  have hdet2 : (M.H σ).det * (M.H σ).det = (S.G.map σ).det * (S.G.map σ).det := by
    have h1 := congr_arg Matrix.det (M.major σ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h1
    field_simp at h1
    linear_combination h1
  have hpos := (M.posDef σ).det_pos
  rw [Complex.lt_def] at hpos
  set x : ℝ := (M.H σ).det.re with hx
  have hxH : (M.H σ).det = (x : ℂ) := by
    apply Complex.ext
    · simp [hx]
    · simp [← hpos.2]
  have hx0 : 0 < x := by simpa using hpos.1
  have hxn : x = ‖(S.G.map σ).det‖ := by
    have h1 := congr_arg (‖·‖) hdet2
    simp only [norm_mul, hxH, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at h1
    nlinarith [norm_nonneg (S.G.map σ).det]
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hxH, hGram_eq,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hE : embMat σ b = (colMat b).map σ := rfl
  rw [det_map_hom, hE, det_map_hom, map_mul, map_mul, S.c_emb]
  rw [det_map_hom] at hxn
  set z := σ (colMat b).det
  rw [Complex.star_def, norm_mul, norm_mul, Complex.norm_conj]
  rw [show (starRingEnd ℂ) z * (x : ℂ) * z = (x : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hxn]
  ring

theorem latDeg_L_nonneg (hS : SelfDualIndexStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (M : Majorant S) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : IsLattice L) (hSD : IsSelfDual S L) (hG : S.G.det ≠ 0) (b : Fin r → Fin r → K)
    (hb : IsKBasisIn L b) : 0 ≤ latDeg M.H L b := by
  unfold latDeg
  rw [Finset.sum_congr rfl fun σ _ => by rw [gram_det_majorant S M hG σ b], sum_log_norm_emb]
  have h1 := hS K r S L b hL hSD hb
  have hone : 1 ≤ (spanIdx L b : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero L b hL.1 hb))
  have hlog1 := Real.log_nonneg hone
  by_cases hN0 : |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| = 0
  · rw [hN0, Real.log_zero]
    unfold spanIdx at hlog1
    linarith
  · have h2 := Real.log_le_log (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hN0)) h1
    rw [Real.log_pow] at h2
    unfold spanIdx at h2
    push_cast at h2
    linarith

theorem clear_denom {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)

theorem kBasis_card {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (b : Fin k → Fin r → K)
    (hb : IsKBasisIn L b) : k = r := by
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← hL.2, Submodule.span_le]
    intro x hx
    exact hb.2.2 x hx
  have h := finrank_span_eq_card hb.2.1
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h
  exact h.symm

theorem g_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0) :
    ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0 := by
  classical
  intro i h1 h2 hg
  have ht := haniso (Pi.single i 1) (fun j hj => by
    have : j ≠ i := fun e => by rw [e] at hj; omega
    simp [this]) (by
    rw [Finset.sum_eq_single i]
    · simp [hg]
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ _) h)
  have := congr_fun ht i
  simp at this

theorem semiPoint_of (hW : WittBasisStatement) (hB : LatDegBasisStatement)
    (hN : IntegralIndexStatement) (hS : SelfDualIndexStatement) (hE : GradedExtStatement)
    (hA : AbsDetStatement) : SemiPointStatement := by
  intro K _ _ r S L hL hSD
  have hG := detG_ne_zero S L hL hSD
  obtain ⟨P, m, g, hP, h2m, hJ, haniso⟩ := hW K r S hG
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  set Q := P⁻¹ with hQdef
  have hQ : Q.det ≠ 0 := by
    rw [hQdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hP
  set Lp := L.map (matLin Q) with hLpdef
  have hLp : Lp.FG := hL.1.map _
  have hfix := g_fix S P m g hJ
  have hg0 := g_ne_zero S m g haniso
  have hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp := by
    intro v
    obtain ⟨a, ha, hav⟩ := clear_denom L (P *ᵥ v) (by rw [hL.2]; exact Submodule.mem_top)
    refine ⟨a, ha, ⟨a • (P *ᵥ v), hav, ?_⟩⟩
    rw [map_smul, matLin_apply, Matrix.mulVec_mulVec, hQdef, Matrix.nonsing_inv_mul P hPu,
      Matrix.one_mulVec]
  have hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← hJ, formM_change, matLin_apply, matLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hQdef, Matrix.mul_nonsing_inv P hPu, Matrix.one_mulVec,
      Matrix.one_mulVec]
    exact hSD.1 x hx y hy
  obtain ⟨dd, hdd, hsemi⟩ :=
    adapted_semistable hB hN hA hE S m g h2m hfix hg0 haniso Lp hLp hsp hint
  obtain ⟨M, hM⟩ := exists_adapted_majorant S P m g dd hP h2m hJ hdd hg0
  have hHeq : M.H = fun σ : K →+* ℂ => (Q.map σ)ᴴ * diagMet (adMet r m g dd) σ * Q.map σ :=
    funext hM
  have hsemiL : ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L → ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg M.H B b ≤ 0 := by
    intro B hB k b hb
    rw [hHeq, latDeg_transport _ Q hQ B b]
    exact hsemi _ (Submodule.map_mono hB) k _ (kBasisIn_map Q hQ B b hb)
  refine ⟨M, ?_, hsemiL⟩
  intro k b hb
  obtain rfl : k = r := kBasis_card L hL b hb
  exact le_antisymm (hsemiL L le_rfl k b hb) (latDeg_L_nonneg hS S M L hL hSD hG b hb)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
end
